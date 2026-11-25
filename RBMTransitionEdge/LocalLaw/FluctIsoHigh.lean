module

public import RBMTransitionEdge.LocalLaw.FluctIsoDer
public import RBMTransitionEdge.LocalLaw.ExpansionHP

@[expose] public section

/-!
# The higher-order terms of the isotropic moment inequality

The order-`k` part, `k ≥ 2`, of the expansion of `E (H̲G)_{uv}^p conj((H̲G)_{uv})^p` for (2.30)
[eq:HGline] in the class, through Lemma 2.11 [lem:complex_cumu] with a high-probability
remainder and the derivative bounds on the good event.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

open scoped ContDiff

/-! ### Wirtinger calculus on smooth functions -/

/-- The operator `F ↦ (∂_x F + c ∂_y F)/2`; `c = -i` gives `∂_w` and `c = i` gives `∂_{w̄}`. -/
private def FIH_op (c : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun w => (fderiv ℝ F w 1 + c * fderiv ℝ F w Complex.I) / 2

private lemma FIH_dW_eq : dW = FIH_op (-Complex.I) := by
  funext F w
  simp only [dW, FIH_op]
  ring

private lemma FIH_dWbar_eq : dWbar = FIH_op Complex.I := by
  funext F w
  simp only [dWbar, FIH_op]

private lemma FIH_op_smooth (c : ℂ) {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (FIH_op c F) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  unfold FIH_op
  exact ((h1.clm_apply contDiff_const).add
    (contDiff_const.mul (h1.clm_apply contDiff_const))).div_const 2

private lemma FIH_iter_smooth (c : ℂ) (n : ℕ) {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ ((FIH_op c)^[n] F) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact FIH_op_smooth c ih

private lemma FIH_diff {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) (w : ℂ) : DifferentiableAt ℝ F w :=
  hF.differentiable (by simp) w

private lemma FIH_op_sum (c : ℂ) {ι : Type*} (s : Finset ι) (H : ι → ℂ → ℂ) (w : ℂ)
    (hH : ∀ i ∈ s, DifferentiableAt ℝ (H i) w) :
    FIH_op c (fun w => ∑ i ∈ s, H i w) w = ∑ i ∈ s, FIH_op c (H i) w := by
  simp only [FIH_op]
  rw [fderiv_fun_sum hH]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]

private lemma FIH_op_prod (c : ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℂ → ℂ)
    (w : ℂ) (hF : ∀ m, DifferentiableAt ℝ (F m) w) :
    FIH_op c (fun w => ∏ m, F m w) w =
      ∑ m₀, ∏ m, (if m = m₀ then FIH_op c (F m) w else F m w) := by
  simp only [FIH_op]
  rw [fderiv_finsetProd (fun m _ => hF m)]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  have e : ∀ m₀, ∏ m, (if m = m₀ then (fderiv ℝ (F m) w 1 + c * fderiv ℝ (F m) w Complex.I) / 2
      else F m w) = (fderiv ℝ (F m₀) w 1 + c * fderiv ℝ (F m₀) w Complex.I) / 2 *
        ∏ m ∈ Finset.univ.erase m₀, F m w := by
    intro m₀
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m₀), ite_eq_left rfl]
    congr 1
    refine Finset.prod_congr rfl fun m hm => ?_
    rw [ite_eq_right (Finset.ne_of_mem_erase hm)]
  simp only [e]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- The number of letters of a word `σ` equal to `m`. -/
private def FIH_cnt {ι : Type*} [DecidableEq ι] {n : ℕ} (σ : Fin n → ι) (m : ι) : ℕ :=
  ∑ l, if σ l = m then 1 else 0

private lemma FIH_cnt_cons {ι : Type*} [DecidableEq ι] {n : ℕ} (a : ι) (σ : Fin n → ι) (m : ι) :
    FIH_cnt (Fin.cons a σ : Fin (n + 1) → ι) m = (if a = m then 1 else 0) + FIH_cnt σ m := by
  simp only [FIH_cnt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- The Leibniz rule for an iterated Wirtinger operator on a finite product, as a sum over
words. -/
private lemma FIH_iter_prod (c : ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℂ → ℂ)
    (hF : ∀ m, ContDiff ℝ ∞ (F m)) (n : ℕ) :
    (FIH_op c)^[n] (fun w => ∏ m, F m w) =
      fun w => ∑ σ : Fin n → ι, ∏ m, (FIH_op c)^[FIH_cnt σ m] (F m) w := by
  induction n with
  | zero =>
    funext w
    simp [FIH_cnt]
  | succ n ih =>
    funext w
    rw [Function.iterate_succ_apply', ih]
    have hd : ∀ σ : Fin n → ι, DifferentiableAt ℝ
        (fun w => ∏ m, (FIH_op c)^[FIH_cnt σ m] (F m) w) w := fun σ =>
      (HasFDerivAt.finsetProd fun m _ =>
        (FIH_diff (FIH_iter_smooth c _ (hF m)) w).hasFDerivAt).differentiableAt
    rw [FIH_op_sum c _ _ w (fun σ _ => hd σ)]
    simp only [fun σ => FIH_op_prod c (fun m => (FIH_op c)^[FIH_cnt σ m] (F m)) w
      (fun m => FIH_diff (FIH_iter_smooth c _ (hF m)) w)]
    conv_rhs => rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun m₀ _ => ?_
    refine Finset.prod_congr rfl fun m _ => ?_
    simp only [Fin.consEquiv_apply, FIH_cnt_cons]
    by_cases h : m = m₀
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl, add_comm, Function.iterate_succ_apply']
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), zero_add]

private lemma FIH_iter_sum (c : ℂ) {ι : Type*} (s : Finset ι) (H : ι → ℂ → ℂ)
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (n : ℕ) :
    (FIH_op c)^[n] (fun w => ∑ i ∈ s, H i w) = fun w => ∑ i ∈ s, (FIH_op c)^[n] (H i) w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext w
    rw [Function.iterate_succ_apply', ih,
      FIH_op_sum c s _ w (fun i _ => FIH_diff (FIH_iter_smooth c n (hH i)) w)]
    simp only [Function.iterate_succ_apply']

/-- The Leibniz rule for `∂_w^a ∂_{w̄}^b` of a finite product of smooth functions, as a sum over
pairs of words. -/
private lemma FIH_wirt_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℂ → ℂ)
    (hF : ∀ m, ContDiff ℝ ∞ (F m)) (a b : ℕ) (w : ℂ) :
    wirt a b (fun w => ∏ m, F m w) w = ∑ σ : Fin b → ι, ∑ τ : Fin a → ι,
      ∏ m, wirt (FIH_cnt τ m) (FIH_cnt σ m) (F m) w := by
  simp only [wirt, FIH_dW_eq, FIH_dWbar_eq]
  rw [FIH_iter_prod Complex.I F hF b, FIH_iter_sum (-Complex.I) _ _
    (fun σ => contDiff_prod fun m _ => FIH_iter_smooth _ _ (hF m)) a]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [FIH_iter_prod (-Complex.I) _ (fun m => FIH_iter_smooth _ _ (hF m)) a]

private lemma FIH_fderiv_op (c : ℂ) {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) (w e : ℂ) :
    fderiv ℝ (FIH_op c F) w e =
      (fderiv ℝ (fderiv ℝ F) w e 1 + c * fderiv ℝ (fderiv ℝ F) w e Complex.I) / 2 := by
  have h2 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) w) w :=
    (h2.differentiable (by simp) w).hasFDerivAt
  have h1 := hd.clm_apply (hasFDerivAt_const (1 : ℂ) w)
  have hI := hd.clm_apply (hasFDerivAt_const Complex.I w)
  have hall := (h1.add (hI.const_mul c)).const_mul (2 : ℂ)⁻¹
  have he : FIH_op c F = fun x => (2 : ℂ)⁻¹ * (fderiv ℝ F x 1 + c * fderiv ℝ F x Complex.I) := by
    funext x
    simp only [FIH_op]
    ring
  have h3 : HasFDerivAt (fun x => (2 : ℂ)⁻¹ * (fderiv ℝ F x 1 + c * fderiv ℝ F x Complex.I)) _ w :=
    hall
  rw [he, h3.fderiv]
  simp
  ring

private lemma FIH_comm {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) : dW (dWbar F) = dWbar (dW F) := by
  funext w
  rw [FIH_dW_eq, FIH_dWbar_eq]
  have hsym := (hF.contDiffAt (x := w)).isSymmSndFDerivAt (by simp)
  have e := hsym 1 Complex.I
  simp only [FIH_op]
  rw [FIH_fderiv_op _ hF, FIH_fderiv_op _ hF, FIH_fderiv_op _ hF, FIH_fderiv_op _ hF]
  linear_combination (Complex.I / 2) * e + (0 : ℂ) * Complex.I_mul_I

private lemma FIH_dW_smooth {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (dW F) := by
  rw [FIH_dW_eq]
  exact FIH_op_smooth _ hF

private lemma FIH_dWbar_smooth {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (dWbar F) := by
  rw [FIH_dWbar_eq]
  exact FIH_op_smooth _ hF

private lemma FIH_dW_iter_smooth (n : ℕ) {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (dW^[n] F) := by
  rw [FIH_dW_eq]
  exact FIH_iter_smooth _ n hF

private lemma FIH_dWbar_iter_smooth (n : ℕ) {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (dWbar^[n] F) := by
  rw [FIH_dWbar_eq]
  exact FIH_iter_smooth _ n hF

private lemma FIH_comm1 (β : ℕ) : ∀ {G : ℂ → ℂ}, ContDiff ℝ ∞ G →
    dWbar (dW^[β] G) = dW^[β] (dWbar G) := by
  induction β with
  | zero => intro G _; rfl
  | succ β ih =>
    intro G hG
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (FIH_dW_smooth hG),
      FIH_comm hG]

/-- `∂_{w̄}^α ∂_w^β = ∂_w^β ∂_{w̄}^α` on smooth functions. -/
private lemma FIH_comm_iter (α : ℕ) : ∀ {F : ℂ → ℂ}, ContDiff ℝ ∞ F → ∀ β : ℕ,
    dWbar^[α] (dW^[β] F) = dW^[β] (dWbar^[α] F) := by
  induction α with
  | zero => intro F _ β; rfl
  | succ α ih =>
    intro F hF β
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, FIH_comm1 β hF,
      ih (FIH_dWbar_smooth hF)]

private lemma FIH_dWbar_conj (β : ℕ) : ∀ {F : ℂ → ℂ}, ContDiff ℝ ∞ F →
    dWbar^[β] (fun w => starRingEnd ℂ (F w)) = fun w => starRingEnd ℂ (dW^[β] F w) := by
  induction β with
  | zero => intro F _; rfl
  | succ β ih =>
    intro F hF
    rw [Function.iterate_succ_apply', ih hF, Function.iterate_succ_apply']
    funext w
    exact (dW_conj (FIH_diff (FIH_dW_iter_smooth β hF) w)).2

private lemma FIH_dW_conj (α : ℕ) : ∀ {F : ℂ → ℂ}, ContDiff ℝ ∞ F →
    dW^[α] (fun w => starRingEnd ℂ (F w)) = fun w => starRingEnd ℂ (dWbar^[α] F w) := by
  induction α with
  | zero => intro F _; rfl
  | succ α ih =>
    intro F hF
    rw [Function.iterate_succ_apply', ih hF, Function.iterate_succ_apply']
    funext w
    exact (dW_conj (FIH_diff (FIH_dWbar_iter_smooth α hF) w)).1

/-- The Wirtinger derivatives of a conjugate: `∂_w^α ∂_{w̄}^β F̄ = conj(∂_w^β ∂_{w̄}^α F)`. -/
private lemma FIH_wirt_conj (α β : ℕ) {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) :
    wirt α β (fun w => starRingEnd ℂ (F w)) = fun w => starRingEnd ℂ (wirt β α F w) := by
  simp only [wirt]
  rw [FIH_dWbar_conj β hF, FIH_dW_conj α (FIH_dW_iter_smooth β hF), FIH_comm_iter α hF β]

/-! ### One-entry slices of Hermitian arrays -/

private lemma FIH_setEntry_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  have e : setEntry h i j w = symArr (setEntry h i j w) := by
    rw [symArr_setEntry, symArr_of_isHermitian h hh]
  rw [e]
  exact symArr_isHermitian _

private lemma FIH_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) : setEntry h i j (h i j) = h := by
  funext k l
  have h1 : ∀ k l, starRingEnd ℂ (h l k) = h k l := fun k l => by
    simpa [Complex.star_def] using hh.apply k l
  by_cases hd : i = j
  · subst hd
    by_cases hkl : k = i ∧ l = i
    · obtain ⟨hk, hl⟩ := hkl
      rw [hk, hl]
      have hre : (((h i i).re : ℝ) : ℂ) = h i i := Complex.conj_eq_iff_re.mp (h1 i i)
      simp [setEntry, hre]
    · simp [setEntry, hkl]
  · by_cases h1' : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1'
      simp [setEntry, hd]
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp [setEntry, hd, Ne.symm hd, h1 k l]
      · simp [setEntry, hd, h1', h2]

private lemma FIH_slice_smooth {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) :
    ContDiff ℝ ∞ (fun w : ℂ => setEntry h i j w) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  by_cases hd : i = j
  · by_cases hk : k = i ∧ l = i
    · have e : (fun w : ℂ => setEntry h i j w k l) = fun w => ((w.re : ℝ) : ℂ) := by
        funext w
        simp [setEntry, hd, hk.1, hk.2]
      rw [e]
      exact Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff
    · have e : (fun w : ℂ => setEntry h i j w k l) = fun _ => h k l := by
        funext w
        subst hd
        simp [setEntry, hk]
      rw [e]
      exact contDiff_const
  · by_cases h1 : k = i ∧ l = j
    · have e : (fun w : ℂ => setEntry h i j w k l) = fun w => w := by
        funext w
        simp [setEntry, hd, h1.1, h1.2]
      rw [e]
      exact contDiff_id
    · by_cases h2 : k = j ∧ l = i
      · have e : (fun w : ℂ => setEntry h i j w k l) = fun w => starRingEnd ℂ w := by
          funext w
          simp [setEntry, hd, h2.1, h2.2, Ne.symm hd]
        rw [e]
        exact Complex.conjCLE.contDiff
      · have e : (fun w : ℂ => setEntry h i j w k l) = fun _ => h k l := by
          funext w
          simp [setEntry, hd, h1, h2]
        rw [e]
        exact contDiff_const

/-- A resolvent polynomial along a one-entry slice of a Hermitian array is smooth. -/
private lemma FIH_rp_smooth {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) :
    ContDiff ℝ ∞ (fun w => resPolyEval P (setEntry h i j w)) := by
  have e : (fun w => resPolyEval P (setEntry h i j w)) =
      (fun h' => resPolyEval P (symArr h')) ∘ (fun w => setEntry h i j w) := by
    funext w
    simp only [Function.comp, symArr_setEntry, symArr_of_isHermitian h hh]
  rw [e, contDiff_infty]
  intro n
  exact (contDiff_resPoly_symArr P hP n).comp
    ((FIH_slice_smooth h i j).of_le (by exact_mod_cast le_top))

private lemma FIH_dot_single {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℂ) (k : ι) :
    star (Pi.single k (1 : ℂ)) ⬝ᵥ x = x k := by
  have : star (Pi.single k (1 : ℂ) : ι → ℂ) = Pi.single k 1 := by
    funext r
    by_cases h : r = k <;> simp [h]
  rw [this, single_one_dotProduct]

/-- The first Wirtinger derivatives of a resolvent form along a one-entry slice:
`∂_w (x^* G y) = -c (x^* G e_s)(e_t^* G y)` and `∂_{w̄} (x^* G y) = -c (x^* G e_t)(e_s^* G y)`. -/
private lemma FIH_form_d {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : z.im ≠ 0)
    (s t : Idx D N) (x y : Idx D N → ℂ) :
    dW (fun w => star x ⬝ᵥ (res (Matrix.of (setEntry h s t w) + Λ) z *ᵥ y)) =
        (fun w => -(if s = t then 1 / 2 else 1) *
          ((star x ⬝ᵥ (res (Matrix.of (setEntry h s t w) + Λ) z *ᵥ Pi.single s 1)) *
            (star (Pi.single t 1) ⬝ᵥ (res (Matrix.of (setEntry h s t w) + Λ) z *ᵥ y)))) ∧
      dWbar (fun w => star x ⬝ᵥ (res (Matrix.of (setEntry h s t w) + Λ) z *ᵥ y)) =
        (fun w => -(if s = t then 1 / 2 else 1) *
          ((star x ⬝ᵥ (res (Matrix.of (setEntry h s t w) + Λ) z *ᵥ Pi.single t 1)) *
            (star (Pi.single s 1) ⬝ᵥ (res (Matrix.of (setEntry h s t w) + Λ) z *ᵥ y)))) := by
  have e : (fun w => star x ⬝ᵥ (res (Matrix.of (setEntry h s t w) + Λ) z *ᵥ y)) =
      fun w => resPolyEval [((1 : ℂ), [(x, y, Λ, z)])] (setEntry h s t w) := by
    funext w
    simp [resPolyEval, resMonoEval, resFactorEval]
  have hP : ∀ t' ∈ [((1 : ℂ), [(x, y, Λ, z)])], ∀ f ∈ t'.2,
      f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
    intro t' ht' f hf
    simp only [List.mem_singleton] at ht'
    subst ht'
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨hΛ, hz⟩
  obtain ⟨h1, h2⟩ := resPoly_dW h hh s t _ hP
  rw [e, h1, h2]
  constructor <;> funext w <;>
    simp [resPolyD, resMonoD, resPolyEval, resMonoEval, resFactorEval]

/-! ### Derivatives of a resolvent form with a fixed right vector -/

/-- The sum of the moduli of the coefficients of a resolvent polynomial. -/
private def FIH_wt {D N : ℕ} (P : ResPoly D N) : ℝ := (P.map fun t => ‖t.1‖).sum

private lemma FIH_wt_nonneg {D N : ℕ} (P : ResPoly D N) : 0 ≤ FIH_wt P :=
  List.sum_nonneg fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _

private lemma FIH_wt_cons {D N : ℕ} (t : ℂ × ResMono D N) (P : ResPoly D N) :
    FIH_wt (t :: P) = ‖t.1‖ + FIH_wt P := by
  simp [FIH_wt]

private lemma FIH_wt_append {D N : ℕ} (P Q : ResPoly D N) :
    FIH_wt (P ++ Q) = FIH_wt P + FIH_wt Q := by
  simp [FIH_wt, List.map_append, List.sum_append]

private lemma FIH_wt_resMonoD {D N : ℕ} (a b : Idx D N) (c : ℂ) (m : ResMono D N) :
    FIH_wt (resMonoD a b c m) = m.length * ‖c‖ := by
  induction m with
  | nil => simp [resMonoD, FIH_wt]
  | cons f m ih =>
    have e : FIH_wt ((resMonoD a b c m).map fun t => (t.1, f :: t.2)) =
        FIH_wt (resMonoD a b c m) := by
      simp [FIH_wt, Function.comp_def]
    simp only [resMonoD]
    rw [FIH_wt_cons, e, ih]
    simp only [norm_neg, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

private lemma FIH_wt_map_mul {D N : ℕ} (c₀ : ℂ) (Q : ResPoly D N) :
    FIH_wt (Q.map fun s => (c₀ * s.1, s.2)) = ‖c₀‖ * FIH_wt Q := by
  induction Q with
  | nil => simp [FIH_wt]
  | cons t Q ih =>
    rw [List.map_cons, FIH_wt_cons, ih, FIH_wt_cons]
    simp only [norm_mul]
    ring

private lemma FIH_wt_resPolyD_le {D N : ℕ} (a b : Idx D N) (c : ℂ) (hc : ‖c‖ ≤ 1) (m : ℕ)
    (P : ResPoly D N) (hP : ∀ t ∈ P, t.2.length ≤ m) :
    FIH_wt (resPolyD a b c P) ≤ m * FIH_wt P := by
  induction P with
  | nil => simp [resPolyD, FIH_wt]
  | cons t P ih =>
    have ih' := ih fun u hu => hP u (List.mem_cons_of_mem _ hu)
    have e : resPolyD a b c (t :: P) =
        ((resMonoD a b c t.2).map fun s => (t.1 * s.1, s.2)) ++ resPolyD a b c P := by
      simp [resPolyD]
    have h2 : (t.2.length : ℝ) ≤ m := by exact_mod_cast hP t List.mem_cons_self
    rw [e, FIH_wt_append, FIH_wt_map_mul, FIH_wt_resMonoD, FIH_wt_cons]
    have h3 := norm_nonneg t.1
    have h4 : ‖t.1‖ * (t.2.length * ‖c‖) ≤ m * ‖t.1‖ := by
      calc ‖t.1‖ * (t.2.length * ‖c‖) ≤ ‖t.1‖ * (m * 1) := by gcongr
        _ = m * ‖t.1‖ := by ring
    nlinarith

/-- The terms of `resMonoD a b c m`: one more factor; each factor is a factor of `m` or one of
the two that replace it; every right vector of `m` survives. -/
private lemma FIH_resMonoD_mem {D N : ℕ} (a b : Idx D N) (c : ℂ) (m : ResMono D N) :
    ∀ s ∈ resMonoD a b c m, s.2.length = m.length + 1 ∧ (∀ g ∈ s.2, ∃ f ∈ m,
      g = f ∨ g = (f.1, Pi.single a 1, f.2.2.1, f.2.2.2) ∨
        g = (Pi.single b 1, f.2.1, f.2.2.1, f.2.2.2)) ∧ ∀ f ∈ m, ∃ g ∈ s.2, g.2.1 = f.2.1 := by
  induction m with
  | nil => intro s hs; simp [resMonoD] at hs
  | cons f m ih =>
    intro s hs
    simp only [resMonoD, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | ⟨t, ht, rfl⟩
    · refine ⟨by simp, fun g hg => ?_, fun f' hf' => ?_⟩
      · simp only [List.mem_cons] at hg
        rcases hg with rfl | rfl | hg
        · exact ⟨f, List.mem_cons_self, Or.inr (Or.inl rfl)⟩
        · exact ⟨f, List.mem_cons_self, Or.inr (Or.inr rfl)⟩
        · exact ⟨g, List.mem_cons_of_mem _ hg, Or.inl rfl⟩
      · simp only [List.mem_cons] at hf'
        rcases hf' with rfl | hf'
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
        · exact ⟨f', List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf'), rfl⟩
    · obtain ⟨h1, h3, h4⟩ := ih t ht
      refine ⟨by simp [h1], fun g hg => ?_, fun f' hf' => ?_⟩
      · simp only [List.mem_cons] at hg
        rcases hg with hg | hg
        · exact ⟨f, List.mem_cons_self, Or.inl hg⟩
        · obtain ⟨f'', hf'', hg'⟩ := h3 g hg
          exact ⟨f'', List.mem_cons_of_mem _ hf'', hg'⟩
      · simp only [List.mem_cons] at hf'
        rcases hf' with rfl | hf'
        · exact ⟨f', List.mem_cons_self, rfl⟩
        · obtain ⟨g, hg, hg'⟩ := h4 f' hf'
          exact ⟨g, List.mem_cons_of_mem _ hg, hg'⟩

/-- Every term: at most `m` factors, left vectors in `E`, right vectors in `E` or `y`, the pair
`pr`, and at least one factor with right vector `y`. -/
private def FIH_inv {D N : ℕ} (E : Set (Idx D N → ℂ)) (y : Idx D N → ℂ)
    (pr : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (m : ℕ) (P : ResPoly D N) : Prop :=
  ∀ t ∈ P, t.2.length ≤ m ∧ (∀ f ∈ t.2, f.1 ∈ E ∧ (f.2.1 ∈ E ∨ f.2.1 = y) ∧ f.2.2 = pr) ∧
    ∃ f ∈ t.2, f.2.1 = y

private lemma FIH_inv_resPolyD {D N : ℕ} (E : Set (Idx D N → ℂ)) (y : Idx D N → ℂ)
    (pr : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (a b : Idx D N) (c : ℂ)
    (ha : Pi.single a 1 ∈ E) (hb : Pi.single b 1 ∈ E) (m : ℕ) (P : ResPoly D N)
    (hP : FIH_inv E y pr m P) : FIH_inv E y pr (m + 1) (resPolyD a b c P) := by
  intro u hu
  unfold resPolyD at hu
  rw [List.mem_flatMap] at hu
  obtain ⟨t, ht, hu⟩ := hu
  rw [List.mem_map] at hu
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨hlen, hall, f₀, hf₀, hy⟩ := hP t ht
  obtain ⟨h1, h2, h3⟩ := FIH_resMonoD_mem a b c t.2 s hs
  refine ⟨by simp only; omega, fun g hg => ?_, ?_⟩
  · obtain ⟨f, hf, hgf⟩ := h2 g hg
    obtain ⟨e1, e2, e3⟩ := hall f hf
    rcases hgf with rfl | rfl | rfl
    · exact ⟨e1, e2, e3⟩
    · exact ⟨e1, Or.inl ha, e3⟩
    · exact ⟨hb, e2, e3⟩
  · obtain ⟨g, hg, hgy⟩ := h3 f₀ hf₀
    exact ⟨g, hg, hgy.trans hy⟩

private lemma FIH_inv_iter {D N : ℕ} (E : Set (Idx D N → ℂ)) (y : Idx D N → ℂ)
    (pr : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (a b : Idx D N) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (ha : Pi.single a 1 ∈ E) (hb : Pi.single b 1 ∈ E) (n m : ℕ) (P : ResPoly D N)
    (hP : FIH_inv E y pr m P) :
    FIH_inv E y pr (m + n) ((resPolyD a b c)^[n] P) ∧
      FIH_wt ((resPolyD a b c)^[n] P) ≤ ((m + n : ℕ) : ℝ) ^ n * FIH_wt P := by
  induction n with
  | zero => exact ⟨hP, by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Function.iterate_succ_apply']
    have h3 := FIH_inv_resPolyD E y pr a b c ha hb (m + n) _ h1
    have h4 := FIH_wt_resPolyD_le a b c hc (m + n) _ fun t ht => (h1 t ht).1
    refine ⟨h3, ?_⟩
    have h5 : ((m + n : ℕ) : ℝ) * FIH_wt ((resPolyD a b c)^[n] P) ≤
        ((m + n : ℕ) : ℝ) * (((m + n : ℕ) : ℝ) ^ n * FIH_wt P) :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    have h6 : ((m + n : ℕ) : ℝ) ^ (n + 1) ≤ ((m + (n + 1) : ℕ) : ℝ) ^ (n + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ_of_le le_rfl) _
    calc FIH_wt (resPolyD a b c ((resPolyD a b c)^[n] P))
        ≤ ((m + n : ℕ) : ℝ) * FIH_wt ((resPolyD a b c)^[n] P) := by exact_mod_cast h4
      _ ≤ ((m + n : ℕ) : ℝ) * (((m + n : ℕ) : ℝ) ^ n * FIH_wt P) := h5
      _ = ((m + n : ℕ) : ℝ) ^ (n + 1) * FIH_wt P := by ring
      _ ≤ ((m + (n + 1) : ℕ) : ℝ) ^ (n + 1) * FIH_wt P :=
        mul_le_mul_of_nonneg_right h6 (FIH_wt_nonneg P)

private lemma FIH_factor_eq {D N : ℕ} (f : ResFactor D N)
    (p : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (hp : f.2.2 = p) (h' : Idx D N → Idx D N → ℂ) :
    resFactorEval f h' = resFactorEval (f.1, f.2.1, p.1, p.2) h' := by
  subst hp
  rfl

private lemma FIH_mono_le {D N : ℕ} (m : ResMono D N) (h' : Idx D N → Idx D N → ℂ) (Γ : ℝ)
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

private lemma FIH_inv_mono_le {D N : ℕ} (E : Set (Idx D N → ℂ)) (y : Idx D N → ℂ)
    (pr : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (h' : Idx D N → Idx D N → ℂ) (Γ om : ℝ)
    (hω0 : 0 ≤ om) (hωΓ : om ≤ Γ)
    (hE : ∀ x ∈ E, ∀ x' ∈ E, ‖resFactorEval (x, x', pr.1, pr.2) h'‖ ≤ Γ)
    (hy : ∀ x ∈ E, ‖resFactorEval (x, y, pr.1, pr.2) h'‖ ≤ om) (l : ResMono D N)
    (hl : ∀ f ∈ l, f.1 ∈ E ∧ (f.2.1 ∈ E ∨ f.2.1 = y) ∧ f.2.2 = pr) (hex : ∃ f ∈ l, f.2.1 = y) :
    ‖resMonoEval l h'‖ ≤ om * Γ ^ (l.length - 1) := by
  have hΓ0 : 0 ≤ Γ := hω0.trans hωΓ
  have hfac : ∀ f ∈ l, ‖resFactorEval f h'‖ ≤ Γ := by
    intro f hf
    obtain ⟨e1, e2, e3⟩ := hl f hf
    rw [FIH_factor_eq f pr e3]
    rcases e2 with e2 | e2
    · exact hE _ e1 _ e2
    · rw [e2]
      exact (hy _ e1).trans hωΓ
  induction l with
  | nil => obtain ⟨f, hf, -⟩ := hex; simp at hf
  | cons f l ih =>
    simp only [resMonoEval, List.map_cons, List.prod_cons, norm_mul, List.length_cons,
      Nat.add_sub_cancel]
    have hl' : ∀ g ∈ l, g.1 ∈ E ∧ (g.2.1 ∈ E ∨ g.2.1 = y) ∧ g.2.2 = pr :=
      fun g hg => hl g (List.mem_cons_of_mem _ hg)
    have hfac' : ∀ g ∈ l, ‖resFactorEval g h'‖ ≤ Γ :=
      fun g hg => hfac g (List.mem_cons_of_mem _ hg)
    by_cases hf : f.2.1 = y
    · have e1 : ‖resFactorEval f h'‖ ≤ om := by
        rw [FIH_factor_eq f pr (hl f List.mem_cons_self).2.2, hf]
        exact hy _ (hl f List.mem_cons_self).1
      have e2 := FIH_mono_le l h' Γ hΓ0 hfac'
      exact mul_le_mul e1 e2 (norm_nonneg _) hω0
    · have hex' : ∃ g ∈ l, g.2.1 = y := by
        obtain ⟨g, hg, hgy⟩ := hex
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact absurd hgy hf
        · exact ⟨g, hg, hgy⟩
      have e2 := ih hl' hex' hfac'
      have hlen : 1 ≤ l.length := by
        obtain ⟨g, hg, -⟩ := hex'
        exact List.length_pos_of_mem hg
      have e1 := hfac f List.mem_cons_self
      have e2' : ‖(l.map fun f => resFactorEval f h').prod‖ ≤ om * Γ ^ (l.length - 1) := e2
      calc ‖resFactorEval f h'‖ * ‖(l.map fun f => resFactorEval f h').prod‖
          ≤ Γ * (om * Γ ^ (l.length - 1)) := mul_le_mul e1 e2' (norm_nonneg _) hΓ0
        _ = om * Γ ^ l.length := by
          obtain ⟨n, hn⟩ : ∃ n, l.length = n + 1 := ⟨l.length - 1, by omega⟩
          rw [hn, Nat.add_sub_cancel, pow_succ]
          ring

private lemma FIH_inv_eval_le {D N : ℕ} (E : Set (Idx D N → ℂ)) (y : Idx D N → ℂ)
    (pr : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (h' : Idx D N → Idx D N → ℂ) (Γ om : ℝ)
    (hΓ : 1 ≤ Γ) (hω0 : 0 ≤ om) (hωΓ : om ≤ Γ)
    (hE : ∀ x ∈ E, ∀ x' ∈ E, ‖resFactorEval (x, x', pr.1, pr.2) h'‖ ≤ Γ)
    (hy : ∀ x ∈ E, ‖resFactorEval (x, y, pr.1, pr.2) h'‖ ≤ om) (m : ℕ) (P : ResPoly D N)
    (hP : FIH_inv E y pr m P) :
    ‖resPolyEval P h'‖ ≤ FIH_wt P * (om * Γ ^ (m - 1)) := by
  induction P with
  | nil => simp [resPolyEval, FIH_wt]
  | cons t P ih =>
    have ih' := ih fun u hu => hP u (List.mem_cons_of_mem _ hu)
    obtain ⟨hlen, hall, hex⟩ := hP t List.mem_cons_self
    have hmono : ‖resMonoEval t.2 h'‖ ≤ om * Γ ^ (m - 1) :=
      (FIH_inv_mono_le E y pr h' Γ om hω0 hωΓ hE hy t.2 hall hex).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΓ (by omega)) hω0)
    have e : resPolyEval (t :: P) h' = t.1 * resMonoEval t.2 h' + resPolyEval P h' := by
      simp [resPolyEval]
    rw [e, FIH_wt_cons]
    calc ‖t.1 * resMonoEval t.2 h' + resPolyEval P h'‖
        ≤ ‖t.1 * resMonoEval t.2 h'‖ + ‖resPolyEval P h'‖ := norm_add_le _ _
      _ ≤ ‖t.1‖ * (om * Γ ^ (m - 1)) + FIH_wt P * (om * Γ ^ (m - 1)) := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hmono (norm_nonneg _)) ih'
      _ = (‖t.1‖ + FIH_wt P) * (om * Γ ^ (m - 1)) := by ring

private lemma FIH_mulVec_single {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ)
    (a r : ι) : (G *ᵥ Pi.single a 1) r = G r a := by
  rw [Matrix.mulVec_single_one]
  rfl

private lemma FIH_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (a b : ι) :
    star (Pi.single a (1 : ℂ)) ⬝ᵥ (G *ᵥ Pi.single b 1) = G a b := by
  rw [FIH_dot_single, Matrix.mulVec_single_one]
  rfl

/-- The derivatives of `(G y)_s` along the slice `(s, t)`:
`|∂_w^α ∂_{w̄}^β (G y)_s| ≤ (1 + r)^r om Γ^r`, `r = α + β`, if the entries of `G` on `{s, t}` are
`≤ Γ` and `|(G y)_s|, |(G y)_t| ≤ om ≤ Γ`. -/
private lemma FIH_B0 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : z.im ≠ 0)
    (s t : Idx D N) (y : Idx D N → ℂ) (Γ om : ℝ) (hΓ : 1 ≤ Γ) (hω0 : 0 ≤ om) (hωΓ : om ≤ Γ)
    (w : ℂ)
    (hE : ∀ a ∈ ({s, t} : Set (Idx D N)), ∀ b ∈ ({s, t} : Set (Idx D N)),
      ‖res (Matrix.of (setEntry h s t w) + Λ) z a b‖ ≤ Γ)
    (hy : ∀ a ∈ ({s, t} : Set (Idx D N)),
      ‖(res (Matrix.of (setEntry h s t w) + Λ) z *ᵥ y) a‖ ≤ om) (α β : ℕ) :
    ‖wirt α β (fun w' => (res (Matrix.of (setEntry h s t w') + Λ) z *ᵥ y) s) w‖ ≤
      ((1 + α + β : ℕ) : ℝ) ^ (α + β) * (om * Γ ^ (α + β)) := by
  set E : Set (Idx D N → ℂ) := {Pi.single s 1, Pi.single t 1} with hEdef
  set P0 : ResPoly D N := [((1 : ℂ), [(Pi.single s 1, y, Λ, z)])] with hP0
  have hc : ‖(if s = t then (1 / 2 : ℂ) else 1)‖ ≤ 1 := by
    split_ifs
    · norm_num
    · simp
  have hP0' : ∀ t' ∈ P0, ∀ f ∈ t'.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
    intro t' ht' f hf
    simp only [hP0, List.mem_singleton] at ht'
    subst ht'
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨hΛ, hz⟩
  have e : (fun w' => (res (Matrix.of (setEntry h s t w') + Λ) z *ᵥ y) s) =
      fun w' => resPolyEval P0 (setEntry h s t w') := by
    funext w'
    simp [hP0, resPolyEval, resMonoEval, resFactorEval]
  rw [e, resPoly_wirt h hh s t P0 hP0' α β]
  have hsE : Pi.single s 1 ∈ E := by simp [hEdef]
  have htE : Pi.single t 1 ∈ E := by simp [hEdef]
  have hinv0 : FIH_inv E y (Λ, z) 1 P0 := by
    intro t' ht'
    simp only [hP0, List.mem_singleton] at ht'
    subst ht'
    refine ⟨by simp, fun f hf => ?_, ⟨_, List.mem_singleton_self _, rfl⟩⟩
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨hsE, Or.inr rfl, rfl⟩
  obtain ⟨g1, w1⟩ := FIH_inv_iter E y (Λ, z) t s _ hc htE hsE β 1 P0 hinv0
  obtain ⟨g2, w2⟩ := FIH_inv_iter E y (Λ, z) s t _ hc hsE htE α (1 + β) _ g1
  have hE' : ∀ x ∈ E, ∀ x' ∈ E,
      ‖resFactorEval (x, x', (Λ, z).1, (Λ, z).2) (setEntry h s t w)‖ ≤ Γ := by
    intro x hx x' hx'
    simp only [hEdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
    simp only [resFactorEval]
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl <;> rw [FIH_entry] <;>
      exact hE _ (by simp) _ (by simp)
  have hy' : ∀ x ∈ E, ‖resFactorEval (x, y, (Λ, z).1, (Λ, z).2) (setEntry h s t w)‖ ≤ om := by
    intro x hx
    simp only [hEdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [resFactorEval]
    rcases hx with rfl | rfl <;> rw [FIH_dot_single] <;> exact hy _ (by simp)
  have hev := FIH_inv_eval_le E y (Λ, z) (setEntry h s t w) Γ om hΓ hω0 hωΓ hE' hy'
    (1 + β + α) _ g2
  have hwt0 : FIH_wt P0 = 1 := by simp [hP0, FIH_wt]
  rw [hwt0, mul_one] at w1
  have hn1 : ((1 + β : ℕ) : ℝ) ≤ ((1 + α + β : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hn2 : ((1 + β + α : ℕ) : ℝ) = ((1 + α + β : ℕ) : ℝ) := by congr 1; omega
  rw [hn2] at w2
  have hwt : FIH_wt ((resPolyD s t (if s = t then 1 / 2 else 1))^[α]
      ((resPolyD t s (if s = t then 1 / 2 else 1))^[β] P0)) ≤
      ((1 + α + β : ℕ) : ℝ) ^ (α + β) := by
    calc _ ≤ _ := w2
      _ ≤ ((1 + α + β : ℕ) : ℝ) ^ α * ((1 + α + β : ℕ) : ℝ) ^ β := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact w1.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hn1 β)
      _ = _ := by rw [pow_add]
  have e1 : 1 + β + α - 1 = α + β := by omega
  rw [e1] at hev
  exact hev.trans (mul_le_mul_of_nonneg_right hwt (by positivity))

/-! ### The operator `(∂_x + c ∂_y)/2` on products and sums -/

private lemma FIH_op_sub (c : ℂ) {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w)
    (hg : DifferentiableAt ℝ g w) :
    FIH_op c (fun x => f x - g x) w = FIH_op c f w - FIH_op c g w := by
  simp only [FIH_op]
  rw [(hf.hasFDerivAt.fun_sub hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.sub_apply]
  ring

private lemma FIH_op_mul (c : ℂ) {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w)
    (hg : DifferentiableAt ℝ g w) :
    FIH_op c (fun x => f x * g x) w = FIH_op c f w * g w + f w * FIH_op c g w := by
  simp only [FIH_op]
  rw [(hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private lemma FIH_op_const_mul (c k : ℂ) {f : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w) :
    FIH_op c (fun x => k * f x) w = k * FIH_op c f w := by
  simp only [FIH_op]
  rw [(hf.hasFDerivAt.const_mul k).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-! ### Ward bounds -/

/-- `N⁻¹ Σ_r |G_{ra}| |G_{br}| ≤ Υ/(Nη)` if `Im G_{aa}, Im G_{bb} ≤ Υ`, from (2.32) [eq_Ward]. -/
private lemma FIH_W2 {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (a b : ι) (N Υ : ℝ) (hN : 0 ≤ N)
    (ha : (res X z a a).im ≤ Υ) (hb : (res X z b b).im ≤ Υ) :
    N⁻¹ * ∑ r, ‖res X z r a‖ * ‖res X z b r‖ ≤ Υ / (N * z.im) := by
  obtain ⟨wa, -⟩ := ward_diag X hX z hz a
  obtain ⟨-, wb⟩ := ward_diag X hX z hz b
  have hΥ : 0 ≤ Υ / z.im := by
    have : 0 ≤ (res X z a a).im / z.im := by rw [← wa]; positivity
    exact this.trans (div_le_div_of_nonneg_right ha hz.le)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun r => ‖res X z r a‖)
    (fun r => ‖res X z b r‖)
  have h1 : ∑ r, ‖res X z r a‖ ^ 2 ≤ Υ / z.im := by
    rw [wa]; exact div_le_div_of_nonneg_right ha hz.le
  have h2 : ∑ r, ‖res X z b r‖ ^ 2 ≤ Υ / z.im := by
    rw [wb]; exact div_le_div_of_nonneg_right hb hz.le
  have h3 : ∑ r, ‖res X z r a‖ * ‖res X z b r‖ ≤ Υ / z.im := by
    refine hcs.trans ?_
    calc Real.sqrt (∑ r, ‖res X z r a‖ ^ 2) * Real.sqrt (∑ r, ‖res X z b r‖ ^ 2)
        ≤ Real.sqrt (Υ / z.im) * Real.sqrt (Υ / z.im) :=
          mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = Υ / z.im := Real.mul_self_sqrt hΥ
  rw [div_mul_eq_div_div_swap, div_eq_inv_mul (Υ / z.im)]
  exact mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hN)

/-- The first derivative of `(H̲G)_{uy}`: `|hgDer(a, b)| ≤ |u_a| |(G y)_b| + λ |(G y)_b| + Γ Z` if
`|(H̲G)_{u e_a}| ≤ λ`, `|t^r(u)^* G y| ≤ Γ` and `N⁻¹ Σ_r |G_{ra}| |G_{br}| ≤ Z`. -/
private lemma FIH_R1 {D N : ℕ} (θ : ℝ) (H Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u y : Idx D N → ℂ) (a b : Idx D N) (Γ lb Z : ℝ) (hΓ : 0 ≤ Γ)
    (hD : ‖star u ⬝ᵥ (hgUnder D N θ H Λ z *ᵥ Pi.single a 1)‖ ≤ lb)
    (ht : ∀ r, ‖star (tiltV D N θ u r) ⬝ᵥ (res (H + Λ) z *ᵥ y)‖ ≤ Γ)
    (hW : (N : ℝ)⁻¹ * ∑ r, ‖res (H + Λ) z r a‖ * ‖res (H + Λ) z b r‖ ≤ Z) :
    ‖hgDer D N θ H Λ z u y a b‖ ≤
      ‖u a‖ * ‖(res (H + Λ) z *ᵥ y) b‖ + lb * ‖(res (H + Λ) z *ᵥ y) b‖ + Γ * Z := by
  set G := res (H + Λ) z
  have h3 : ‖(N : ℂ)⁻¹ * ∑ r, G r a * G b r * (star (tiltV D N θ u r) ⬝ᵥ (G *ᵥ y))‖ ≤
      Γ * Z := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ r, G r a * G b r * (star (tiltV D N θ u r) ⬝ᵥ (G *ᵥ y))‖
        ≤ (N : ℝ)⁻¹ * ∑ r, ‖G r a‖ * ‖G b r‖ * Γ := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun r _ => ?_)) (by positivity)
          rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_left (ht r) (by positivity)
      _ = Γ * ((N : ℝ)⁻¹ * ∑ r, ‖G r a‖ * ‖G b r‖) := by
          rw [← Finset.sum_mul]; ring
      _ ≤ Γ * Z := mul_le_mul_of_nonneg_left hW hΓ
  unfold hgDer
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) h3)
  · rw [norm_mul, Complex.norm_conj]
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hD (norm_nonneg _)

/-- A resolvent form along a one-entry slice. -/
private def FIH_fF {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (s t : Idx D N) (x y : Idx D N → ℂ) (w : ℂ) : ℂ :=
  star x ⬝ᵥ (res (Matrix.of (setEntry h s t w) + Λ) z *ᵥ y)

private lemma FIH_fF_smooth {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (s t : Idx D N) (x y : Idx D N → ℂ) :
    ContDiff ℝ ∞ (FIH_fF h Λ z s t x y) := by
  have e : FIH_fF h Λ z s t x y =
      fun w => resPolyEval [((1 : ℂ), [(x, y, Λ, z)])] (setEntry h s t w) := by
    funext w
    simp [FIH_fF, resPolyEval, resMonoEval, resFactorEval]
  rw [e]
  refine FIH_rp_smooth h hh s t _ ?_
  intro t' ht' f hf
  simp only [List.mem_singleton] at ht'
  subst ht'
  simp only [List.mem_singleton] at hf
  subst hf
  exact ⟨hΛ, hz⟩

/-- `(H̲G)_{xy}` along a one-entry slice of a Hermitian array is smooth. -/
private lemma FIH_hg_smooth {D N : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (s t : Idx D N) (x y : Idx D N → ℂ) (hx : ∑ k, ‖x k‖ ^ 2 ≤ 1) (hy : ∑ k, ‖y k‖ ^ 2 ≤ 1) :
    ContDiff ℝ ∞
      (fun w => star x ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h s t w)) Λ z *ᵥ y)) := by
  obtain ⟨P, hP1, -, hP3⟩ := hgUnder_resPoly D N θ hθ0 hθ1 Λ hΛ z hz x y hx hy
  have e : (fun w => star x ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h s t w)) Λ z *ᵥ y)) =
      fun w => resPolyEval P (setEntry h s t w) := by
    funext w
    exact (hP3 _ (FIH_setEntry_herm h hh s t w)).symm
  rw [e]
  refine FIH_rp_smooth h hh s t P fun t' ht' f hf => ?_
  rw [((hP1 t' ht').2 f hf).2.2]
  exact ⟨hΛ, hz.ne'⟩

private lemma FIH_single_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (k₀ : ι) :
    ∑ k, ‖(Pi.single k₀ (1 : ℂ) : ι → ℂ) k‖ ^ 2 ≤ 1 := by
  have : ∀ k, ‖(Pi.single k₀ (1 : ℂ) : ι → ℂ) k‖ ^ 2 = if k = k₀ then 1 else 0 := by
    intro k
    by_cases h : k = k₀ <;> simp [h]
  simp [this]

/-- The part `N⁻¹ Σ_r G_{ra} G_{br} t^r(u)^* G y` of `hgDer`, differentiated once. -/
private lemma FIH_R2_sum {ι : Type*} [Fintype ι] (N : ℕ) (cc : ℂ) (hcc : ‖cc‖ ≤ 1)
    (G : ι → ι → ℂ) (Ty : ι → ℂ) (Tσ : ι → ℂ) (Gy : ι → ℂ) (a b σ τ : ι) (Γ Z : ℝ)
    (hΓ : 0 ≤ Γ) (hG : ∀ k l, ‖G k l‖ ≤ Γ) (hTy : ∀ r, ‖Ty r‖ ≤ Γ) (hTσ : ∀ r, ‖Tσ r‖ ≤ Γ)
    (hW : ∀ k l, (N : ℝ)⁻¹ * ∑ r, ‖G r k‖ * ‖G l r‖ ≤ Z) :
    ‖(N : ℂ)⁻¹ * ∑ r, (((-cc * (G r σ * G τ a)) * G b r + G r a * (-cc * (G b σ * G τ r))) * Ty r +
      G r a * G b r * (-cc * (Tσ r * Gy τ)))‖ ≤ 2 * Γ ^ 2 * Z + Γ * Z * ‖Gy τ‖ := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have key : ∀ r, ‖((-cc * (G r σ * G τ a)) * G b r + G r a * (-cc * (G b σ * G τ r))) * Ty r +
      G r a * G b r * (-cc * (Tσ r * Gy τ))‖ ≤
      Γ ^ 2 * (‖G r σ‖ * ‖G b r‖) + Γ ^ 2 * (‖G r a‖ * ‖G τ r‖) +
        Γ * ‖Gy τ‖ * (‖G r a‖ * ‖G b r‖) := by
    intro r
    have e1 : ‖(-cc * (G r σ * G τ a)) * G b r * Ty r‖ ≤ Γ ^ 2 * (‖G r σ‖ * ‖G b r‖) := by
      simp only [norm_mul, norm_neg]
      have := hG τ a
      have := hTy r
      have h0 : 0 ≤ ‖G r σ‖ * ‖G b r‖ := by positivity
      calc ‖cc‖ * (‖G r σ‖ * ‖G τ a‖) * ‖G b r‖ * ‖Ty r‖
          ≤ 1 * (‖G r σ‖ * Γ) * ‖G b r‖ * Γ := by gcongr
        _ = Γ ^ 2 * (‖G r σ‖ * ‖G b r‖) := by ring
    have e2 : ‖G r a * (-cc * (G b σ * G τ r)) * Ty r‖ ≤ Γ ^ 2 * (‖G r a‖ * ‖G τ r‖) := by
      simp only [norm_mul, norm_neg]
      have := hG b σ
      have := hTy r
      calc ‖G r a‖ * (‖cc‖ * (‖G b σ‖ * ‖G τ r‖)) * ‖Ty r‖
          ≤ ‖G r a‖ * (1 * (Γ * ‖G τ r‖)) * Γ := by gcongr
        _ = Γ ^ 2 * (‖G r a‖ * ‖G τ r‖) := by ring
    have e3 : ‖G r a * G b r * (-cc * (Tσ r * Gy τ))‖ ≤ Γ * ‖Gy τ‖ * (‖G r a‖ * ‖G b r‖) := by
      simp only [norm_mul, norm_neg]
      have := hTσ r
      calc ‖G r a‖ * ‖G b r‖ * (‖cc‖ * (‖Tσ r‖ * ‖Gy τ‖))
          ≤ ‖G r a‖ * ‖G b r‖ * (1 * (Γ * ‖Gy τ‖)) := by gcongr
        _ = Γ * ‖Gy τ‖ * (‖G r a‖ * ‖G b r‖) := by ring
    calc _ ≤ ‖(-cc * (G r σ * G τ a)) * G b r * Ty r‖ + ‖G r a * (-cc * (G b σ * G τ r)) * Ty r‖ +
          ‖G r a * G b r * (-cc * (Tσ r * Gy τ))‖ := by
          rw [add_mul]
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add e1 e2) e3
  calc (N : ℝ)⁻¹ * ‖∑ r, (((-cc * (G r σ * G τ a)) * G b r + G r a * (-cc * (G b σ * G τ r))) *
        Ty r + G r a * G b r * (-cc * (Tσ r * Gy τ)))‖
      ≤ (N : ℝ)⁻¹ * ∑ r, (Γ ^ 2 * (‖G r σ‖ * ‖G b r‖) + Γ ^ 2 * (‖G r a‖ * ‖G τ r‖) +
          Γ * ‖Gy τ‖ * (‖G r a‖ * ‖G b r‖)) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => key r)) hN
    _ = Γ ^ 2 * ((N : ℝ)⁻¹ * ∑ r, ‖G r σ‖ * ‖G b r‖) +
          Γ ^ 2 * ((N : ℝ)⁻¹ * ∑ r, ‖G r a‖ * ‖G τ r‖) +
          Γ * ‖Gy τ‖ * ((N : ℝ)⁻¹ * ∑ r, ‖G r a‖ * ‖G b r‖) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
    _ ≤ Γ ^ 2 * Z + Γ ^ 2 * Z + Γ * ‖Gy τ‖ * Z := by
        gcongr
        · exact hW σ b
        · exact hW a τ
        · exact hW a b
    _ = 2 * Γ ^ 2 * Z + Γ * Z * ‖Gy τ‖ := by ring

/-- The second derivatives of `(H̲G)_{uy}` along a slice, through one derivative `(∂_x + c ∂_y)/2`
of `hgDer(a, b)` in the direction `(σ, τ)`. -/
private lemma FIH_R2 {D N : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (s t : Idx D N) (u y : Idx D N → ℂ) (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (a b σ τ : Idx D N)
    (c' cc : ℂ) (hcc : ‖cc‖ ≤ 1)
    (hF : ∀ x y', FIH_op c' (FIH_fF h Λ z s t x y') = fun w =>
      -cc * (FIH_fF h Λ z s t x (Pi.single σ 1) w * FIH_fF h Λ z s t (Pi.single τ 1) y' w))
    (hH : FIH_op c' (fun w => star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h s t w)) Λ z *ᵥ
      Pi.single a 1)) = fun w =>
        cc * hgDer D N θ (Matrix.of (setEntry h s t w)) Λ z u (Pi.single a 1) σ τ)
    (w₀ : ℂ) (Γ lb Z : ℝ) (hΓ : 0 ≤ Γ)
    (hG : ∀ k l, ‖res (Matrix.of (setEntry h s t w₀) + Λ) z k l‖ ≤ Γ)
    (hTy : ∀ r, ‖star (tiltV D N θ u r) ⬝ᵥ (res (Matrix.of (setEntry h s t w₀) + Λ) z *ᵥ y)‖ ≤ Γ)
    (hTe : ∀ r k, ‖star (tiltV D N θ u r) ⬝ᵥ
      (res (Matrix.of (setEntry h s t w₀) + Λ) z *ᵥ Pi.single k 1)‖ ≤ Γ)
    (hD : ∀ k, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h s t w₀)) Λ z *ᵥ
      Pi.single k 1)‖ ≤ lb)
    (hW : ∀ k l, (N : ℝ)⁻¹ * ∑ r, ‖res (Matrix.of (setEntry h s t w₀) + Λ) z r k‖ *
      ‖res (Matrix.of (setEntry h s t w₀) + Λ) z l r‖ ≤ Z) :
    ‖FIH_op c' (fun w => hgDer D N θ (Matrix.of (setEntry h s t w)) Λ z u y a b) w₀‖ ≤
      ‖u a‖ * Γ * ‖(res (Matrix.of (setEntry h s t w₀) + Λ) z *ᵥ y) τ‖ +
        (‖u σ‖ * Γ + lb * Γ + Γ * Z) *
          ‖(res (Matrix.of (setEntry h s t w₀) + Λ) z *ᵥ y) b‖ +
        lb * Γ * ‖(res (Matrix.of (setEntry h s t w₀) + Λ) z *ᵥ y) τ‖ +
        (2 * Γ ^ 2 * Z + Γ * Z * ‖(res (Matrix.of (setEntry h s t w₀) + Λ) z *ᵥ y) τ‖) := by
  set fF := FIH_fF h Λ z s t with hfF
  have hsm : ∀ x y', ContDiff ℝ ∞ (fF x y') := fun x y' =>
    FIH_fF_smooth h hh Λ hΛ z hz.ne' s t x y'
  have hd : ∀ x y', DifferentiableAt ℝ (fF x y') w₀ := fun x y' => FIH_diff (hsm x y') w₀
  set fH := fun w => star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h s t w)) Λ z *ᵥ
      Pi.single a 1) with hfH
  have hdH : DifferentiableAt ℝ fH w₀ :=
    FIH_diff (FIH_hg_smooth θ hθ0 hθ1 h hh Λ hΛ z hz s t u _ hu (FIH_single_norm a)) w₀
  have e : (fun w => hgDer D N θ (Matrix.of (setEntry h s t w)) Λ z u y a b) = fun w =>
      (starRingEnd ℂ (u a) * fF (Pi.single b 1) y w - fH w * fF (Pi.single b 1) y w) -
        (N : ℂ)⁻¹ * ∑ r, fF (Pi.single r 1) (Pi.single a 1) w *
          fF (Pi.single b 1) (Pi.single r 1) w * fF (tiltV D N θ u r) y w := by
    funext w
    simp only [hgDer, hfF, hfH, FIH_fF, FIH_dot_single, Matrix.mulVec_single_one,
      Matrix.col_apply]
  have dA : DifferentiableAt ℝ (fun w => starRingEnd ℂ (u a) * fF (Pi.single b 1) y w) w₀ :=
    (differentiableAt_const _).fun_mul (hd _ _)
  have dB : DifferentiableAt ℝ (fun w => fH w * fF (Pi.single b 1) y w) w₀ :=
    hdH.fun_mul (hd _ _)
  have dT : ∀ r, DifferentiableAt ℝ (fun w => fF (Pi.single r 1) (Pi.single a 1) w *
      fF (Pi.single b 1) (Pi.single r 1) w * fF (tiltV D N θ u r) y w) w₀ := fun r =>
    ((hd _ _).fun_mul (hd _ _)).fun_mul (hd _ _)
  have dC : DifferentiableAt ℝ (fun w => ∑ r, fF (Pi.single r 1) (Pi.single a 1) w *
      fF (Pi.single b 1) (Pi.single r 1) w * fF (tiltV D N θ u r) y w) w₀ := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) fun r _ => (dT r).hasFDerivAt
    exact this.differentiableAt
  rw [e, FIH_op_sub c' (dA.fun_sub dB) ((differentiableAt_const _).fun_mul dC),
    FIH_op_sub c' dA dB, FIH_op_const_mul c' _ (hd _ _), FIH_op_mul c' hdH (hd _ _),
    FIH_op_const_mul c' _ dC, FIH_op_sum c' _ _ w₀ fun r _ => dT r]
  simp only [fun r => FIH_op_mul c' ((hd (Pi.single r 1) (Pi.single a 1)).fun_mul
    (hd (Pi.single b 1) (Pi.single r 1))) (hd (tiltV D N θ u r) y),
    fun r => FIH_op_mul c' (hd (Pi.single r 1) (Pi.single a 1)) (hd (Pi.single b 1)
      (Pi.single r 1)), hF, hH]
  set G := res (Matrix.of (setEntry h s t w₀) + Λ) z with hGdef
  simp only [hfF, hfH, FIH_fF, FIH_dot_single, FIH_mulVec_single, ← hGdef]
  -- the three parts
  have hR1 := FIH_R1 θ (Matrix.of (setEntry h s t w₀)) Λ z u (Pi.single a 1) σ τ Γ lb Z hΓ
    (hD σ) (fun r => hTe r a) (hW σ τ)
  rw [← hGdef, Matrix.mulVec_single_one] at hR1
  simp only [Matrix.col_apply] at hR1
  have hS := FIH_R2_sum N cc hcc G (fun r => star (tiltV D N θ u r) ⬝ᵥ (G *ᵥ y))
    (fun r => star (tiltV D N θ u r) ⬝ᵥ (G *ᵥ Pi.single σ 1)) (G *ᵥ y) a b σ τ Γ Z hΓ hG
    hTy (fun r => hTe r σ) hW
  have hDa := hD a
  have hlb : 0 ≤ lb := (norm_nonneg _).trans hDa
  have p1 : ‖starRingEnd ℂ (u a) * (-cc * (G b σ * (G *ᵥ y) τ))‖ ≤ ‖u a‖ * Γ * ‖(G *ᵥ y) τ‖ := by
    simp only [norm_mul, norm_neg, Complex.norm_conj]
    have := hG b σ
    calc ‖u a‖ * (‖cc‖ * (‖G b σ‖ * ‖(G *ᵥ y) τ‖)) ≤ ‖u a‖ * (1 * (Γ * ‖(G *ᵥ y) τ‖)) := by
          gcongr
      _ = _ := by ring
  have p2 : ‖cc * hgDer D N θ (Matrix.of (setEntry h s t w₀)) Λ z u (Pi.single a 1) σ τ *
      (G *ᵥ y) b + star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h s t w₀)) Λ z *ᵥ
        Pi.single a 1) * (-cc * (G b σ * (G *ᵥ y) τ))‖ ≤
      (‖u σ‖ * Γ + lb * Γ + Γ * Z) * ‖(G *ᵥ y) b‖ + lb * Γ * ‖(G *ᵥ y) τ‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul]
      have hGt := hG τ a
      have h1 : ‖hgDer D N θ (Matrix.of (setEntry h s t w₀)) Λ z u (Pi.single a 1) σ τ‖ ≤
          ‖u σ‖ * Γ + lb * Γ + Γ * Z := by
        refine hR1.trans ?_
        gcongr
      calc ‖cc‖ * ‖hgDer D N θ (Matrix.of (setEntry h s t w₀)) Λ z u (Pi.single a 1) σ τ‖ *
          ‖(G *ᵥ y) b‖ ≤ 1 * (‖u σ‖ * Γ + lb * Γ + Γ * Z) * ‖(G *ᵥ y) b‖ := by gcongr
        _ = _ := by ring
    · simp only [norm_mul, norm_neg]
      have := hG b σ
      calc ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h s t w₀)) Λ z *ᵥ Pi.single a 1)‖ *
          (‖cc‖ * (‖G b σ‖ * ‖(G *ᵥ y) τ‖)) ≤ lb * (1 * (Γ * ‖(G *ᵥ y) τ‖)) := by gcongr
        _ = _ := by ring
  refine ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add p1 p2)) hS)).trans (le_of_eq ?_)
  ring

/-! ### Exponent bookkeeping and Ward sums -/

/-- `x^a l^b ≤ (x l²)^{n/3}` for `a + b = n`, `n ≤ 3a` and `0 ≤ x ≤ l`. -/
private lemma FIH_norm (x l : ℝ) (hx : 0 ≤ x) (hxl : x ≤ l) (a b n : ℕ) (hab : a + b = n)
    (h3 : n ≤ 3 * a) : x ^ a * l ^ b ≤ (x * l ^ 2) ^ ((n : ℝ) / 3) := by
  have hl : 0 ≤ l := hx.trans hxl
  have key : (x ^ a * l ^ b) ^ 3 ≤ (x * l ^ 2) ^ n := by
    have h1 : (x ^ a * l ^ b) ^ 3 = x ^ (3 * a) * l ^ (3 * b) := by ring
    have h2 : x ^ (3 * a) = x ^ n * x ^ (3 * a - n) := by
      rw [← pow_add]
      congr 1
      omega
    have h3' : x ^ (3 * a - n) ≤ l ^ (3 * a - n) := pow_le_pow_left₀ hx hxl _
    have h4 : l ^ (3 * a - n) * l ^ (3 * b) = l ^ (2 * n) := by
      rw [← pow_add]
      congr 1
      omega
    have h5 : (x * l ^ 2) ^ n = x ^ n * l ^ (2 * n) := by
      rw [mul_pow, ← pow_mul]
    calc (x ^ a * l ^ b) ^ 3 = x ^ n * x ^ (3 * a - n) * l ^ (3 * b) := by rw [h1, h2]
      _ ≤ x ^ n * l ^ (3 * a - n) * l ^ (3 * b) := by gcongr
      _ = (x * l ^ 2) ^ n := by rw [mul_assoc, h4, h5]
  have hA : 0 ≤ x ^ a * l ^ b := by positivity
  have hB : 0 ≤ x * l ^ 2 := by positivity
  calc x ^ a * l ^ b = ((x ^ a * l ^ b) ^ 3) ^ (((3 : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hA (by norm_num)).symm
    _ ≤ ((x * l ^ 2) ^ n) ^ (((3 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) key (by norm_num)
    _ = (x * l ^ 2) ^ ((n : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
        congr 1

/-- The sums of the Ward bounds: `s_i = |u_i|`, `g_i = |(G v)_i|`, `Σ s² ≤ 1`, `g ≤ Γ`,
`Σ g² ≤ (M ζ)²` over an index set of size `D M²`. -/
private lemma FIH_sums {ι : Type*} [Fintype ι] (s g : ι → ℝ) (D M ζ Γ : ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∑ i, s i ^ 2 ≤ 1) (hg0 : ∀ i, 0 ≤ g i) (hgΓ : ∀ i, g i ≤ Γ)
    (hg2 : ∑ i, g i ^ 2 ≤ (M * ζ) ^ 2) (hcard : (Fintype.card ι : ℝ) = D * M ^ 2)
    (hM : 0 ≤ M) (hζ : 0 ≤ ζ) (hD : 0 ≤ D) (hΓ : 0 ≤ Γ) :
    ∑ i, s i ≤ Real.sqrt D * M ∧ ∑ i, g i ≤ Real.sqrt D * M * (M * ζ) ∧
      ∑ i, s i * g i ≤ M * ζ ∧ ∑ i, s i ^ 2 * g i ≤ Γ ∧ ∑ i, s i * g i ^ 2 ≤ Γ * (M * ζ) ∧
      ∑ i, g i ^ 3 ≤ Γ * (M * ζ) ^ 2 ∧ ∑ i, s i ^ 3 ≤ 1 := by
  have hs1' : ∀ i, s i ≤ 1 := by
    intro i
    have : s i ^ 2 ≤ 1 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (s j)) (Finset.mem_univ i)).trans hs1
    nlinarith [hs0 i]
  have hsq : Real.sqrt (Fintype.card ι : ℝ) = Real.sqrt D * M := by
    rw [hcard, Real.sqrt_mul hD, Real.sqrt_sq hM]
  have h1 : ∑ i, s i ≤ Real.sqrt D * M := by
    have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => (1 : ℝ)) s
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    refine this.trans ?_
    rw [hsq]
    have := Real.sqrt_le_one.mpr hs1
    have h0 : 0 ≤ Real.sqrt D * M := by positivity
    nlinarith [Real.sqrt_nonneg (∑ i, s i ^ 2)]
  have hgs : Real.sqrt (∑ i, g i ^ 2) ≤ M * ζ := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hg2
  have h2 : ∑ i, g i ≤ Real.sqrt D * M * (M * ζ) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => (1 : ℝ)) g
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    refine this.trans ?_
    rw [hsq]
    exact mul_le_mul_of_nonneg_left hgs (by positivity)
  have h3 : ∑ i, s i * g i ≤ M * ζ := by
    refine (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ s g).trans ?_
    have := Real.sqrt_le_one.mpr hs1
    nlinarith [Real.sqrt_nonneg (∑ i, s i ^ 2), Real.sqrt_nonneg (∑ i, g i ^ 2)]
  have h4 : ∑ i, s i ^ 2 * g i ≤ Γ := by
    calc ∑ i, s i ^ 2 * g i ≤ ∑ i, s i ^ 2 * Γ :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hgΓ i) (sq_nonneg _)
      _ = (∑ i, s i ^ 2) * Γ := by rw [Finset.sum_mul]
      _ ≤ 1 * Γ := mul_le_mul_of_nonneg_right hs1 hΓ
      _ = Γ := one_mul Γ
  have h5 : ∑ i, s i * g i ^ 2 ≤ Γ * (M * ζ) := by
    calc ∑ i, s i * g i ^ 2 ≤ ∑ i, Γ * (s i * g i) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hs0 i
          have := hg0 i
          have := hgΓ i
          nlinarith [mul_nonneg (hs0 i) (hg0 i)]
      _ = Γ * ∑ i, s i * g i := by rw [Finset.mul_sum]
      _ ≤ Γ * (M * ζ) := mul_le_mul_of_nonneg_left h3 hΓ
  have h6 : ∑ i, g i ^ 3 ≤ Γ * (M * ζ) ^ 2 := by
    calc ∑ i, g i ^ 3 ≤ ∑ i, Γ * g i ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hg0 i
          have := hgΓ i
          nlinarith [sq_nonneg (g i)]
      _ = Γ * ∑ i, g i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ Γ * (M * ζ) ^ 2 := mul_le_mul_of_nonneg_left hg2 hΓ
  have h7 : ∑ i, s i ^ 3 ≤ 1 := by
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) hs1
    have := hs0 i
    have := hs1' i
    nlinarith [sq_nonneg (s i)]
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

private lemma FIH_dsum {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    ∑ i, ∑ j, a i * b j = (∑ i, a i) * ∑ j, b j := (Finset.sum_mul_sum _ _ _ _).symm

private lemma FIH_mm {a b A B : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ A) (hb : b ≤ B) :
    a * b ≤ A * B :=
  mul_le_mul ha hb hb0 (ha0.trans ha)

set_option maxHeartbeats 1000000 in
/-- The four double sums of the order-`k` terms with `n ≥ k` factors of `(H̲G)_{uv}`
differentiated: with `d₁ = s_i g_j + s_j g_i + Γ λ` and
`d₂ = Γ (s_i + s_j)(g_i + g_j) + λ Γ (g_i + g_j) + Γ² ζ²`. -/
private lemma FIH_S4 {ι : Type*} [Fintype ι] (s g : ι → ℝ) (D M ζ Γ lb : ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∑ i, s i ^ 2 ≤ 1) (hg0 : ∀ i, 0 ≤ g i) (hgΓ : ∀ i, g i ≤ Γ)
    (hg2 : ∑ i, g i ^ 2 ≤ (M * ζ) ^ 2) (hcard : (Fintype.card ι : ℝ) = D * M ^ 2)
    (hD : 1 ≤ D) (hΓ : 1 ≤ Γ) (hM : 1 ≤ M) (hMζ : 1 ≤ M * ζ) (hζ1 : ζ ≤ 1) (hζl : ζ ≤ lb) :
    ∑ i, ∑ j, s i * (g i + g j) ≤ 2 * D * M ^ 3 * ζ ∧
    ∑ i, ∑ j, s i * g j * (s i * g j + s j * g i + Γ * lb) ^ 2 ≤
      9 * D * M ^ 3 * Γ ^ 2 * ζ * lb ^ 2 ∧
    ∑ i, ∑ j, s i * (g i + g j) * (s i * g j + s j * g i + Γ * lb) ≤
      6 * D * M ^ 3 * Γ * ζ * lb ∧
    ∑ i, ∑ j, s i * g j * (Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) +
      Γ ^ 2 * ζ ^ 2) ≤ 8 * D * M ^ 3 * Γ ^ 2 * ζ * lb := by
  have hζ0 : 0 ≤ ζ := by
    by_contra h
    push_neg at h
    nlinarith
  have hM0 : 0 ≤ M := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hΓ0 : 0 ≤ Γ := by linarith
  have hl0 : 0 ≤ lb := hζ0.trans hζl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    FIH_sums s g D M ζ Γ hs0 hs1 hg0 hgΓ hg2 hcard hM0 hζ0 hD0 hΓ0
  have hMl : 1 ≤ M * lb := hMζ.trans (mul_le_mul_of_nonneg_left hζl hM0)
  have hsD : Real.sqrt D ≤ D := by
    rw [Real.sqrt_le_left hD0]
    nlinarith
  have hsD0 := Real.sqrt_nonneg D
  have hsDD : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hD0
  -- nonnegativity of the single sums
  have n1 : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => hs0 i
  have n2 : 0 ≤ ∑ i, g i := Finset.sum_nonneg fun i _ => hg0 i
  have n3 : 0 ≤ ∑ i, s i * g i := Finset.sum_nonneg fun i _ => mul_nonneg (hs0 i) (hg0 i)
  have n4 : 0 ≤ ∑ i, s i ^ 2 * g i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hg0 i)
  have n5 : 0 ≤ ∑ i, s i * g i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hs0 i) (sq_nonneg _)
  have n6 : 0 ≤ ∑ i, g i ^ 3 := Finset.sum_nonneg fun i _ => pow_nonneg (hg0 i) 3
  have n7 : 0 ≤ ∑ i, s i ^ 3 := Finset.sum_nonneg fun i _ => pow_nonneg (hs0 i) 3
  have n8 : 0 ≤ ∑ i, s i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have n9 : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc1 : ∑ _j : ι, (1 : ℝ) = D * M ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
  -- products of single sums
  have P_sg : (∑ i, s i) * ∑ i, g i ≤ D * M ^ 3 * ζ := by
    calc _ ≤ (Real.sqrt D * M) * (Real.sqrt D * M * (M * ζ)) := FIH_mm n1 n2 h1 h2
      _ = (Real.sqrt D * Real.sqrt D) * M ^ 3 * ζ := by ring
      _ = _ := by rw [hsDD]
  have P_s2g_g : (∑ i, s i ^ 2 * g i) * ∑ i, g i ≤ Real.sqrt D * Γ * M ^ 2 * ζ := by
    calc _ ≤ Γ * (Real.sqrt D * M * (M * ζ)) := FIH_mm n4 n2 h4 h2
      _ = _ := by ring
  have P_sg2_s : (∑ i, s i * g i ^ 2) * ∑ i, s i ≤ Real.sqrt D * Γ * M ^ 2 * ζ := by
    calc _ ≤ (Γ * (M * ζ)) * (Real.sqrt D * M) := FIH_mm n5 n1 h5 h1
      _ = _ := by ring
  have P_sg_c : (∑ i, s i * g i) * ∑ _j : ι, (1 : ℝ) ≤ D * M ^ 3 * ζ := by
    rw [hc1]
    calc _ ≤ (M * ζ) * (D * M ^ 2) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = _ := by ring
  have P_s2_g2 : (∑ i, s i ^ 2) * ∑ i, g i ^ 2 ≤ M ^ 2 * ζ ^ 2 := by
    calc _ ≤ 1 * (M * ζ) ^ 2 := FIH_mm n8 n9 hs1 hg2
      _ = _ := by ring
  have P_sg_sg : (∑ i, s i * g i) * ∑ i, s i * g i ≤ M ^ 2 * ζ ^ 2 := by
    calc _ ≤ (M * ζ) * (M * ζ) := FIH_mm n3 n3 h3 h3
      _ = _ := by ring
  have P_sg_g : (∑ i, s i * g i) * ∑ i, g i ≤ Real.sqrt D * M ^ 3 * ζ ^ 2 := by
    calc _ ≤ (M * ζ) * (Real.sqrt D * M * (M * ζ)) := FIH_mm n3 n2 h3 h2
      _ = _ := by ring
  have P_s_g2 : (∑ i, s i) * ∑ i, g i ^ 2 ≤ Real.sqrt D * M ^ 3 * ζ ^ 2 := by
    calc _ ≤ (Real.sqrt D * M) * (M * ζ) ^ 2 := FIH_mm n1 n9 h1 hg2
      _ = _ := by ring
  have P_s3_g3 : (∑ i, s i ^ 3) * ∑ i, g i ^ 3 ≤ Γ * M ^ 2 * ζ ^ 2 := by
    calc _ ≤ 1 * (Γ * (M * ζ) ^ 2) := FIH_mm n7 n6 h7 h6
      _ = _ := by ring
  have P_sg2_s2g : (∑ i, s i * g i ^ 2) * ∑ i, s i ^ 2 * g i ≤ Γ ^ 2 * M * ζ := by
    calc _ ≤ (Γ * (M * ζ)) * Γ := FIH_mm n5 n4 h5 h4
      _ = _ := by ring
  -- elementary comparisons
  have U0 : 0 ≤ D * M ^ 3 * Γ * ζ * lb := by positivity
  have e1 : Real.sqrt D * Γ * M ^ 2 * ζ ≤ D * M ^ 3 * Γ * ζ * lb := by
    have : Real.sqrt D * Γ * M ^ 2 * ζ ≤ D * Γ * M ^ 2 * ζ * (M * lb) := by
      calc Real.sqrt D * Γ * M ^ 2 * ζ = Real.sqrt D * (Γ * M ^ 2 * ζ) * 1 := by ring
        _ ≤ D * (Γ * M ^ 2 * ζ) * (M * lb) := by gcongr
        _ = _ := by ring
    linarith [show D * Γ * M ^ 2 * ζ * (M * lb) = D * M ^ 3 * Γ * ζ * lb by ring]
  have hζMl : ζ ≤ M * lb := by nlinarith
  have e2 : M ^ 2 * ζ ^ 2 ≤ D * M ^ 3 * Γ * ζ * lb := by
    calc M ^ 2 * ζ ^ 2 = 1 * 1 * M ^ 2 * ζ * ζ := by ring
      _ ≤ D * Γ * M ^ 2 * ζ * (M * lb) := by gcongr
      _ = _ := by ring
  have e3 : Real.sqrt D * M ^ 3 * ζ ^ 2 ≤ D * M ^ 3 * Γ * ζ * lb := by
    calc Real.sqrt D * M ^ 3 * ζ ^ 2 = Real.sqrt D * M ^ 3 * ζ * ζ := by ring
      _ ≤ D * M ^ 3 * ζ * (Γ * lb) := by
          gcongr
          calc ζ = 1 * ζ := (one_mul ζ).symm
            _ ≤ Γ * lb := by gcongr
      _ = _ := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the generic sum
    calc ∑ i, ∑ j, s i * (g i + g j)
        = (∑ i, s i * g i) * (∑ _j : ι, (1 : ℝ)) + (∑ i, s i) * ∑ j, g j := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
          congr 1
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          ring
      _ ≤ D * M ^ 3 * ζ + D * M ^ 3 * ζ := add_le_add P_sg_c P_sg
      _ = _ := by ring
  · -- `k` factors with one derivative each
    have hpt : ∀ i j, s i * g j * (s i * g j + s j * g i + Γ * lb) ^ 2 ≤
        3 * (s i ^ 3 * g j ^ 3) + 3 * ((s i * g i ^ 2) * (s j ^ 2 * g j)) +
          3 * (Γ * lb) ^ 2 * (s i * g j) := by
      intro i j
      have hsg : 0 ≤ s i * g j := mul_nonneg (hs0 i) (hg0 j)
      have hq : (s i * g j + s j * g i + Γ * lb) ^ 2 ≤
          3 * ((s i * g j) ^ 2 + (s j * g i) ^ 2 + (Γ * lb) ^ 2) := by
        nlinarith [sq_nonneg (s i * g j - s j * g i), sq_nonneg (s i * g j - Γ * lb),
          sq_nonneg (s j * g i - Γ * lb)]
      calc _ ≤ s i * g j * (3 * ((s i * g j) ^ 2 + (s j * g i) ^ 2 + (Γ * lb) ^ 2)) :=
            mul_le_mul_of_nonneg_left hq hsg
        _ = _ := by ring
    calc ∑ i, ∑ j, s i * g j * (s i * g j + s j * g i + Γ * lb) ^ 2
        ≤ ∑ i, ∑ j, (3 * (s i ^ 3 * g j ^ 3) + 3 * ((s i * g i ^ 2) * (s j ^ 2 * g j)) +
          3 * (Γ * lb) ^ 2 * (s i * g j)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
      _ = 3 * ((∑ i, s i ^ 3) * ∑ j, g j ^ 3) +
            3 * ((∑ i, s i * g i ^ 2) * ∑ j, s j ^ 2 * g j) +
            3 * (Γ * lb) ^ 2 * ((∑ i, s i) * ∑ j, g j) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ 3 * (Γ * M ^ 2 * ζ ^ 2) + 3 * (Γ ^ 2 * M * ζ) + 3 * (Γ * lb) ^ 2 * (D * M ^ 3 * ζ) := by
          gcongr
      _ ≤ _ := by
          have f1 : Γ * M ^ 2 * ζ ^ 2 ≤ D * M ^ 3 * Γ ^ 2 * ζ * lb ^ 2 := by
            calc Γ * M ^ 2 * ζ ^ 2 = 1 * 1 * Γ * M ^ 2 * ζ * ζ := by ring
              _ ≤ D * Γ * Γ * M ^ 2 * ζ * (lb * (M * lb)) := by
                  gcongr
                  calc ζ = ζ * 1 := (mul_one ζ).symm
                    _ ≤ lb * (M * lb) := FIH_mm hζ0 zero_le_one hζl hMl
              _ = _ := by ring
          have f2 : Γ ^ 2 * M * ζ ≤ D * M ^ 3 * Γ ^ 2 * ζ * lb ^ 2 := by
            calc Γ ^ 2 * M * ζ = 1 * Γ ^ 2 * M * ζ * (1 * 1) := by ring
              _ ≤ D * Γ ^ 2 * M * ζ * ((M * lb) * (M * lb)) := by gcongr
              _ = _ := by ring
          have g3 : 3 * (Γ * lb) ^ 2 * (D * M ^ 3 * ζ) = 3 * (D * M ^ 3 * Γ ^ 2 * ζ * lb ^ 2) := by
            ring
          linarith
  · -- `G_{jv}` with one derivative
    have e : ∀ i j, s i * (g i + g j) * (s i * g j + s j * g i + Γ * lb) =
        (s i ^ 2 * g i) * g j + (s i * g i ^ 2) * s j + Γ * lb * ((s i * g i) * 1) +
          s i ^ 2 * g j ^ 2 + (s i * g i) * (s j * g j) + Γ * lb * (s i * g j) := by
      intro i j; ring
    simp only [e]
    calc _ = (∑ i, s i ^ 2 * g i) * (∑ j, g j) + (∑ i, s i * g i ^ 2) * (∑ j, s j) +
          Γ * lb * ((∑ i, s i * g i) * ∑ _j : ι, (1 : ℝ)) +
          (∑ i, s i ^ 2) * (∑ j, g j ^ 2) + (∑ i, s i * g i) * (∑ j, s j * g j) +
          Γ * lb * ((∑ i, s i) * ∑ j, g j) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ Real.sqrt D * Γ * M ^ 2 * ζ + Real.sqrt D * Γ * M ^ 2 * ζ +
          Γ * lb * (D * M ^ 3 * ζ) + M ^ 2 * ζ ^ 2 + M ^ 2 * ζ ^ 2 +
          Γ * lb * (D * M ^ 3 * ζ) := by
          gcongr
      _ ≤ _ := by
          have g3 : Γ * lb * (D * M ^ 3 * ζ) = D * M ^ 3 * Γ * ζ * lb := by ring
          linarith
  · -- one factor with two derivatives
    have e : ∀ i j, s i * g j * (Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) +
        Γ ^ 2 * ζ ^ 2) =
        Γ * ((s i ^ 2 * g i) * g j) + Γ * (s i ^ 2 * g j ^ 2) + Γ * ((s i * g i) * (s j * g j)) +
          Γ * (s i * (s j * g j ^ 2)) + lb * Γ * ((s i * g i) * g j) +
          lb * Γ * (s i * g j ^ 2) + Γ ^ 2 * ζ ^ 2 * (s i * g j) := by
      intro i j; ring
    simp only [e]
    calc _ = Γ * ((∑ i, s i ^ 2 * g i) * (∑ j, g j)) + Γ * ((∑ i, s i ^ 2) * (∑ j, g j ^ 2)) +
          Γ * ((∑ i, s i * g i) * (∑ j, s j * g j)) + Γ * ((∑ i, s i) * (∑ j, s j * g j ^ 2)) +
          lb * Γ * ((∑ i, s i * g i) * (∑ j, g j)) + lb * Γ * ((∑ i, s i) * (∑ j, g j ^ 2)) +
          Γ ^ 2 * ζ ^ 2 * ((∑ i, s i) * ∑ j, g j) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ Γ * (Real.sqrt D * Γ * M ^ 2 * ζ) + Γ * (M ^ 2 * ζ ^ 2) + Γ * (M ^ 2 * ζ ^ 2) +
          Γ * (Real.sqrt D * Γ * M ^ 2 * ζ) + lb * Γ * (Real.sqrt D * M ^ 3 * ζ ^ 2) +
          lb * Γ * (Real.sqrt D * M ^ 3 * ζ ^ 2) + Γ ^ 2 * ζ ^ 2 * (D * M ^ 3 * ζ) := by
          have P' : (∑ i, s i) * ∑ j, s j * g j ^ 2 ≤ Real.sqrt D * Γ * M ^ 2 * ζ := by
            rw [mul_comm]; exact P_sg2_s
          gcongr
      _ ≤ _ := by
          have f1 : Real.sqrt D * M ^ 3 * ζ ^ 2 ≤ D * M ^ 3 * Γ * ζ := by
            calc Real.sqrt D * M ^ 3 * ζ ^ 2 = Real.sqrt D * M ^ 3 * ζ * ζ := by ring
              _ ≤ D * M ^ 3 * ζ * Γ := by gcongr; linarith
              _ = _ := by ring
          have f2 : Γ ^ 2 * ζ ^ 2 * (D * M ^ 3 * ζ) ≤ D * M ^ 3 * Γ ^ 2 * ζ * lb := by
            calc Γ ^ 2 * ζ ^ 2 * (D * M ^ 3 * ζ) = D * M ^ 3 * Γ ^ 2 * ζ * (ζ * ζ) := by ring
              _ ≤ D * M ^ 3 * Γ ^ 2 * ζ * (lb * 1) := by gcongr
              _ = _ := by ring
          have g1 := mul_le_mul_of_nonneg_left e1 hΓ0
          have g2 := mul_le_mul_of_nonneg_left e2 hΓ0
          have g3 := mul_le_mul_of_nonneg_left f1 (mul_nonneg hl0 hΓ0)
          linarith

/-- The normalization of the terms with at most `k - 2` differentiated factors:
`c₁^{q+1} Γ^k (z₁ Γ² M ζ)^q · 2 D M³ ζ ≤ 20 D c₁^{k+1} M^{k+1} ζ̂^{q+1}`
for `k = q + 2 + e`, `Γ ≤ M`, with `ζ̂ = c_D z₁ Γ³ ζ`. -/
private lemma FIH_num1 (q e : ℕ) (D M ζ Γ z1 cD c₁ : ℝ) (hD : 0 ≤ D) (hΓ : 1 ≤ Γ) (hΓM : Γ ≤ M)
    (hζ : 0 ≤ ζ) (hz1 : 1 ≤ z1) (hcD : 1 ≤ cD) (hc₁ : 1 ≤ c₁) :
    c₁ ^ (q + 1) * Γ ^ (q + 2 + e) * (z1 * Γ ^ 2 * (M * ζ)) ^ q * (2 * D * M ^ 3 * ζ) ≤
      M ^ (q + 2 + e + 1) * (20 * D * c₁ ^ (q + 2 + e + 1)) * (cD * z1 * Γ ^ 3 * ζ) ^ (q + 1) := by
  have hΓ0 : 0 ≤ Γ := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hz0 : 0 ≤ z1 := by linarith
  have h1 : c₁ ^ (q + 1) ≤ c₁ ^ (q + 2 + e + 1) := pow_le_pow_right₀ hc₁ (by omega)
  have h2 : Γ ^ e ≤ M ^ e := pow_le_pow_left₀ hΓ0 hΓM e
  have h3 : 1 ≤ cD ^ (q + 1) * z1 * Γ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hcD) hz1) hΓ
  have h4 : 0 ≤ Γ ^ (3 * q + 2) * z1 ^ q * ζ ^ (q + 1) := by positivity
  have e1 : c₁ ^ (q + 1) * Γ ^ (q + 2 + e) * (z1 * Γ ^ 2 * (M * ζ)) ^ q * (2 * D * M ^ 3 * ζ) =
      2 * D * c₁ ^ (q + 1) * Γ ^ e * M ^ (q + 3) * (Γ ^ (3 * q + 2) * z1 ^ q * ζ ^ (q + 1)) := by
    ring
  have e2 : M ^ (q + 2 + e + 1) * (20 * D * c₁ ^ (q + 2 + e + 1)) *
      (cD * z1 * Γ ^ 3 * ζ) ^ (q + 1) =
      20 * D * c₁ ^ (q + 2 + e + 1) * M ^ e * M ^ (q + 3) *
        ((cD ^ (q + 1) * z1 * Γ) * (Γ ^ (3 * q + 2) * z1 ^ q * ζ ^ (q + 1))) := by
    ring
  rw [e1, e2]
  have h5 : Γ ^ (3 * q + 2) * z1 ^ q * ζ ^ (q + 1) ≤
      (cD ^ (q + 1) * z1 * Γ) * (Γ ^ (3 * q + 2) * z1 ^ q * ζ ^ (q + 1)) :=
    le_mul_of_one_le_left h4 h3
  have h6 : 2 * D * c₁ ^ (q + 1) ≤ 20 * D * c₁ ^ (q + 2 + e + 1) := by
    have : 0 ≤ D * c₁ ^ (q + 1) := by positivity
    nlinarith
  gcongr

/-- The normalization of the terms with `k - 1` or `k` differentiated factors:
`c₁^{t+3} (z₁ Γ³ M ζ)^t · A D M³ Γ² ζ L ≤
20 D c₁^{t+3} M^{t+3} ζ̂^{t+1} L` for `A ≤ 20`, `L ≥ 0`. -/
private lemma FIH_num2 (t : ℕ) (A D M ζ Γ z1 cD c₁ L : ℝ) (hA : A ≤ 20) (hD : 0 ≤ D)
    (hΓ : 1 ≤ Γ) (hM : 0 ≤ M) (hζ : 0 ≤ ζ) (hz1 : 1 ≤ z1) (hcD : 1 ≤ cD) (hc₁ : 1 ≤ c₁)
    (hL : 0 ≤ L) :
    c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t * (A * D * M ^ 3 * Γ ^ 2 * ζ * L) ≤
      M ^ (t + 3) * (20 * D * c₁ ^ (t + 3)) * (cD * z1 * Γ ^ 3 * ζ) ^ (t + 1) * L := by
  have hΓ0 : 0 ≤ Γ := by linarith
  have hz0 : 0 ≤ z1 := by linarith
  have hb : z1 * Γ ^ 3 * ζ ≤ cD * z1 * Γ ^ 3 * ζ := by
    have : 0 ≤ z1 * Γ ^ 3 * ζ := by positivity
    nlinarith
  have hb2 : Γ ^ 2 * ζ ≤ cD * z1 * Γ ^ 3 * ζ := by
    have h1 : Γ ^ 2 * ζ ≤ Γ ^ 2 * ζ * Γ := le_mul_of_one_le_right (by positivity) hΓ
    have h2 : 0 ≤ Γ ^ 2 * ζ * Γ := by positivity
    have h3 : 1 ≤ cD * z1 := one_le_mul_of_one_le_of_one_le hcD hz1
    calc Γ ^ 2 * ζ ≤ Γ ^ 2 * ζ * Γ := h1
      _ ≤ (cD * z1) * (Γ ^ 2 * ζ * Γ) := le_mul_of_one_le_left h2 h3
      _ = _ := by ring
  have e1 : c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t * (A * D * M ^ 3 * Γ ^ 2 * ζ * L) =
      A * (D * c₁ ^ (t + 3) * M ^ (t + 3) * L) * ((z1 * Γ ^ 3 * ζ) ^ t * (Γ ^ 2 * ζ)) := by
    ring
  have e2 : M ^ (t + 3) * (20 * D * c₁ ^ (t + 3)) * (cD * z1 * Γ ^ 3 * ζ) ^ (t + 1) * L =
      20 * (D * c₁ ^ (t + 3) * M ^ (t + 3) * L) *
        ((cD * z1 * Γ ^ 3 * ζ) ^ t * (cD * z1 * Γ ^ 3 * ζ)) := by
    ring
  rw [e1, e2]
  have h0 : 0 ≤ D * c₁ ^ (t + 3) * M ^ (t + 3) * L := by
    have : 0 ≤ c₁ := by linarith
    positivity
  have h7 : (z1 * Γ ^ 3 * ζ) ^ t * (Γ ^ 2 * ζ) ≤
      (cD * z1 * Γ ^ 3 * ζ) ^ t * (cD * z1 * Γ ^ 3 * ζ) := by
    gcongr
  have h8 : 0 ≤ (z1 * Γ ^ 3 * ζ) ^ t * (Γ ^ 2 * ζ) := by positivity
  have hA0 : A * (D * c₁ ^ (t + 3) * M ^ (t + 3) * L) ≤
      20 * (D * c₁ ^ (t + 3) * M ^ (t + 3) * L) := mul_le_mul_of_nonneg_right hA h0
  calc A * (D * c₁ ^ (t + 3) * M ^ (t + 3) * L) * ((z1 * Γ ^ 3 * ζ) ^ t * (Γ ^ 2 * ζ))
      ≤ 20 * (D * c₁ ^ (t + 3) * M ^ (t + 3) * L) * ((z1 * Γ ^ 3 * ζ) ^ t * (Γ ^ 2 * ζ)) :=
        mul_le_mul_of_nonneg_right hA0 h8
    _ ≤ _ := mul_le_mul_of_nonneg_left h7 (by positivity)

/-- The bound on the good event of one Leibniz word with `G_{jv}` differentiated `r` times and the
factor `m` of `(H̲G)_{uv}^{p-1} conj((H̲G)_{uv})^p` differentiated `c_m` times, `r + Σ c_m = k`:
after `Σ_{i,j} |u_i|`, `≤ M^{k+1} K (ζ̂ λ²)^{(q+1)/3} |(H̲G)_{uv}|^{2p-1-q}`, where `q` is the
number of differentiated factors. -/
private lemma FIH_word {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s g : ι → ℝ) (βG βD : ι → ι → ℕ → ℝ) (D M ζ Γ lb z1 cD c₁ δ : ℝ) (k r : ℕ) (c : κ → ℕ)
    (hk : 2 ≤ k) (hrc : r + ∑ m, c m = k)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∑ i, s i ^ 2 ≤ 1) (hg0 : ∀ i, 0 ≤ g i) (hgΓ : ∀ i, g i ≤ Γ)
    (hg2 : ∑ i, g i ^ 2 ≤ (M * ζ) ^ 2) (hcard : (Fintype.card ι : ℝ) = D * M ^ 2)
    (hD : 1 ≤ D) (hΓ : 1 ≤ Γ) (hΓM : Γ ≤ M) (hMζ : 1 ≤ M * ζ) (hζ1 : ζ ≤ 1)
    (hz1 : 1 ≤ z1) (hcD : 1 ≤ cD) (hζl : cD * z1 * Γ ^ 3 * ζ ≤ lb) (hc₁ : 1 ≤ c₁) (hδ : 0 ≤ δ)
    (hGnn : ∀ i j l, 0 ≤ βG i j l) (hG0 : ∀ i j, βG i j 0 ≤ c₁ * g j)
    (hG : ∀ i j l, l ≤ k → βG i j l ≤ c₁ * Γ ^ l * (g i + g j))
    (hDnn : ∀ i j l, 0 ≤ βD i j l) (hD0 : ∀ i j, βD i j 0 = δ)
    (hDl : ∀ i j l, 1 ≤ l → l ≤ k → βD i j l ≤ c₁ * z1 * Γ ^ (l + 2) * (M * ζ))
    (hD1 : ∀ i j, βD i j 1 ≤ c₁ * (s i * g j + s j * g i + Γ * lb))
    (hD2 : ∀ i j, βD i j 2 ≤
      c₁ * (Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) + Γ ^ 2 * ζ ^ 2)) :
    ∑ i, ∑ j, s i * (βG i j r * ∏ m, βD i j (c m)) ≤
      M ^ (k + 1) * (20 * D * c₁ ^ (k + 1)) *
        (cD * z1 * Γ ^ 3 * ζ * lb ^ 2) ^
          ((((Finset.univ.filter fun m => 1 ≤ c m).card + 1 : ℕ) : ℝ) / 3) *
        δ ^ (Fintype.card κ - (Finset.univ.filter fun m => 1 ≤ c m).card) := by
  classical
  set S := Finset.univ.filter fun m => 1 ≤ c m with hS
  set q := S.card with hq
  set zh := cD * z1 * Γ ^ 3 * ζ with hzh
  have hζ0 : 0 ≤ ζ := by
    by_contra h
    push_neg at h
    nlinarith
  have hM1 : 1 ≤ M := hΓ.trans hΓM
  have hM0 : 0 ≤ M := by linarith
  have hD0' : 0 ≤ D := by linarith
  have hΓ0 : 0 ≤ Γ := by linarith
  have hc0 : 0 ≤ c₁ := by linarith
  have hz0 : 0 ≤ z1 := by linarith
  have hzh0 : 0 ≤ zh := by positivity
  have hζzh : ζ ≤ zh := by
    have h1 : 1 ≤ cD * z1 * Γ ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hcD hz1) (one_le_pow₀ hΓ)
    calc ζ = 1 * ζ := (one_mul ζ).symm
      _ ≤ cD * z1 * Γ ^ 3 * ζ := mul_le_mul_of_nonneg_right h1 hζ0
  have hζlb : ζ ≤ lb := hζzh.trans hζl
  have hlb0 : 0 ≤ lb := hζ0.trans hζlb
  obtain ⟨S1, S2, S3, S4⟩ := FIH_S4 s g D M ζ Γ lb hs0 hs1 hg0 hgΓ hg2 hcard hD hΓ hM1 hMζ hζ1 hζlb
  -- splitting off the undifferentiated factors
  have hcardS : (Finset.univ.filter fun m => ¬ 1 ≤ c m).card = Fintype.card κ - q := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset κ))
      (p := fun m => 1 ≤ c m)
    rw [Finset.card_univ, ← hS, ← hq] at this
    omega
  have hsplit : ∀ i j, ∏ m, βD i j (c m) =
      (∏ m ∈ S, βD i j (c m)) * δ ^ (Fintype.card κ - q) := by
    intro i j
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 1 ≤ c m), ← hcardS,
      ← Finset.prod_const]
    congr 1
    refine Finset.prod_congr rfl fun m hm => ?_
    have : c m = 0 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hm
      omega
    rw [this, hD0]
  have hsumS : ∑ m ∈ S, c m = k - r := by
    have h1 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 1 ≤ c m) c
    rw [← hS] at h1
    have h2 : ∑ m ∈ Finset.univ.filter (fun m => ¬ 1 ≤ c m), c m = 0 :=
      Finset.sum_eq_zero fun m hm => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hm
        omega
    omega
  have hcle : ∀ m, c m ≤ k := fun m =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)).trans (by omega)
  have hqS : q ≤ k - r := by
    rw [← hsumS, hq, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun m hm => (Finset.mem_filter.mp hm).2
  have hP1 : ∀ i j, βD i j 1 ≤ c₁ * (z1 * Γ ^ 3 * (M * ζ)) := fun i j =>
    (hDl i j 1 le_rfl (by omega)).trans (le_of_eq (by ring))
  have hpos1 : ∀ i j, 0 ≤ c₁ * (s i * g j + s j * g i + Γ * lb) := fun i j => by
    have := hs0 i; have := hs0 j; have := hg0 i; have := hg0 j
    positivity
  have key : ∑ i, ∑ j, s i * (βG i j r * ∏ m ∈ S, βD i j (c m)) ≤
      M ^ (k + 1) * (20 * D * c₁ ^ (k + 1)) * (zh * lb ^ 2) ^ (((q + 1 : ℕ) : ℝ) / 3) := by
    by_cases hq2 : q + 2 ≤ k
    · -- at most `k - 2` differentiated factors: every derivative by its generic bound
      have hprod : ∀ i j, ∏ m ∈ S, βD i j (c m) ≤
          (c₁ * z1 * Γ ^ 2 * (M * ζ)) ^ q * Γ ^ (k - r) := by
        intro i j
        calc ∏ m ∈ S, βD i j (c m) ≤ ∏ m ∈ S, (c₁ * z1 * Γ ^ 2 * (M * ζ)) * Γ ^ c m := by
              refine Finset.prod_le_prod₀ (fun m _ => hDnn i j _) fun m hm => ?_
              calc βD i j (c m) ≤ c₁ * z1 * Γ ^ (c m + 2) * (M * ζ) :=
                    hDl i j _ (Finset.mem_filter.mp hm).2 (hcle m)
                _ = _ := by ring
          _ = _ := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, hsumS]
      have hΓk : Γ ^ k = Γ ^ r * Γ ^ (k - r) := by
        rw [← pow_add]; congr 1; omega
      have hpt : ∀ i j, s i * (βG i j r * ∏ m ∈ S, βD i j (c m)) ≤
          (c₁ ^ (q + 1) * Γ ^ k * (z1 * Γ ^ 2 * (M * ζ)) ^ q) * (s i * (g i + g j)) := by
        intro i j
        have h1 := hG i j r (by omega)
        have h2 := hprod i j
        have h3 : 0 ≤ ∏ m ∈ S, βD i j (c m) := Finset.prod_nonneg fun m _ => hDnn i j _
        have h4 : 0 ≤ c₁ * Γ ^ r * (g i + g j) := by
          have := hg0 i; have := hg0 j; positivity
        calc s i * (βG i j r * ∏ m ∈ S, βD i j (c m))
            ≤ s i * ((c₁ * Γ ^ r * (g i + g j)) * ((c₁ * z1 * Γ ^ 2 * (M * ζ)) ^ q *
                Γ ^ (k - r))) := mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 h3 h4) (hs0 i)
          _ = _ := by rw [hΓk]; ring
      obtain ⟨e, he⟩ : ∃ e, k = q + 2 + e := ⟨k - (q + 2), by omega⟩
      have hC0 : 0 ≤ c₁ ^ (q + 1) * Γ ^ k * (z1 * Γ ^ 2 * (M * ζ)) ^ q := by positivity
      calc ∑ i, ∑ j, s i * (βG i j r * ∏ m ∈ S, βD i j (c m))
          ≤ ∑ i, ∑ j, (c₁ ^ (q + 1) * Γ ^ k * (z1 * Γ ^ 2 * (M * ζ)) ^ q) * (s i * (g i + g j)) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
        _ = (c₁ ^ (q + 1) * Γ ^ k * (z1 * Γ ^ 2 * (M * ζ)) ^ q) *
              ∑ i, ∑ j, s i * (g i + g j) := by simp only [Finset.mul_sum]
        _ ≤ (c₁ ^ (q + 1) * Γ ^ k * (z1 * Γ ^ 2 * (M * ζ)) ^ q) * (2 * D * M ^ 3 * ζ) :=
            mul_le_mul_of_nonneg_left S1 hC0
        _ ≤ M ^ (k + 1) * (20 * D * c₁ ^ (k + 1)) * zh ^ (q + 1) := by
            rw [he]; exact FIH_num1 q e D M ζ Γ z1 cD c₁ hD0' hΓ hΓM hζ0 hz1 hcD hc₁
        _ = M ^ (k + 1) * (20 * D * c₁ ^ (k + 1)) * (zh ^ (q + 1) * lb ^ 0) := by ring
        _ ≤ _ := by
            gcongr
            exact FIH_norm zh lb hzh0 hζl (q + 1) 0 (q + 1) rfl (by omega)
    · -- `k - 1` or `k` differentiated factors: `r ≤ 1` and all `c_m ≤ 2`
      push_neg at hq2
      obtain ⟨t, ht⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
      have hdef : (∑ m ∈ S, (c m - 1)) + q = k - r := by
        rw [hq, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib, ← hsumS]
        refine Finset.sum_congr rfl fun m hm => ?_
        have := (Finset.mem_filter.mp hm).2
        omega
      by_cases hz : ∑ m ∈ S, (c m - 1) = 0
      · have hc1 : ∀ m ∈ S, c m = 1 := by
          intro m hm
          have := (Finset.sum_eq_zero_iff.mp hz) m hm
          have := (Finset.mem_filter.mp hm).2
          omega
        have hprod : ∀ i j, ∏ m ∈ S, βD i j (c m) = βD i j 1 ^ q := by
          intro i j
          rw [Finset.prod_congr rfl fun m hm => by rw [hc1 m hm], Finset.prod_const]
        by_cases hr : r = 0
        · -- `G_{jv}` undifferentiated, `k` factors with one derivative each
          have hqk : q = t + 2 := by omega
          have hpt : ∀ i j, s i * (βG i j r * ∏ m ∈ S, βD i j (c m)) ≤
              (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
                (s i * g j * (s i * g j + s j * g i + Γ * lb) ^ 2) := by
            intro i j
            rw [hprod, hr, hqk, pow_add]
            have h1 : βD i j 1 ^ t ≤ (c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t :=
              pow_le_pow_left₀ (hDnn i j 1) (hP1 i j) t
            have h2 : βD i j 1 ^ 2 ≤ (c₁ * (s i * g j + s j * g i + Γ * lb)) ^ 2 :=
              pow_le_pow_left₀ (hDnn i j 1) (hD1 i j) 2
            have h3 : βD i j 1 ^ t * βD i j 1 ^ 2 ≤
                (c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t * (c₁ * (s i * g j + s j * g i + Γ * lb)) ^ 2 :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
            have h4 : βG i j 0 * (βD i j 1 ^ t * βD i j 1 ^ 2) ≤ (c₁ * g j) *
                ((c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t * (c₁ * (s i * g j + s j * g i + Γ * lb)) ^ 2) :=
              mul_le_mul (hG0 i j) h3 (by have := hDnn i j 1; positivity)
                (by have := hg0 j; positivity)
            calc s i * (βG i j 0 * (βD i j 1 ^ t * βD i j 1 ^ 2)) ≤ s i * ((c₁ * g j) *
                  ((c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t *
                    (c₁ * (s i * g j + s j * g i + Γ * lb)) ^ 2)) :=
                  mul_le_mul_of_nonneg_left h4 (hs0 i)
              _ = _ := by ring
          have hC0 : 0 ≤ c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t := by positivity
          calc ∑ i, ∑ j, s i * (βG i j r * ∏ m ∈ S, βD i j (c m))
              ≤ ∑ i, ∑ j, (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
                  (s i * g j * (s i * g j + s j * g i + Γ * lb) ^ 2) :=
                Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
            _ = (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
                  ∑ i, ∑ j, s i * g j * (s i * g j + s j * g i + Γ * lb) ^ 2 := by
                simp only [Finset.mul_sum]
            _ ≤ (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
                  (9 * D * M ^ 3 * Γ ^ 2 * ζ * lb ^ 2) := mul_le_mul_of_nonneg_left S2 hC0
            _ ≤ M ^ (t + 3) * (20 * D * c₁ ^ (t + 3)) * zh ^ (t + 1) * lb ^ 2 :=
                FIH_num2 t 9 D M ζ Γ z1 cD c₁ (lb ^ 2) (by norm_num) hD0' hΓ hM0 hζ0 hz1 hcD hc₁
                  (sq_nonneg _)
            _ ≤ _ := by
                rw [ht, hqk, mul_assoc (M ^ (t + 2 + 1) * _)]
                gcongr
                exact FIH_norm zh lb hzh0 hζl (t + 1) 2 (t + 2 + 1) (by omega) (by omega)
        · -- `G_{jv}` differentiated once, `k - 1` factors with one derivative each
          have hr1 : r = 1 := by omega
          have hqk : q = t + 1 := by omega
          have hpt : ∀ i j, s i * (βG i j r * ∏ m ∈ S, βD i j (c m)) ≤
              (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
                (Γ * (s i * (g i + g j) * (s i * g j + s j * g i + Γ * lb))) := by
            intro i j
            rw [hprod, hr1, hqk, pow_succ]
            have h1 : βD i j 1 ^ t ≤ (c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t :=
              pow_le_pow_left₀ (hDnn i j 1) (hP1 i j) t
            have h3 : βD i j 1 ^ t * βD i j 1 ≤
                (c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t * (c₁ * (s i * g j + s j * g i + Γ * lb)) :=
              mul_le_mul h1 (hD1 i j) (hDnn i j 1) (by positivity)
            have h4 : βG i j 1 * (βD i j 1 ^ t * βD i j 1) ≤ (c₁ * Γ ^ 1 * (g i + g j)) *
                ((c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t * (c₁ * (s i * g j + s j * g i + Γ * lb))) :=
              mul_le_mul (hG i j 1 (by omega)) h3 (by have := hDnn i j 1; positivity)
                (by have := hg0 i; have := hg0 j; positivity)
            have hc3 : c₁ ^ 2 ≤ c₁ ^ 3 := pow_le_pow_right₀ hc₁ (by norm_num)
            have hA : 0 ≤ (z1 * Γ ^ 3 * (M * ζ)) ^ t *
                (Γ * (s i * (g i + g j) * (s i * g j + s j * g i + Γ * lb))) := by
              have := hs0 i; have := hs0 j; have := hg0 i; have := hg0 j; positivity
            calc s i * (βG i j 1 * (βD i j 1 ^ t * βD i j 1)) ≤ s i * ((c₁ * Γ ^ 1 * (g i + g j)) *
                  ((c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t *
                    (c₁ * (s i * g j + s j * g i + Γ * lb)))) :=
                  mul_le_mul_of_nonneg_left h4 (hs0 i)
              _ = c₁ ^ t * c₁ ^ 2 * ((z1 * Γ ^ 3 * (M * ζ)) ^ t *
                    (Γ * (s i * (g i + g j) * (s i * g j + s j * g i + Γ * lb)))) := by ring
              _ ≤ c₁ ^ t * c₁ ^ 3 * ((z1 * Γ ^ 3 * (M * ζ)) ^ t *
                    (Γ * (s i * (g i + g j) * (s i * g j + s j * g i + Γ * lb)))) := by
                  gcongr
              _ = _ := by ring
          have hC0 : 0 ≤ c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t := by positivity
          calc ∑ i, ∑ j, s i * (βG i j r * ∏ m ∈ S, βD i j (c m))
              ≤ ∑ i, ∑ j, (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
                  (Γ * (s i * (g i + g j) * (s i * g j + s j * g i + Γ * lb))) :=
                Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
            _ = (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
                  (Γ * ∑ i, ∑ j, s i * (g i + g j) * (s i * g j + s j * g i + Γ * lb)) := by
                simp only [Finset.mul_sum]
            _ ≤ (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
                  (6 * D * M ^ 3 * Γ ^ 2 * ζ * lb) := by
                refine mul_le_mul_of_nonneg_left ?_ hC0
                calc Γ * ∑ i, ∑ j, s i * (g i + g j) * (s i * g j + s j * g i + Γ * lb)
                    ≤ Γ * (6 * D * M ^ 3 * Γ * ζ * lb) := mul_le_mul_of_nonneg_left S3 hΓ0
                  _ = _ := by ring
            _ ≤ M ^ (t + 3) * (20 * D * c₁ ^ (t + 3)) * zh ^ (t + 1) * lb :=
                FIH_num2 t 6 D M ζ Γ z1 cD c₁ lb (by norm_num) hD0' hΓ hM0 hζ0 hz1 hcD hc₁ hlb0
            _ ≤ _ := by
                rw [ht, hqk, mul_assoc (M ^ (t + 2 + 1) * _)]
                have e1 : zh ^ (t + 1) * lb = zh ^ (t + 1) * lb ^ 1 := by ring
                rw [e1]
                gcongr
                exact FIH_norm zh lb hzh0 hζl (t + 1) 1 (t + 1 + 1) (by omega) (by omega)
      · -- `G_{jv}` undifferentiated, one factor with two derivatives
        have hr : r = 0 := by omega
        have hqk : q = t + 1 := by omega
        have hone : ∑ m ∈ S, (c m - 1) = 1 := by omega
        obtain ⟨m₀, hm₀, hm₀'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
        have hrest := Finset.add_sum_erase S (fun m => c m - 1) hm₀
        rw [hone] at hrest
        have hrest0 : ∑ m ∈ S.erase m₀, (c m - 1) = 0 := by omega
        have hcm₀ : c m₀ = 2 := by
          have := (Finset.mem_filter.mp hm₀).2
          omega
        have hc1 : ∀ m ∈ S.erase m₀, c m = 1 := by
          intro m hm
          have := (Finset.sum_eq_zero_iff.mp hrest0) m hm
          have := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hm)).2
          omega
        have hcardE : (S.erase m₀).card = t := by
          rw [Finset.card_erase_of_mem hm₀]; omega
        have hprod : ∀ i j, ∏ m ∈ S, βD i j (c m) = βD i j 2 * βD i j 1 ^ t := by
          intro i j
          rw [← Finset.mul_prod_erase S _ hm₀, hcm₀,
            Finset.prod_congr rfl fun m hm => by rw [hc1 m hm], Finset.prod_const, hcardE]
        have hpt : ∀ i j, s i * (βG i j r * ∏ m ∈ S, βD i j (c m)) ≤
            (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
              (s i * g j * (Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) +
                Γ ^ 2 * ζ ^ 2)) := by
          intro i j
          rw [hprod, hr]
          have h1 : βD i j 1 ^ t ≤ (c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t :=
            pow_le_pow_left₀ (hDnn i j 1) (hP1 i j) t
          have hd2 : 0 ≤ Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) + Γ ^ 2 * ζ ^ 2 := by
            have := hs0 i; have := hs0 j; have := hg0 i; have := hg0 j; positivity
          have h3 : βD i j 2 * βD i j 1 ^ t ≤ (c₁ * (Γ * (s i + s j) * (g i + g j) +
              lb * Γ * (g i + g j) + Γ ^ 2 * ζ ^ 2)) * (c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t :=
            mul_le_mul (hD2 i j) h1 (by have := hDnn i j 1; positivity) (by positivity)
          have h4 : βG i j 0 * (βD i j 2 * βD i j 1 ^ t) ≤ (c₁ * g j) *
              ((c₁ * (Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) + Γ ^ 2 * ζ ^ 2)) *
                (c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t) :=
            mul_le_mul (hG0 i j) h3 (by have := hDnn i j 1; have := hDnn i j 2; positivity)
              (by have := hg0 j; positivity)
          have hc3 : c₁ ^ 2 ≤ c₁ ^ 3 := pow_le_pow_right₀ hc₁ (by norm_num)
          have hA : 0 ≤ (z1 * Γ ^ 3 * (M * ζ)) ^ t * (s i * g j * (Γ * (s i + s j) * (g i + g j) +
              lb * Γ * (g i + g j) + Γ ^ 2 * ζ ^ 2)) := by
            have := hs0 i; have := hg0 j; positivity
          calc s i * (βG i j 0 * (βD i j 2 * βD i j 1 ^ t)) ≤ s i * ((c₁ * g j) *
                ((c₁ * (Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) + Γ ^ 2 * ζ ^ 2)) *
                  (c₁ * (z1 * Γ ^ 3 * (M * ζ))) ^ t)) := mul_le_mul_of_nonneg_left h4 (hs0 i)
            _ = c₁ ^ t * c₁ ^ 2 * ((z1 * Γ ^ 3 * (M * ζ)) ^ t * (s i * g j *
                  (Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) + Γ ^ 2 * ζ ^ 2))) := by
                ring
            _ ≤ c₁ ^ t * c₁ ^ 3 * ((z1 * Γ ^ 3 * (M * ζ)) ^ t * (s i * g j *
                  (Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) + Γ ^ 2 * ζ ^ 2))) := by
                gcongr
            _ = _ := by ring
        have hC0 : 0 ≤ c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t := by positivity
        calc ∑ i, ∑ j, s i * (βG i j r * ∏ m ∈ S, βD i j (c m))
            ≤ ∑ i, ∑ j, (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
                (s i * g j * (Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) +
                  Γ ^ 2 * ζ ^ 2)) :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
          _ = (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
                ∑ i, ∑ j, s i * g j * (Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) +
                  Γ ^ 2 * ζ ^ 2) := by
              simp only [Finset.mul_sum]
          _ ≤ (c₁ ^ (t + 3) * (z1 * Γ ^ 3 * (M * ζ)) ^ t) *
                (8 * D * M ^ 3 * Γ ^ 2 * ζ * lb) := mul_le_mul_of_nonneg_left S4 hC0
          _ ≤ M ^ (t + 3) * (20 * D * c₁ ^ (t + 3)) * zh ^ (t + 1) * lb :=
              FIH_num2 t 8 D M ζ Γ z1 cD c₁ lb (by norm_num) hD0' hΓ hM0 hζ0 hz1 hcD hc₁ hlb0
          _ ≤ _ := by
              rw [ht, hqk, mul_assoc (M ^ (t + 2 + 1) * _)]
              have e1 : zh ^ (t + 1) * lb = zh ^ (t + 1) * lb ^ 1 := by ring
              rw [e1]
              gcongr
              exact FIH_norm zh lb hzh0 hζl (t + 1) 1 (t + 1 + 1) (by omega) (by omega)
  calc ∑ i, ∑ j, s i * (βG i j r * ∏ m, βD i j (c m))
      = (∑ i, ∑ j, s i * (βG i j r * ∏ m ∈ S, βD i j (c m))) * δ ^ (Fintype.card κ - q) := by
        simp only [hsplit, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right key (pow_nonneg hδ _)

/-- The bound off the good event of one Leibniz word: every factor by its bound for `‖G‖ ≤ Y`. -/
private lemma FIH_word_bad {κ : Type*} [Fintype κ] (βG βD : ℕ → ℝ) (A Z Y : ℝ) (r : ℕ)
    (c : κ → ℕ) (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hY : 0 ≤ Y) (hGnn : 0 ≤ βG r)
    (hG : βG r ≤ A * Y ^ (r + 1)) (hDnn : ∀ l, 0 ≤ βD l)
    (hD : ∀ m, βD (c m) ≤ A * Z * Y ^ (c m + 3)) :
    βG r * ∏ m, βD (c m) ≤
      A ^ (Fintype.card κ + 1) * Z ^ Fintype.card κ *
        Y ^ (r + (∑ m, c m) + 1 + 3 * Fintype.card κ) := by
  have h1 : ∏ m, βD (c m) ≤ ∏ m, (A * Z * Y ^ 3) * Y ^ c m :=
    Finset.prod_le_prod₀ (fun m _ => hDnn _) fun m _ => (hD m).trans (le_of_eq (by ring))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
    Finset.card_univ] at h1
  calc βG r * ∏ m, βD (c m)
      ≤ (A * Y ^ (r + 1)) * ((A * Z * Y ^ 3) ^ Fintype.card κ * Y ^ ∑ m, c m) :=
        mul_le_mul hG h1 (Finset.prod_nonneg fun m _ => hDnn _) (by positivity)
    _ = _ := by ring

/-! ### The Leibniz expansion of the order-`k` integrand -/

/-- `(G v)_j` along the slice `w ↦ setEntry h j i w`. -/
private def FIH_Gs (D N : ℕ) (h : Idx D N → Idx D N → ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (v : Idx D N → ℂ) (j i : Idx D N) : ℂ → ℂ :=
  fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j

/-- `(H̲G)_{uv}` along the slice `w ↦ setEntry h j i w`. -/
private def FIH_Hs (D N : ℕ) (θ : ℝ) (h : Idx D N → Idx D N → ℂ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (u v : Idx D N → ℂ) (j i : Idx D N) : ℂ → ℂ :=
  fun w => star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)

/-- The sum over `α + β = l` of `|∂_w^α ∂_{w̄}^β F(w)|`. -/
private def FIH_bnd (F : ℂ → ℂ) (w : ℂ) (l : ℕ) : ℝ :=
  ∑ α ∈ Finset.range (l + 1), ‖wirt α (l - α) F w‖

private lemma FIH_bnd_nonneg (F : ℂ → ℂ) (w : ℂ) (l : ℕ) : 0 ≤ FIH_bnd F w l :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

private lemma FIH_le_bnd (F : ℂ → ℂ) (w : ℂ) (α β : ℕ) :
    ‖wirt α β F w‖ ≤ FIH_bnd F w (α + β) := by
  have h := Finset.single_le_sum (f := fun α' => ‖wirt α' (α + β - α') F w‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_add_right α β)))
  simp only [Nat.add_sub_cancel_left] at h
  exact h

private lemma FIH_bnd_zero (F : ℂ → ℂ) (w : ℂ) : FIH_bnd F w 0 = ‖F w‖ := by
  simp [FIH_bnd, wirt]

private lemma FIH_bnd_le (F : ℂ → ℂ) (w : ℂ) (l : ℕ) (B : ℝ)
    (hB : ∀ α ≤ l, ‖wirt α (l - α) F w‖ ≤ B) : FIH_bnd F w l ≤ (l + 1) * B := by
  calc FIH_bnd F w l ≤ ∑ _α ∈ Finset.range (l + 1), B :=
        Finset.sum_le_sum fun α hα => hB α (Nat.lt_succ_iff.mp (Finset.mem_range.mp hα))
    _ = _ := by simp

private lemma FIH_cnt_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (σ : Fin n → ι) :
    ∑ m, FIH_cnt σ m = n := by
  simp only [FIH_cnt]
  rw [Finset.sum_comm]
  simp

/-- The Leibniz rule for the integrand of `isoTerm`: `|∂_w^a ∂_{w̄}^b (G_{jv} 𝒟^{p-1} 𝒟̄^p)|` is at
most the sum over pairs of words of the product of the bounds of the factors, each by the total
number of derivatives it receives. -/
private lemma FIH_leib (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (u v : Idx D N → ℂ) (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1) (p : ℕ) (j i : Idx D N)
    (a b : ℕ) (w : ℂ) :
    ‖wirt a b (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
        w‖ ≤
      ∑ σ : Fin b → Option (Fin (p - 1) ⊕ Fin p), ∑ τ : Fin a → Option (Fin (p - 1) ⊕ Fin p),
        FIH_bnd (FIH_Gs D N h Λ z v j i) w (FIH_cnt τ none + FIH_cnt σ none) *
          ∏ m : Fin (p - 1) ⊕ Fin p,
            FIH_bnd (FIH_Hs D N θ h Λ z u v j i) w (FIH_cnt τ (some m) + FIH_cnt σ (some m)) := by
  classical
  set Gs := FIH_Gs D N h Λ z v j i with hGs
  set Hs := FIH_Hs D N θ h Λ z u v j i with hHs
  let F : Option (Fin (p - 1) ⊕ Fin p) → ℂ → ℂ := fun m =>
    Option.elim m Gs (Sum.elim (fun _ => Hs) (fun _ => fun w => starRingEnd ℂ (Hs w)))
  have hGsm : ContDiff ℝ ∞ Gs := by
    have e : Gs = FIH_fF h Λ z j i (Pi.single j 1) v := by
      funext w
      simp only [hGs, FIH_Gs, FIH_fF, FIH_dot_single]
    rw [e]
    exact FIH_fF_smooth h hh Λ hΛ z hz.ne' j i _ v
  have hHsm : ContDiff ℝ ∞ Hs := FIH_hg_smooth θ hθ0 hθ1 h hh Λ hΛ z hz j i u v hu hv
  have hF : ∀ m, ContDiff ℝ ∞ (F m) := by
    intro m
    rcases m with _ | m | m
    · exact hGsm
    · exact hHsm
    · exact Complex.conjCLE.contDiff.comp hHsm
  have hf : (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
      (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
      starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p) =
      fun w => ∏ m, F m w := by
    funext w
    rw [Fintype.prod_option, Fintype.prod_sum_type]
    simp only [F, Option.elim, Sum.elim_inl, Sum.elim_inr, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hGs, hHs, FIH_Gs, FIH_Hs]
    ring
  rw [hf, FIH_wirt_prod F hF a b w]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun τ _ => ?_))
  rw [norm_prod, Fintype.prod_option]
  refine mul_le_mul ?_ (Finset.prod_le_prod₀ (fun m _ => norm_nonneg _) fun m _ => ?_)
    (Finset.prod_nonneg fun m _ => norm_nonneg _) (FIH_bnd_nonneg _ _ _)
  · exact FIH_le_bnd _ _ _ _
  · rcases m with m | m
    · exact FIH_le_bnd _ _ _ _
    · show ‖wirt _ _ (fun w => starRingEnd ℂ (Hs w)) w‖ ≤ _
      rw [FIH_wirt_conj _ _ hHsm, Complex.norm_conj, add_comm]
      exact FIH_le_bnd _ _ _ _

/-! ### The bounds of the factors on the good event -/

private lemma FIH_iv_u (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (u v : Idx D N → ℂ) :
    u ∈ isoVecs D N θ Λ u v := by simp [isoVecs]

private lemma FIH_iv_v (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (u v : Idx D N → ℂ) :
    v ∈ isoVecs D N θ Λ u v := by simp [isoVecs]

private lemma FIH_iv_e (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (u v : Idx D N → ℂ)
    (k : Idx D N) : Pi.single k 1 ∈ isoVecs D N θ Λ u v := by
  simp only [isoVecs, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ k))))

private lemma FIH_iv_t (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (u v : Idx D N → ℂ)
    (r : Idx D N) : tiltV D N θ u r ∈ isoVecs D N θ Λ u v := by
  simp only [isoVecs, Finset.mem_union]
  exact Or.inl (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ r)))

private lemma FIH_good_entry {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (V : Finset (Idx D N → ℂ)) (Γ Υ : ℝ) (h : Idx D N → Idx D N → ℂ) (hg : h ∈ goodSet Λ z V Γ Υ)
    (hV : ∀ k, Pi.single k 1 ∈ V) (a b : Idx D N) :
    ‖res (Matrix.of h + Λ) z a b‖ ≤ Γ ∧ (res (Matrix.of h + Λ) z a a).im ≤ Υ := by
  have h1 := hg _ (hV a) _ (hV b)
  have h2 := hg _ (hV a) _ (hV a)
  rw [FIH_entry] at h1 h2
  exact ⟨h1.1, h2.2⟩

private lemma FIH_good_gv {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (V : Finset (Idx D N → ℂ)) (Γ Υ : ℝ) (h : Idx D N → Idx D N → ℂ) (hg : h ∈ goodSet Λ z V Γ Υ)
    (hV : ∀ k, Pi.single k 1 ∈ V) (v : Idx D N → ℂ) (hv : v ∈ V) (a : Idx D N) :
    ‖(res (Matrix.of h + Λ) z *ᵥ v) a‖ ≤ Γ := by
  have := (hg _ (hV a) _ hv).1
  rwa [FIH_dot_single] at this

/-- The derivatives of `G_{jv}` on the good event: `Σ_{α+β=l} |∂^α ∂̄^β G_{jv}| ≤
(l+1)^{l+1} Γ^l (|G_{iv}| + |G_{jv}|)`, and `G_{jv}` itself at `l = 0`. -/
private lemma FIH_good_G (D N : ℕ) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (V : Finset (Idx D N → ℂ)) (v : Idx D N → ℂ) (hvV : v ∈ V) (hV : ∀ k, Pi.single k 1 ∈ V)
    (Γ Υ : ℝ) (hΓ : 1 ≤ Γ) (hg : h ∈ goodSet Λ z V Γ Υ) (i j : Idx D N) :
    FIH_bnd (FIH_Gs D N h Λ z v j i) (h j i) 0 = ‖(res (Matrix.of h + Λ) z *ᵥ v) j‖ ∧
    ∀ l, FIH_bnd (FIH_Gs D N h Λ z v j i) (h j i) l ≤ ((l + 1 : ℕ) : ℝ) ^ (l + 1) * Γ ^ l *
      (‖(res (Matrix.of h + Λ) z *ᵥ v) i‖ + ‖(res (Matrix.of h + Λ) z *ᵥ v) j‖) := by
  have hse := FIH_setEntry_self h hh j i
  set G := res (Matrix.of h + Λ) z with hG
  refine ⟨by rw [FIH_bnd_zero, FIH_Gs, hse], fun l => ?_⟩
  set om := max ‖(G *ᵥ v) i‖ ‖(G *ᵥ v) j‖ with hom
  have hω0 : 0 ≤ om := (norm_nonneg _).trans (le_max_left _ _)
  have hωΓ : om ≤ Γ := max_le (FIH_good_gv Λ z V Γ Υ h hg hV v hvV i)
    (FIH_good_gv Λ z V Γ Υ h hg hV v hvV j)
  have hω2 : om ≤ ‖(G *ᵥ v) i‖ + ‖(G *ᵥ v) j‖ :=
    max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hE : ∀ a ∈ ({j, i} : Set (Idx D N)), ∀ b ∈ ({j, i} : Set (Idx D N)),
      ‖res (Matrix.of (setEntry h j i (h j i)) + Λ) z a b‖ ≤ Γ := by
    intro a _ b _
    rw [hse]
    exact (FIH_good_entry Λ z V Γ Υ h hg hV a b).1
  have hy : ∀ a ∈ ({j, i} : Set (Idx D N)),
      ‖(res (Matrix.of (setEntry h j i (h j i)) + Λ) z *ᵥ v) a‖ ≤ om := by
    intro a ha
    rw [hse]
    rcases ha with rfl | ha
    · exact le_max_right _ _
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact le_max_left _ _
  have hB := FIH_bnd_le (FIH_Gs D N h Λ z v j i) (h j i) l
    (((1 + l : ℕ) : ℝ) ^ l * (om * Γ ^ l)) fun α hα => by
      have := FIH_B0 h hh Λ hΛ z hz.ne' j i v Γ om hΓ hω0 hωΓ (h j i) hE hy α (l - α)
      have e : α + (l - α) = l := by omega
      have e2 : 1 + α + (l - α) = 1 + l := by omega
      rw [e2, e] at this
      exact this
  have hΓ0 : 0 ≤ Γ := by linarith
  calc FIH_bnd (FIH_Gs D N h Λ z v j i) (h j i) l
      ≤ (l + 1) * (((1 + l : ℕ) : ℝ) ^ l * (om * Γ ^ l)) := hB
    _ = ((l + 1 : ℕ) : ℝ) ^ (l + 1) * Γ ^ l * om := by
        rw [show (1 + l : ℕ) = l + 1 by omega]; push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hω2 (by positivity)

/-- The first derivatives of `(H̲G)_{uv}` on the good event:
`|∂_w 𝒟| + |∂_{w̄} 𝒟| ≤ 4 (|u_i| |G_{jv}| + |u_j| |G_{iv}| + Γ λ)`. -/
private lemma FIH_good_D1 (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (u v : Idx D N → ℂ) (Γ Υ lb : ℝ) (hΓ : 1 ≤ Γ) (hZ : Υ / ((N : ℝ) * z.im) ≤ lb)
    (hgood : h ∈ isoGood D N θ Λ z u v Γ Υ lb) (i j : Idx D N) :
    FIH_bnd (FIH_Hs D N θ h Λ z u v j i) (h j i) 1 ≤
      4 * (‖u i‖ * ‖(res (Matrix.of h + Λ) z *ᵥ v) j‖ +
        ‖u j‖ * ‖(res (Matrix.of h + Λ) z *ᵥ v) i‖ + Γ * lb) := by
  have hse := FIH_setEntry_self h hh j i
  set G := res (Matrix.of h + Λ) z with hG
  have hg := hgood.1
  have hV := FIH_iv_e D N θ Λ u v
  have hΓ0 : 0 ≤ Γ := by linarith
  have hHΛ : (Matrix.of h + Λ).IsHermitian := hh.add hΛ
  have hR : ∀ a b, ‖hgDer D N θ (Matrix.of h) Λ z u v a b‖ ≤
      ‖u a‖ * ‖(G *ᵥ v) b‖ + lb * ‖(G *ᵥ v) b‖ + Γ * (Υ / ((N : ℝ) * z.im)) := by
    intro a b
    refine FIH_R1 θ (Matrix.of h) Λ z u v a b Γ lb _ hΓ0 ?_ ?_ ?_
    · exact hgood.2 _ (Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ a))))
    · exact fun r => (hg _ (FIH_iv_t D N θ Λ u v r) _ (FIH_iv_v D N θ Λ u v)).1
    · exact FIH_W2 _ hHΛ z hz a b N Υ (Nat.cast_nonneg N)
        (FIH_good_entry Λ z _ Γ Υ h hg hV a a).2 (FIH_good_entry Λ z _ Γ Υ h hg hV b b).2
  have hlb0 : 0 ≤ lb := by
    have := hgood.2 v (Finset.mem_insert_self _ _)
    exact (norm_nonneg _).trans this
  have hgΓ : ∀ a, ‖(G *ᵥ v) a‖ ≤ Γ := FIH_good_gv Λ z _ Γ Υ h hg hV v (FIH_iv_v D N θ Λ u v)
  have hc : ‖(if j = i then (1 / 2 : ℂ) else 1)‖ ≤ 1 := by
    split_ifs
    · norm_num
    · simp
  obtain ⟨d1, d2⟩ := hgUnder_dW D N θ Λ hΛ z hz h hh j i u v (h j i)
  have e : FIH_bnd (FIH_Hs D N θ h Λ z u v j i) (h j i) 1 =
      ‖dWbar (FIH_Hs D N θ h Λ z u v j i) (h j i)‖ +
        ‖dW (FIH_Hs D N θ h Λ z u v j i) (h j i)‖ := by
    simp [FIH_bnd, Finset.sum_range_succ, wirt]
  have d1' : dW (FIH_Hs D N θ h Λ z u v j i) (h j i) = (if j = i then 1 / 2 else 1) *
      hgDer D N θ (Matrix.of (setEntry h j i (h j i))) Λ z u v j i := d1
  have d2' : dWbar (FIH_Hs D N θ h Λ z u v j i) (h j i) = (if j = i then 1 / 2 else 1) *
      hgDer D N θ (Matrix.of (setEntry h j i (h j i))) Λ z u v i j := d2
  rw [e, d1', d2', hse, norm_mul, norm_mul]
  have hZ0 : 0 ≤ Υ / ((N : ℝ) * z.im) := by
    have := (FIH_good_entry Λ z _ Γ Υ h hg hV i i).2
    have h0 : 0 ≤ (G i i).im := by
      have := (ward_diag _ hHΛ z hz i).1
      have h1 : 0 ≤ (∑ x, ‖res (Matrix.of h + Λ) z x i‖ ^ 2) := by positivity
      rw [this] at h1
      exact (div_nonneg_iff.mp h1).elim (fun h => h.1) fun h => absurd hz (not_lt.mpr h.2)
    have : 0 ≤ Υ := h0.trans this
    positivity
  have b1 := hR i j
  have b2 := hR j i
  have hn1 := norm_nonneg (hgDer D N θ (Matrix.of h) Λ z u v i j)
  have hn2 := norm_nonneg (hgDer D N θ (Matrix.of h) Λ z u v j i)
  have hc0 := norm_nonneg (if j = i then (1 / 2 : ℂ) else 1)
  have k1 : ‖(if j = i then (1 / 2 : ℂ) else 1)‖ * ‖hgDer D N θ (Matrix.of h) Λ z u v i j‖ ≤
      ‖hgDer D N θ (Matrix.of h) Λ z u v i j‖ := mul_le_of_le_one_left hn1 hc
  have k2 : ‖(if j = i then (1 / 2 : ℂ) else 1)‖ * ‖hgDer D N θ (Matrix.of h) Λ z u v j i‖ ≤
      ‖hgDer D N θ (Matrix.of h) Λ z u v j i‖ := mul_le_of_le_one_left hn2 hc
  have l1 : lb * ‖(G *ᵥ v) j‖ ≤ lb * Γ := mul_le_mul_of_nonneg_left (hgΓ j) hlb0
  have l2 : lb * ‖(G *ᵥ v) i‖ ≤ lb * Γ := mul_le_mul_of_nonneg_left (hgΓ i) hlb0
  have l3 : Γ * (Υ / ((N : ℝ) * z.im)) ≤ Γ * lb := mul_le_mul_of_nonneg_left hZ hΓ0
  have q1 := mul_nonneg (norm_nonneg (u i)) (norm_nonneg ((G *ᵥ v) j))
  have q2 := mul_nonneg (norm_nonneg (u j)) (norm_nonneg ((G *ᵥ v) i))
  have q3 := mul_nonneg hΓ0 hlb0
  linarith

private lemma FIH_d2_num (sa sσ gb gτ S Gs Γ lb Z : ℝ) (hsa : 0 ≤ sa) (hsσ : 0 ≤ sσ)
    (hgb : 0 ≤ gb) (hgτ : 0 ≤ gτ) (hsaS : sa ≤ S) (hsσS : sσ ≤ S) (hgbG : gb ≤ Gs)
    (hgτG : gτ ≤ Gs) (hΓ : 0 ≤ Γ) (hlb : 0 ≤ lb) (hZ0 : 0 ≤ Z) (hZ : Z ≤ lb) :
    sa * Γ * gτ + (sσ * Γ + lb * Γ + Γ * Z) * gb + lb * Γ * gτ + (2 * Γ ^ 2 * Z + Γ * Z * gτ) ≤
      4 * (Γ * S * Gs + lb * Γ * Gs + Γ ^ 2 * Z) := by
  have hS : 0 ≤ S := hsa.trans hsaS
  have hG : 0 ≤ Gs := hgb.trans hgbG
  have t1 := mul_le_mul_of_nonneg_left (FIH_mm hsa hgτ hsaS hgτG) hΓ
  have t2 := mul_le_mul_of_nonneg_left (FIH_mm hsσ hgb hsσS hgbG) hΓ
  have t3 := mul_le_mul_of_nonneg_left hgbG (mul_nonneg hlb hΓ)
  have t4 := mul_le_mul_of_nonneg_left hgτG (mul_nonneg hlb hΓ)
  have t5 := mul_le_mul_of_nonneg_left (FIH_mm hZ0 hgb hZ hgbG) hΓ
  have t6 := mul_le_mul_of_nonneg_left (FIH_mm hZ0 hgτ hZ hgτG) hΓ
  have t7 : 0 ≤ Γ * S * Gs := by positivity
  have t8 : 0 ≤ Γ ^ 2 * Z := by positivity
  nlinarith

/-- The second derivatives of `(H̲G)_{uv}` on the good event: `Σ_{α+β=2} |∂^α ∂̄^β 𝒟| ≤
12 (Γ (|u_i| + |u_j|)(|G_{iv}| + |G_{jv}|) + λ Γ (|G_{iv}| + |G_{jv}|) + Γ² Υ/(Nη))`. -/
private lemma FIH_good_D2 (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (u v : Idx D N → ℂ) (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1)
    (Γ Υ lb : ℝ) (hΓ : 1 ≤ Γ) (hZ0 : 0 ≤ Υ / ((N : ℝ) * z.im)) (hZ : Υ / ((N : ℝ) * z.im) ≤ lb)
    (hgood : h ∈ isoGood D N θ Λ z u v Γ Υ lb) (i j : Idx D N) :
    FIH_bnd (FIH_Hs D N θ h Λ z u v j i) (h j i) 2 ≤
      12 * (Γ * (‖u i‖ + ‖u j‖) * (‖(res (Matrix.of h + Λ) z *ᵥ v) i‖ +
        ‖(res (Matrix.of h + Λ) z *ᵥ v) j‖) + lb * Γ * (‖(res (Matrix.of h + Λ) z *ᵥ v) i‖ +
        ‖(res (Matrix.of h + Λ) z *ᵥ v) j‖) + Γ ^ 2 * (Υ / ((N : ℝ) * z.im))) := by
  have hse := FIH_setEntry_self h hh j i
  set G := res (Matrix.of h + Λ) z with hG
  set Z := Υ / ((N : ℝ) * z.im) with hZdef
  set w₀ := h j i with hw₀
  have hg := hgood.1
  have hV := FIH_iv_e D N θ Λ u v
  have hΓ0 : 0 ≤ Γ := by linarith
  have hHΛ : (Matrix.of h + Λ).IsHermitian := hh.add hΛ
  have hlb0 : 0 ≤ lb := hZ0.trans hZ
  set Hs := FIH_Hs D N θ h Λ z u v j i with hHs
  have hHsm : ContDiff ℝ ∞ Hs := FIH_hg_smooth θ hθ0 hθ1 h hh Λ hΛ z hz j i u v hu hv
  set cc : ℂ := if j = i then 1 / 2 else 1 with hcc
  have hcc1 : ‖cc‖ ≤ 1 := by
    rw [hcc]; split_ifs
    · norm_num
    · simp
  have hcc0 : cc ≠ 0 := by
    rw [hcc]; split_ifs <;> norm_num
  have hdW : dW Hs = fun w => cc * hgDer D N θ (Matrix.of (setEntry h j i w)) Λ z u v j i :=
    funext fun w => (hgUnder_dW D N θ Λ hΛ z hz h hh j i u v w).1
  have hdWb : dWbar Hs = fun w => cc * hgDer D N θ (Matrix.of (setEntry h j i w)) Λ z u v i j :=
    funext fun w => (hgUnder_dW D N θ Λ hΛ z hz h hh j i u v w).2
  have hX1 : DifferentiableAt ℝ
      (fun w => hgDer D N θ (Matrix.of (setEntry h j i w)) Λ z u v j i) w₀ := by
    have e : (fun w => hgDer D N θ (Matrix.of (setEntry h j i w)) Λ z u v j i) =
        fun w => cc⁻¹ * dW Hs w := by
      funext w; rw [hdW]; field_simp
    rw [e]
    exact (differentiableAt_const _).fun_mul (FIH_diff (FIH_dW_smooth hHsm) w₀)
  have hX2 : DifferentiableAt ℝ
      (fun w => hgDer D N θ (Matrix.of (setEntry h j i w)) Λ z u v i j) w₀ := by
    have e : (fun w => hgDer D N θ (Matrix.of (setEntry h j i w)) Λ z u v i j) =
        fun w => cc⁻¹ * dWbar Hs w := by
      funext w; rw [hdWb]; field_simp
    rw [e]
    exact (differentiableAt_const _).fun_mul (FIH_diff (FIH_dWbar_smooth hHsm) w₀)
  -- the hypotheses of `FIH_R2` at `w₀`, where the slice is `h` itself
  have hGb : ∀ k l, ‖res (Matrix.of (setEntry h j i w₀) + Λ) z k l‖ ≤ Γ := by
    intro k l; rw [hse]; exact (FIH_good_entry Λ z _ Γ Υ h hg hV k l).1
  have hTy : ∀ r, ‖star (tiltV D N θ u r) ⬝ᵥ (res (Matrix.of (setEntry h j i w₀) + Λ) z *ᵥ v)‖ ≤
      Γ := by
    intro r; rw [hse]; exact (hg _ (FIH_iv_t D N θ Λ u v r) _ (FIH_iv_v D N θ Λ u v)).1
  have hTe : ∀ r k, ‖star (tiltV D N θ u r) ⬝ᵥ
      (res (Matrix.of (setEntry h j i w₀) + Λ) z *ᵥ Pi.single k 1)‖ ≤ Γ := by
    intro r k; rw [hse]; exact (hg _ (FIH_iv_t D N θ Λ u v r) _ (hV k)).1
  have hDl : ∀ k, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w₀)) Λ z *ᵥ
      Pi.single k 1)‖ ≤ lb := by
    intro k; rw [hse]
    exact hgood.2 _ (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ k))))
  have hW : ∀ k l, (N : ℝ)⁻¹ * ∑ r, ‖res (Matrix.of (setEntry h j i w₀) + Λ) z r k‖ *
      ‖res (Matrix.of (setEntry h j i w₀) + Λ) z l r‖ ≤ Z := by
    intro k l; rw [hse]
    exact FIH_W2 _ hHΛ z hz k l N Υ (Nat.cast_nonneg N)
      (FIH_good_entry Λ z _ Γ Υ h hg hV k k).2 (FIH_good_entry Λ z _ Γ Υ h hg hV l l).2
  have hFm : ∀ x y', FIH_op (-Complex.I) (FIH_fF h Λ z j i x y') = fun w =>
      -cc * (FIH_fF h Λ z j i x (Pi.single j 1) w * FIH_fF h Λ z j i (Pi.single i 1) y' w) := by
    intro x y'; rw [← FIH_dW_eq]; exact (FIH_form_d h hh Λ hΛ z hz.ne' j i x y').1
  have hFp : ∀ x y', FIH_op Complex.I (FIH_fF h Λ z j i x y') = fun w =>
      -cc * (FIH_fF h Λ z j i x (Pi.single i 1) w * FIH_fF h Λ z j i (Pi.single j 1) y' w) := by
    intro x y'; rw [← FIH_dWbar_eq]; exact (FIH_form_d h hh Λ hΛ z hz.ne' j i x y').2
  have hHm : ∀ a, FIH_op (-Complex.I) (fun w => star u ⬝ᵥ (hgUnder D N θ
      (Matrix.of (setEntry h j i w)) Λ z *ᵥ Pi.single a 1)) = fun w =>
        cc * hgDer D N θ (Matrix.of (setEntry h j i w)) Λ z u (Pi.single a 1) j i := by
    intro a; rw [← FIH_dW_eq]; funext w
    exact (hgUnder_dW D N θ Λ hΛ z hz h hh j i u (Pi.single a 1) w).1
  have hHp : ∀ a, FIH_op Complex.I (fun w => star u ⬝ᵥ (hgUnder D N θ
      (Matrix.of (setEntry h j i w)) Λ z *ᵥ Pi.single a 1)) = fun w =>
        cc * hgDer D N θ (Matrix.of (setEntry h j i w)) Λ z u (Pi.single a 1) i j := by
    intro a; rw [← FIH_dWbar_eq]; funext w
    exact (hgUnder_dW D N θ Λ hΛ z hz h hh j i u (Pi.single a 1) w).2
  -- the numerical bound for indices in `{i, j}`
  have hs : ∀ a, a = i ∨ a = j → ‖u a‖ ≤ ‖u i‖ + ‖u j‖ := by
    rintro a (rfl | rfl)
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have hgg : ∀ a, a = i ∨ a = j → ‖(G *ᵥ v) a‖ ≤ ‖(G *ᵥ v) i‖ + ‖(G *ᵥ v) j‖ := by
    rintro a (rfl | rfl)
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have hnum : ∀ a b σ τ, a = i ∨ a = j → b = i ∨ b = j → σ = i ∨ σ = j → τ = i ∨ τ = j →
      ‖u a‖ * Γ * ‖(G *ᵥ v) τ‖ + (‖u σ‖ * Γ + lb * Γ + Γ * Z) * ‖(G *ᵥ v) b‖ +
        lb * Γ * ‖(G *ᵥ v) τ‖ + (2 * Γ ^ 2 * Z + Γ * Z * ‖(G *ᵥ v) τ‖) ≤
      4 * (Γ * (‖u i‖ + ‖u j‖) * (‖(G *ᵥ v) i‖ + ‖(G *ᵥ v) j‖) +
        lb * Γ * (‖(G *ᵥ v) i‖ + ‖(G *ᵥ v) j‖) + Γ ^ 2 * Z) := by
    intro a b σ τ ha hb hσ hτ
    exact FIH_d2_num _ _ _ _ _ _ Γ lb Z (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (hs a ha) (hs σ hσ) (hgg b hb) (hgg τ hτ) hΓ0 hlb0 hZ0 hZ
  set d2 := Γ * (‖u i‖ + ‖u j‖) * (‖(G *ᵥ v) i‖ + ‖(G *ᵥ v) j‖) +
    lb * Γ * (‖(G *ᵥ v) i‖ + ‖(G *ᵥ v) j‖) + Γ ^ 2 * Z with hd2
  have k20 : ‖wirt 2 0 Hs w₀‖ ≤ 4 * d2 := by
    have e : wirt 2 0 Hs w₀ = cc * FIH_op (-Complex.I)
        (fun w => hgDer D N θ (Matrix.of (setEntry h j i w)) Λ z u v j i) w₀ := by
      show dW (dW Hs) w₀ = _
      rw [hdW, FIH_dW_eq, FIH_op_const_mul _ _ hX1]
    rw [e, norm_mul]
    have := FIH_R2 θ hθ0 hθ1 h hh Λ hΛ z hz j i u v hu j i j i (-Complex.I) cc hcc1 hFm
      (hHm j) w₀ Γ lb Z hΓ0 hGb hTy hTe hDl hW
    rw [hse] at this
    exact (mul_le_of_le_one_left (norm_nonneg _) hcc1).trans (this.trans
      (hnum j i j i (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)))
  have k11 : ‖wirt 1 1 Hs w₀‖ ≤ 4 * d2 := by
    have e : wirt 1 1 Hs w₀ = cc * FIH_op (-Complex.I)
        (fun w => hgDer D N θ (Matrix.of (setEntry h j i w)) Λ z u v i j) w₀ := by
      show dW (dWbar Hs) w₀ = _
      rw [hdWb, FIH_dW_eq, FIH_op_const_mul _ _ hX2]
    rw [e, norm_mul]
    have := FIH_R2 θ hθ0 hθ1 h hh Λ hΛ z hz j i u v hu i j j i (-Complex.I) cc hcc1 hFm
      (hHm i) w₀ Γ lb Z hΓ0 hGb hTy hTe hDl hW
    rw [hse] at this
    exact (mul_le_of_le_one_left (norm_nonneg _) hcc1).trans (this.trans
      (hnum i j j i (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)))
  have k02 : ‖wirt 0 2 Hs w₀‖ ≤ 4 * d2 := by
    have e : wirt 0 2 Hs w₀ = cc * FIH_op Complex.I
        (fun w => hgDer D N θ (Matrix.of (setEntry h j i w)) Λ z u v i j) w₀ := by
      show dWbar (dWbar Hs) w₀ = _
      rw [hdWb, FIH_dWbar_eq, FIH_op_const_mul _ _ hX2]
    rw [e, norm_mul]
    have := FIH_R2 θ hθ0 hθ1 h hh Λ hΛ z hz j i u v hu i j i j Complex.I cc hcc1 hFp
      (hHp i) w₀ Γ lb Z hΓ0 hGb hTy hTe hDl hW
    rw [hse] at this
    exact (mul_le_of_le_one_left (norm_nonneg _) hcc1).trans (this.trans
      (hnum i j i j (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)))
  have e : FIH_bnd Hs w₀ 2 = ‖wirt 0 2 Hs w₀‖ + ‖wirt 1 1 Hs w₀‖ + ‖wirt 2 0 Hs w₀‖ := by
    simp [FIH_bnd, Finset.sum_range_succ]
  rw [e]
  linarith

/-! ### Measurability and the deterministic bounds -/

private lemma FIH_res_meas {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    Measurable fun h : Idx D N → Idx D N → ℂ => res (Matrix.of h + Λ) z := by
  have hc : Continuous fun h : Idx D N → Idx D N → ℂ =>
      Matrix.of h + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) :=
    ((continuous_id : Continuous fun h : Idx D N → Idx D N → ℂ => h).add
      continuous_const).sub continuous_const
  have e : (fun h : Idx D N → Idx D N → ℂ => res (Matrix.of h + Λ) z) = fun h =>
      Ring.inverse (Matrix.of h + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)).det •
        (Matrix.of h + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)).adjugate := by
    funext h
    rw [res, Matrix.inv_def]
  rw [e, Ring.inverse_eq_inv']
  exact (hc.matrix_det.measurable.inv).smul hc.matrix_adjugate.measurable

private lemma FIH_sTheta_cont (D N : ℕ) (θ : ℝ) : Continuous (sTheta D N θ) := by
  have hn : ∀ E : Matrix (Idx D N) (Idx D N) ℂ,
      Continuous fun R : Matrix (Idx D N) (Idx D N) ℂ => ntr (R * E) := fun E =>
    continuous_const.mul ((continuous_id.matrix_mul continuous_const).matrix_trace)
  have hn1 : Continuous fun R : Matrix (Idx D N) (Idx D N) ℂ => ntr R :=
    continuous_const.mul continuous_id.matrix_trace
  have h1 : Continuous fun R : Matrix (Idx D N) (Idx D N) ℂ =>
      ∑ a : Fin D, ((D : ℂ) * ntr (R * Ea D N a)) • Ea D N a :=
    continuous_finsetSum _ fun a _ => (continuous_const.mul (hn (Ea D N a))).smul continuous_const
  have h2 : Continuous fun R : Matrix (Idx D N) (Idx D N) ℂ =>
      ntr R • (1 : Matrix (Idx D N) (Idx D N) ℂ) := hn1.smul continuous_const
  have e : sTheta D N θ = fun R => (θ : ℂ) • (∑ a : Fin D, ((D : ℂ) * ntr (R * Ea D N a)) •
      Ea D N a) + ((1 - θ : ℝ) : ℂ) • (ntr R • (1 : Matrix (Idx D N) (Idx D N) ℂ)) := by
    funext R; rfl
  rw [e]
  exact (h1.const_smul (θ : ℂ)).add (h2.const_smul ((1 - θ : ℝ) : ℂ))

private lemma FIH_hg_meas {D N : ℕ} (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) :
    Measurable fun h : Idx D N → Idx D N → ℂ =>
      ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ := by
  have hΦ : Continuous fun q : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ =>
      ‖star u ⬝ᵥ ((q.1 * q.2 + sTheta D N θ q.2 * q.2) *ᵥ v)‖ := by
    have hS := FIH_sTheta_cont D N θ
    have hA : Continuous fun q : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ =>
        q.1 * q.2 + sTheta D N θ q.2 * q.2 :=
      (continuous_fst.matrix_mul continuous_snd).add
        ((hS.comp continuous_snd).matrix_mul continuous_snd)
    exact (continuous_const.dotProduct (hA.matrix_mulVec continuous_const)).norm
  haveI : SecondCountableTopology (Matrix (Idx D N) (Idx D N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Idx D N → Idx D N → ℂ))
  have hof : Measurable fun h : Idx D N → Idx D N → ℂ =>
      (Matrix.of h : Matrix (Idx D N) (Idx D N) ℂ) := by
    exact measurable_id
  have hm : Measurable fun h : Idx D N → Idx D N → ℂ =>
      ((Matrix.of h : Matrix (Idx D N) (Idx D N) ℂ), res (Matrix.of h + Λ) z) :=
    hof.prodMk (FIH_res_meas Λ z)
  have e : (fun h : Idx D N → Idx D N → ℂ =>
      ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖) =
      (fun q : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ =>
        ‖star u ⬝ᵥ ((q.1 * q.2 + sTheta D N θ q.2 * q.2) *ᵥ v)‖) ∘
      (fun h : Idx D N → Idx D N → ℂ =>
        ((Matrix.of h : Matrix (Idx D N) (Idx D N) ℂ), res (Matrix.of h + Λ) z)) := by
    funext h
    simp only [Function.comp, hgUnder]
  rw [e]
  exact hΦ.measurable.comp hm

private lemma FIH_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
    (x w : ι → ℂ) :
    ‖star x ⬝ᵥ (T *ᵥ w)‖ ≤
      opNorm T * (Real.sqrt (∑ k, ‖x k‖ ^ 2) * Real.sqrt (∑ k, ‖w k‖ ^ 2)) := by
  have e : star x ⬝ᵥ (T *ᵥ w) =
      inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanLin T (WithLp.toLp 2 w)) := by
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
  have hx' : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = Real.sqrt (∑ k, ‖x k‖ ^ 2) :=
    EuclideanSpace.norm_eq _
  have hw' : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ ι)‖ = Real.sqrt (∑ k, ‖w k‖ ^ 2) :=
    EuclideanSpace.norm_eq _
  have h1 : Matrix.toEuclideanLin T (WithLp.toLp 2 w) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 w) := rfl
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 w)‖ ≤
      opNorm T * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ ι)‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [e, h1, ← hx', ← hw']
  calc ‖inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 w))‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 w)‖ := norm_inner_le_norm _ _
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
          (opNorm T * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ ι)‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = _ := by ring

/-- On Hermitian arrays every form of `G` over vectors of norm `≤ 1` is `≤ η⁻¹`: the good event
holds with `Γ = Υ = B` for every `B ≥ η⁻¹`. -/
private lemma FIH_herm_good {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (V : Finset (Idx D N → ℂ)) (hVn : ∀ x ∈ V, ∑ k, ‖x k‖ ^ 2 ≤ 1) (B : ℝ) (hB : z.im⁻¹ ≤ B) :
    h ∈ goodSet Λ z V B B := by
  have hG := opNorm_res_le _ (hh.add hΛ) z hz
  have hf : ∀ x ∈ V, ∀ y ∈ V, ‖star x ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y)‖ ≤ B := by
    intro x hx y hy
    refine (FIH_form_le _ x y).trans ?_
    have h1 : Real.sqrt (∑ k, ‖x k‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (hVn x hx)
    have h2 : Real.sqrt (∑ k, ‖y k‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (hVn y hy)
    have h3 : Real.sqrt (∑ k, ‖x k‖ ^ 2) * Real.sqrt (∑ k, ‖y k‖ ^ 2) ≤ 1 :=
      mul_le_one₀ h1 (Real.sqrt_nonneg _) h2
    have h4 : 0 ≤ opNorm (res (Matrix.of h + Λ) z) := norm_nonneg _
    calc _ ≤ opNorm (res (Matrix.of h + Λ) z) * 1 :=
          mul_le_mul_of_nonneg_left h3 h4
      _ ≤ B := by linarith
  exact fun x hx y hy => ⟨hf x hx y hy, (Complex.im_le_norm _).trans (hf x hx x hx)⟩

private lemma FIH_dot_self {ι : Type*} [Fintype ι] (y : ι → ℂ) :
    ‖star y ⬝ᵥ y‖ = ∑ k, ‖y k‖ ^ 2 := by
  have : star y ⬝ᵥ y = ((∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

private lemma FIH_tilt_le (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (u : Idx D N → ℂ)
    (r k : Idx D N) : ‖tiltV D N θ u r k‖ ≤ ‖u k‖ := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos k.2
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast Fin.pos k.1
  have e : (N : ℝ) * varProf D N θ k r =
      θ * (if k.1 = r.1 then 1 else 0) + (1 - θ) * (D : ℝ)⁻¹ := by
    unfold varProf
    split_ifs <;> field_simp <;> ring
  have hD' : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
  have hD0 : 0 ≤ (D : ℝ)⁻¹ := by positivity
  have h1 : 0 ≤ (N : ℝ) * varProf D N θ k r := by
    rw [e]; split_ifs <;> nlinarith
  have h2 : (N : ℝ) * varProf D N θ k r ≤ 1 := by
    rw [e]; split_ifs <;> nlinarith
  simp only [tiltV, norm_mul, Complex.norm_real, Real.norm_of_nonneg h1]
  exact mul_le_of_le_one_right (norm_nonneg _) h2

/-- The vectors of `isoVecs` have norm `≤ 1` for `θ ∈ [0, 1]`, `‖Λ‖ ≤ 1/10` and `|u|, |v| ≤ 1`
(`N s_{kr} ≤ 1`). -/
private lemma FIH_iv_norm (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (hΛn : opNorm Λ ≤ 1 / 10)
    (u v : Idx D N → ℂ) (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1) :
    ∀ x ∈ isoVecs D N θ Λ u v, ∑ k, ‖x k‖ ^ 2 ≤ 1 := by
  have hle : ∀ y : Idx D N → ℂ, (∀ k, ‖y k‖ ≤ ‖u k‖) → ∑ k, ‖y k‖ ^ 2 ≤ 1 := fun y hy =>
    (Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hy k) 2).trans hu
  intro x hx
  simp only [isoVecs, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with (((((rfl | rfl | rfl) | ⟨a, rfl⟩) | ⟨k, rfl⟩) | ⟨r, rfl⟩) | ⟨r, rfl⟩)
  · exact hu
  · exact hv
  · rw [hΛ.eq]
    set S := ∑ k, ‖(Λ *ᵥ u) k‖ ^ 2 with hS
    have h1 := FIH_form_le Λ (Λ *ᵥ u) u
    rw [FIH_dot_self, ← hS] at h1
    have h2 : Real.sqrt (∑ k, ‖u k‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hu
    have h3 : 0 ≤ opNorm Λ := norm_nonneg _
    have h4 : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
    have h5 : S = Real.sqrt S * Real.sqrt S := (Real.mul_self_sqrt (by positivity)).symm
    have h6 : Real.sqrt S * Real.sqrt S ≤ Real.sqrt S * (1 / 10) := by
      calc Real.sqrt S * Real.sqrt S = S := h5.symm
        _ ≤ opNorm Λ * (Real.sqrt S * Real.sqrt (∑ k, ‖u k‖ ^ 2)) := h1
        _ ≤ (1 / 10) * (Real.sqrt S * 1) := by gcongr
        _ = _ := by ring
    nlinarith
  · refine hle _ fun k => ?_
    simp only [Ea, Matrix.diagonal_conjTranspose, Matrix.mulVec_diagonal, Pi.star_apply, norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    split_ifs <;> simp
  · exact FIH_single_norm k
  · exact hle _ fun k => FIH_tilt_le D N θ hθ0 hθ1 u r k
  · refine hle _ fun k => ?_
    rw [Pi.star_apply, norm_star]
    exact FIH_tilt_le D N θ hθ0 hθ1 u r k

/-! ### The pointwise bounds of the order-`k` integrand -/

private lemma FIH_swap {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    ∑ x, ∑ y, ∑ w, f x y w = ∑ w, ∑ x, ∑ y, f x y w := by
  calc _ = ∑ x, ∑ w, ∑ y, f x y w := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private lemma FIH_words (p a b : ℕ) (hp : 1 ≤ p) :
    (Fintype.card ((Fin b → Option (Fin (p - 1) ⊕ Fin p)) × (Fin a → Option (Fin (p - 1) ⊕ Fin p)))
      : ℝ) = ((2 * p : ℕ) : ℝ) ^ (a + b) := by
  have : Fintype.card (Option (Fin (p - 1) ⊕ Fin p)) = 2 * p := by
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin]
    omega
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    this]
  push_cast
  ring

private lemma FIH_cnt_total (p a b : ℕ) (σ : Fin b → Option (Fin (p - 1) ⊕ Fin p))
    (τ : Fin a → Option (Fin (p - 1) ⊕ Fin p)) :
    (FIH_cnt τ none + FIH_cnt σ none) +
      ∑ m : Fin (p - 1) ⊕ Fin p, (FIH_cnt τ (some m) + FIH_cnt σ (some m)) = a + b := by
  have h1 := FIH_cnt_sum τ
  have h2 := FIH_cnt_sum σ
  rw [Fintype.sum_option] at h1 h2
  rw [Finset.sum_add_distrib]
  omega

/-- The order-`k` integrand on the good event: after `Σ_{i,j} |u_i|`,
`≤ M^{k+1} K Σ_{n=1}^{2p} (ζ̂ λ²)^{n/3} |(H̲G)_{uv}|^{2p-n}` with `M = √N`. -/
private lemma FIH_pt_good (D N p k a : ℕ) (hp : 1 ≤ p) (hk : 2 ≤ k) (ha : a ≤ k) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (hΛn : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (u v : Idx D N → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1) (Γ Υ lb : ℝ) (hD : 1 ≤ (D : ℝ))
    (hΓ : 1 ≤ Γ) (hΓM : Γ ≤ Real.sqrt N) (hΥ : z.im ≤ Υ) (hΥ2 : Υ ≤ (N : ℝ) * z.im)
    (hlb : (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ≤ lb)
    (cWs c₁ : ℝ) (hc₁ : 12 + 2 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) + (k + 1) * cWs ≤ c₁)
    (hcWs : 0 ≤ cWs)
    (hgen : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → ∀ (i j : Idx D N) (Γ' Υ' : ℝ),
      1 ≤ Γ' → z.im ≤ Υ' → h ∈ goodSet Λ z (isoVecs D N θ Λ u v) Γ' Υ' → ∀ l ≤ k,
        FIH_bnd (FIH_Hs D N θ h Λ z u v j i) (h j i) l ≤
          (k + 1) * cWs * (1 + ‖z‖) * Γ' ^ (l + 2) * Real.sqrt (Υ' / z.im))
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (hgood : h ∈ isoGood D N θ Λ z u v Γ Υ lb) :
    ∑ i, ∑ j, ‖u i‖ * ‖wirt a (k - a) (fun w =>
        (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
        (h j i)‖ ≤
      Real.sqrt N ^ (k + 1) * (((2 * p : ℕ) : ℝ) ^ k * (20 * D * c₁ ^ (k + 1))) *
        ∑ n ∈ Finset.Icc 1 (2 * p),
          ((Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) * lb ^ 2) ^
            ((n : ℝ) / 3) * ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - n) := by
  classical
  set M := Real.sqrt N with hMdef
  set ζ := Real.sqrt (Υ / ((N : ℝ) * z.im)) with hζdef
  set δ := ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ with hδdef
  set X := (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * ζ * lb ^ 2 with hX
  set G := res (Matrix.of h + Λ) z with hG
  have hM1 : 1 ≤ M := hΓ.trans hΓM
  have hN1 : (1 : ℝ) ≤ N := Real.one_le_sqrt.mp hM1
  have hN0 : (0 : ℝ) < N := by linarith
  have hMsq : M ^ 2 = N := Real.sq_sqrt hN0.le
  have hΥ0 : 0 < Υ := hz.trans_le hΥ
  have hMζ : M * ζ = Real.sqrt (Υ / z.im) := by
    rw [hMdef, hζdef, ← Real.sqrt_mul hN0.le]
    congr 1
    field_simp
  have hMζ1 : 1 ≤ M * ζ := by rw [hMζ]; exact Real.one_le_sqrt.mpr ((one_le_div hz).mpr hΥ)
  have hζ0 : 0 ≤ ζ := Real.sqrt_nonneg _
  have hζ1 : ζ ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one (by positivity)).mpr hΥ2)
  have hZ : Υ / ((N : ℝ) * z.im) = ζ ^ 2 := (Real.sq_sqrt (by positivity)).symm
  have hz1 : 1 ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)
  have hcD : 1 ≤ Real.sqrt D + 3 := by linarith [Real.sqrt_nonneg (D : ℝ)]
  have hΓ0 : 0 ≤ Γ := by linarith
  have hζl : ζ ≤ lb := by
    have h1 : 1 ≤ (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hcD hz1) (one_le_pow₀ hΓ)
    calc ζ = 1 * ζ := (one_mul ζ).symm
      _ ≤ (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * ζ := mul_le_mul_of_nonneg_right h1 hζ0
      _ ≤ lb := hlb
  have hZl : Υ / ((N : ℝ) * z.im) ≤ lb := by
    rw [hZ]; nlinarith
  have hc1 : 1 ≤ c₁ := by
    have : 0 ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by positivity
    have : 0 ≤ ((k : ℝ) + 1) * cWs := by positivity
    linarith
  have hg := hgood.1
  have hV := FIH_iv_e D N θ Λ u v
  have hvV := FIH_iv_v D N θ Λ u v
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hX0 : 0 ≤ X := by positivity
  have h12 : 12 ≤ c₁ := by
    have : 0 ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by positivity
    have : 0 ≤ ((k : ℝ) + 1) * cWs := by positivity
    linarith
  set s : Idx D N → ℝ := fun i => ‖u i‖ with hs
  set g : Idx D N → ℝ := fun i => ‖(G *ᵥ v) i‖ with hgdef
  set βG : Idx D N → Idx D N → ℕ → ℝ := fun i j l => FIH_bnd (FIH_Gs D N h Λ z v j i) (h j i) l
    with hβG
  set βD : Idx D N → Idx D N → ℕ → ℝ :=
    fun i j l => FIH_bnd (FIH_Hs D N θ h Λ z u v j i) (h j i) l with hβD
  have hse : ∀ i j, setEntry h j i (h j i) = h := fun i j => FIH_setEntry_self h hh j i
  -- the hypotheses of `FIH_word`
  have hs1 : ∑ i, s i ^ 2 ≤ 1 := hu
  have hg2 : ∑ i, g i ^ 2 ≤ (M * ζ) ^ 2 := by
    rw [hMζ, Real.sq_sqrt (by positivity)]
    have := ward_vec _ (hh.add hΛ) z hz v
    simp only [hgdef, hG]
    rw [this]
    exact div_le_div_of_nonneg_right (hg v hvV v hvV).2 hz.le
  have hgΓ : ∀ i, g i ≤ Γ := FIH_good_gv Λ z _ Γ Υ h hg hV v hvV
  have hcard : (Fintype.card (Idx D N) : ℝ) = D * M ^ 2 := by
    rw [hMsq]; simp [Fintype.card_prod, Fintype.card_fin]
  have hG0 : ∀ i j, βG i j 0 ≤ c₁ * g j := by
    intro i j
    simp only [hβG, (FIH_good_G D N h hh Λ hΛ z hz _ v hvV hV Γ Υ hΓ hg i j).1]
    exact le_mul_of_one_le_left (norm_nonneg _) hc1
  have hGb : ∀ i j l, l ≤ k → βG i j l ≤ c₁ * Γ ^ l * (g i + g j) := by
    intro i j l hl
    refine ((FIH_good_G D N h hh Λ hΛ z hz _ v hvV hV Γ Υ hΓ hg i j).2 l).trans ?_
    have h1 : ((l + 1 : ℕ) : ℝ) ^ (l + 1) ≤ c₁ := by
      have h2 : ((l + 1 : ℕ) : ℝ) ^ (l + 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by
        calc ((l + 1 : ℕ) : ℝ) ^ (l + 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (l + 1) := by
              gcongr
          _ ≤ _ := pow_le_pow_right₀ (by norm_cast; omega) (by omega)
      have : 0 ≤ ((k : ℝ) + 1) * cWs := by positivity
      have : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by positivity
      linarith
    have : 0 ≤ Γ ^ l * (g i + g j) := by positivity
    calc ((l + 1 : ℕ) : ℝ) ^ (l + 1) * Γ ^ l * (g i + g j)
        = ((l + 1 : ℕ) : ℝ) ^ (l + 1) * (Γ ^ l * (g i + g j)) := by ring
      _ ≤ c₁ * (Γ ^ l * (g i + g j)) := mul_le_mul_of_nonneg_right h1 this
      _ = _ := by ring
  have hD0 : ∀ i j, βD i j 0 = δ := by
    intro i j
    simp only [hβD, FIH_bnd_zero, FIH_Hs, hse]
    rfl
  have hDl : ∀ i j l, 1 ≤ l → l ≤ k → βD i j l ≤ c₁ * (1 + ‖z‖) * Γ ^ (l + 2) * (M * ζ) := by
    intro i j l _ hl
    refine (hgen h hh i j Γ Υ hΓ hΥ hg l hl).trans ?_
    rw [← hMζ]
    have h1 : ((k : ℝ) + 1) * cWs ≤ c₁ := by
      have : 0 ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by positivity
      linarith
    have : 0 ≤ (1 + ‖z‖) * Γ ^ (l + 2) * (M * ζ) := by positivity
    calc ((k : ℝ) + 1) * cWs * (1 + ‖z‖) * Γ ^ (l + 2) * (M * ζ)
        = (((k : ℝ) + 1) * cWs) * ((1 + ‖z‖) * Γ ^ (l + 2) * (M * ζ)) := by ring
      _ ≤ c₁ * ((1 + ‖z‖) * Γ ^ (l + 2) * (M * ζ)) := mul_le_mul_of_nonneg_right h1 this
      _ = _ := by ring
  have hD1 : ∀ i j, βD i j 1 ≤ c₁ * (s i * g j + s j * g i + Γ * lb) := by
    intro i j
    refine (FIH_good_D1 D N θ hθ0 hθ1 h hh Λ hΛ z hz u v Γ Υ lb hΓ hZl hgood i j).trans ?_
    have : 0 ≤ s i * g j + s j * g i + Γ * lb := by
      have := hζ0.trans hζl
      positivity
    exact mul_le_mul_of_nonneg_right (by linarith) this
  have hD2 : ∀ i j, βD i j 2 ≤
      c₁ * (Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) + Γ ^ 2 * ζ ^ 2) := by
    intro i j
    refine (FIH_good_D2 D N θ hθ0 hθ1 h hh Λ hΛ z hz u v hu hv Γ Υ lb hΓ (by positivity) hZl
      hgood i j).trans ?_
    rw [hZ]
    have : 0 ≤ Γ * (s i + s j) * (g i + g j) + lb * Γ * (g i + g j) + Γ ^ 2 * ζ ^ 2 := by
      have := hζ0.trans hζl
      positivity
    exact mul_le_mul_of_nonneg_right (by linarith) this
  -- the Leibniz expansion and the bound of each word
  have hL : ∀ i j, ‖wirt a (k - a) (fun w =>
        (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
        (h j i)‖ ≤
      ∑ w : (Fin (k - a) → Option (Fin (p - 1) ⊕ Fin p)) × (Fin a → Option (Fin (p - 1) ⊕ Fin p)),
        βG i j (FIH_cnt w.2 none + FIH_cnt w.1 none) *
          ∏ m, βD i j (FIH_cnt w.2 (some m) + FIH_cnt w.1 (some m)) := by
    intro i j
    refine (FIH_leib D N θ hθ0 hθ1 h hh Λ hΛ z hz u v hu hv p j i a (k - a) (h j i)).trans
      (le_of_eq ?_)
    rw [Fintype.sum_prod_type]
  set B := M ^ (k + 1) * (20 * D * c₁ ^ (k + 1)) *
    ∑ n ∈ Finset.Icc 1 (2 * p), X ^ ((n : ℝ) / 3) * δ ^ (2 * p - n) with hB
  have hW : ∀ w : (Fin (k - a) → Option (Fin (p - 1) ⊕ Fin p)) ×
      (Fin a → Option (Fin (p - 1) ⊕ Fin p)),
      ∑ i, ∑ j, s i * (βG i j (FIH_cnt w.2 none + FIH_cnt w.1 none) *
        ∏ m, βD i j (FIH_cnt w.2 (some m) + FIH_cnt w.1 (some m))) ≤ B := by
    intro w
    have hrc := FIH_cnt_total p a (k - a) w.1 w.2
    refine (FIH_word s g βG βD D M ζ Γ lb (1 + ‖z‖) (Real.sqrt D + 3) c₁ δ k _ _ hk
      (by rw [hrc]; omega) (fun i => norm_nonneg _) hs1 (fun i => norm_nonneg _) hgΓ hg2 hcard
      hD hΓ hΓM hMζ1 hζ1 hz1 hcD hlb hc1 hδ0 (fun i j l => FIH_bnd_nonneg _ _ _) hG0 hGb
      (fun i j l => FIH_bnd_nonneg _ _ _) hD0 hDl hD1 hD2).trans ?_
    set q := (Finset.univ.filter fun m : Fin (p - 1) ⊕ Fin p =>
      1 ≤ FIH_cnt w.2 (some m) + FIH_cnt w.1 (some m)).card with hq
    have hqle : q ≤ p - 1 + p := by
      have := Finset.card_le_univ (Finset.univ.filter fun m : Fin (p - 1) ⊕ Fin p =>
        1 ≤ FIH_cnt w.2 (some m) + FIH_cnt w.1 (some m))
      simpa [Fintype.card_sum, Fintype.card_fin] using this
    have hcardκ : Fintype.card (Fin (p - 1) ⊕ Fin p) - q = 2 * p - (q + 1) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hcardκ, hB, mul_assoc (M ^ (k + 1) * (20 * D * c₁ ^ (k + 1)))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.single_le_sum (f := fun n : ℕ => X ^ ((n : ℝ) / 3) * δ ^ (2 * p - n))
      (fun n _ => by positivity) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  calc ∑ i, ∑ j, ‖u i‖ * ‖wirt a (k - a) (fun w =>
        (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
        (h j i)‖
      ≤ ∑ i, ∑ j, ∑ w : (Fin (k - a) → Option (Fin (p - 1) ⊕ Fin p)) ×
          (Fin a → Option (Fin (p - 1) ⊕ Fin p)), s i * (βG i j (FIH_cnt w.2 none +
            FIH_cnt w.1 none) * ∏ m, βD i j (FIH_cnt w.2 (some m) + FIH_cnt w.1 (some m))) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hL i j) (norm_nonneg _)
    _ = ∑ w : (Fin (k - a) → Option (Fin (p - 1) ⊕ Fin p)) ×
          (Fin a → Option (Fin (p - 1) ⊕ Fin p)), ∑ i, ∑ j, s i * (βG i j (FIH_cnt w.2 none +
            FIH_cnt w.1 none) * ∏ m, βD i j (FIH_cnt w.2 (some m) + FIH_cnt w.1 (some m))) :=
        FIH_swap _
    _ ≤ ∑ _w : (Fin (k - a) → Option (Fin (p - 1) ⊕ Fin p)) ×
          (Fin a → Option (Fin (p - 1) ⊕ Fin p)), B := Finset.sum_le_sum fun w _ => hW w
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, FIH_words p a (k - a) hp,
          show a + (k - a) = k by omega, hB]
        ring

/-- The order-`k` integrand on every Hermitian array, from `‖G‖ ≤ η⁻¹ ≤ N`, for
`k ≤ 16p + 16`: after `Σ_{i,j} |u_i|`, `≤ M^{k+1} K N^{21p+18}` with `M = √N`. -/
private lemma FIH_pt_bad (D N p k a : ℕ) (hp : 1 ≤ p) (hk' : k ≤ 16 * p + 16) (ha : a ≤ k)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (hΛn : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (u v : Idx D N → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1) (hD : 1 ≤ (D : ℝ)) (hN1 : 1 ≤ (N : ℝ))
    (hzN : ((N : ℝ))⁻¹ ≤ z.im) (hzn : ‖z‖ ≤ N)
    (cWs c₁ : ℝ) (hc₁ : 12 + 2 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) + (k + 1) * cWs ≤ c₁)
    (hcWs : 0 ≤ cWs)
    (hgen : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → ∀ (i j : Idx D N) (Γ' Υ' : ℝ),
      1 ≤ Γ' → z.im ≤ Υ' → h ∈ goodSet Λ z (isoVecs D N θ Λ u v) Γ' Υ' → ∀ l ≤ k,
        FIH_bnd (FIH_Hs D N θ h Λ z u v j i) (h j i) l ≤
          (k + 1) * cWs * (1 + ‖z‖) * Γ' ^ (l + 2) * Real.sqrt (Υ' / z.im))
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ∑ i, ∑ j, ‖u i‖ * ‖wirt a (k - a) (fun w =>
        (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
        (h j i)‖ ≤
      Real.sqrt N ^ (k + 1) * (((2 * p : ℕ) : ℝ) ^ k * (D ^ 2 * c₁ ^ (2 * p) * 2 ^ (2 * p))) *
        Real.sqrt N ^ (42 * p + 36) := by
  classical
  set M := Real.sqrt N with hMdef
  have hN0 : (0 : ℝ) < N := by linarith
  have hMsq : M ^ 2 = N := Real.sq_sqrt hN0.le
  have hM1 : 1 ≤ M := Real.one_le_sqrt.mpr hN1
  have hM0 : 0 ≤ M := by linarith
  have hN0' : (0 : ℝ) ≤ N := hN0.le
  have h12 : 12 ≤ c₁ := by
    have : 0 ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by positivity
    have : 0 ≤ ((k : ℝ) + 1) * cWs := by positivity
    linarith
  have hc0 : 0 ≤ c₁ := by linarith
  have hηN : z.im ≤ N := (Complex.im_le_norm z).trans hzn
  have hinv : z.im⁻¹ ≤ N := by
    rw [inv_le_comm₀ hz hN0]; exact hzN
  have hivn := FIH_iv_norm D N θ hθ0 hθ1 Λ hΛ hΛn u v hu hv
  have hg : h ∈ goodSet Λ z (isoVecs D N θ Λ u v) N N :=
    FIH_herm_good h hh Λ hΛ z hz _ hivn N hinv
  have hV := FIH_iv_e D N θ Λ u v
  have hvV := FIH_iv_v D N θ Λ u v
  have hsq : Real.sqrt ((N : ℝ) / z.im) ≤ N := by
    rw [Real.sqrt_le_left hN0']
    calc (N : ℝ) / z.im = N * z.im⁻¹ := div_eq_mul_inv _ _
      _ ≤ N * N := mul_le_mul_of_nonneg_left hinv hN0'
      _ = _ := by ring
  have hz2 : 1 + ‖z‖ ≤ 2 * N := by linarith
  set βG : Idx D N → Idx D N → ℕ → ℝ := fun i j l => FIH_bnd (FIH_Gs D N h Λ z v j i) (h j i) l
    with hβG
  set βD : Idx D N → Idx D N → ℕ → ℝ :=
    fun i j l => FIH_bnd (FIH_Hs D N θ h Λ z u v j i) (h j i) l with hβD
  have hGb : ∀ i j l, l ≤ k → βG i j l ≤ c₁ * (N : ℝ) ^ (l + 1) := by
    intro i j l hl
    refine ((FIH_good_G D N h hh Λ hΛ z hz _ v hvV hV N N hN1 hg i j).2 l).trans ?_
    have hgi := FIH_good_gv Λ z _ N N h hg hV v hvV i
    have hgj := FIH_good_gv Λ z _ N N h hg hV v hvV j
    have h1 : ((l + 1 : ℕ) : ℝ) ^ (l + 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by
      calc ((l + 1 : ℕ) : ℝ) ^ (l + 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (l + 1) := by gcongr
        _ ≤ _ := pow_le_pow_right₀ (by norm_cast; omega) (by omega)
    have h2 : 2 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) ≤ c₁ := by
      have : 0 ≤ ((k : ℝ) + 1) * cWs := by positivity
      linarith
    have h3 : 0 ≤ ((l + 1 : ℕ) : ℝ) ^ (l + 1) := by positivity
    calc ((l + 1 : ℕ) : ℝ) ^ (l + 1) * (N : ℝ) ^ l *
          (‖(res (Matrix.of h + Λ) z *ᵥ v) i‖ + ‖(res (Matrix.of h + Λ) z *ᵥ v) j‖)
        ≤ ((l + 1 : ℕ) : ℝ) ^ (l + 1) * (N : ℝ) ^ l * (2 * N) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (2 * ((l + 1 : ℕ) : ℝ) ^ (l + 1)) * (N : ℝ) ^ (l + 1) := by ring
      _ ≤ c₁ * (N : ℝ) ^ (l + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hDb : ∀ i j l, l ≤ k → βD i j l ≤ c₁ * (1 + ‖z‖) * (N : ℝ) ^ (l + 3) := by
    intro i j l hl
    refine (hgen h hh i j N N hN1 hηN hg l hl).trans ?_
    have h1 : ((k : ℝ) + 1) * cWs ≤ c₁ := by
      have : 0 ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by positivity
      linarith
    have h0 : 0 ≤ (1 + ‖z‖) * (N : ℝ) ^ (l + 2) := by positivity
    calc ((k : ℝ) + 1) * cWs * (1 + ‖z‖) * (N : ℝ) ^ (l + 2) * Real.sqrt ((N : ℝ) / z.im)
        ≤ ((k : ℝ) + 1) * cWs * (1 + ‖z‖) * (N : ℝ) ^ (l + 2) * N :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (((k : ℝ) + 1) * cWs) * ((1 + ‖z‖) * (N : ℝ) ^ (l + 3)) := by ring
      _ ≤ c₁ * ((1 + ‖z‖) * (N : ℝ) ^ (l + 3)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  have hL : ∀ i j, ‖wirt a (k - a) (fun w =>
        (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
        (h j i)‖ ≤
      ∑ w : (Fin (k - a) → Option (Fin (p - 1) ⊕ Fin p)) × (Fin a → Option (Fin (p - 1) ⊕ Fin p)),
        βG i j (FIH_cnt w.2 none + FIH_cnt w.1 none) *
          ∏ m, βD i j (FIH_cnt w.2 (some m) + FIH_cnt w.1 (some m)) := by
    intro i j
    refine (FIH_leib D N θ hθ0 hθ1 h hh Λ hΛ z hz u v hu hv p j i a (k - a) (h j i)).trans
      (le_of_eq ?_)
    rw [Fintype.sum_prod_type]
  -- one word
  set B := c₁ ^ (2 * p) * 2 ^ (2 * p) * M ^ (2 * k + 16 * p - 6) with hB
  have hW : ∀ (w : (Fin (k - a) → Option (Fin (p - 1) ⊕ Fin p)) ×
      (Fin a → Option (Fin (p - 1) ⊕ Fin p))) (i j : Idx D N),
      βG i j (FIH_cnt w.2 none + FIH_cnt w.1 none) *
        ∏ m, βD i j (FIH_cnt w.2 (some m) + FIH_cnt w.1 (some m)) ≤ B := by
    intro w i j
    have hrc := FIH_cnt_total p a (k - a) w.1 w.2
    have hcle : ∀ m, FIH_cnt w.2 (some m) + FIH_cnt w.1 (some m) ≤ k := by
      intro m
      have := Finset.single_le_sum (f := fun m : Fin (p - 1) ⊕ Fin p =>
        FIH_cnt w.2 (some m) + FIH_cnt w.1 (some m)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ m)
      omega
    have hb := FIH_word_bad (βG i j) (βD i j) c₁ (1 + ‖z‖) N
      (FIH_cnt w.2 none + FIH_cnt w.1 none) (fun m => FIH_cnt w.2 (some m) + FIH_cnt w.1 (some m))
      hc0 (by positivity) hN0' (FIH_bnd_nonneg _ _ _) (hGb i j _ (by omega))
      (fun l => FIH_bnd_nonneg _ _ _) (fun m => hDb i j _ (hcle m))
    have hκ : Fintype.card (Fin (p - 1) ⊕ Fin p) = 2 * p - 1 := by
      simp only [Fintype.card_sum, Fintype.card_fin]; omega
    rw [hκ, hrc, show a + (k - a) = k by omega] at hb
    refine hb.trans ?_
    have e1 : 2 * p - 1 + 1 = 2 * p := by omega
    rw [e1]
    have hz3 : (1 + ‖z‖) ^ (2 * p - 1) ≤ (2 * N) ^ (2 * p - 1) :=
      pow_le_pow_left₀ (by positivity) hz2 _
    have e2 : (2 * (N : ℝ)) ^ (2 * p - 1) * (N : ℝ) ^ (k + 1 + 3 * (2 * p - 1)) =
        2 ^ (2 * p - 1) * M ^ (2 * k + 16 * p - 6) := by
      rw [← hMsq, mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
      congr 2
      omega
    have h22 : (2 : ℝ) ^ (2 * p - 1) ≤ 2 ^ (2 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc c₁ ^ (2 * p) * (1 + ‖z‖) ^ (2 * p - 1) * (N : ℝ) ^ (k + 1 + 3 * (2 * p - 1))
        ≤ c₁ ^ (2 * p) * (2 * N) ^ (2 * p - 1) * (N : ℝ) ^ (k + 1 + 3 * (2 * p - 1)) := by
          gcongr
      _ = c₁ ^ (2 * p) * (2 ^ (2 * p - 1) * M ^ (2 * k + 16 * p - 6)) := by rw [mul_assoc, e2]
      _ ≤ c₁ ^ (2 * p) * (2 ^ (2 * p) * M ^ (2 * k + 16 * p - 6)) := by gcongr
      _ = B := by rw [hB]; ring
  -- the sum over `i, j`
  have hsum : ∑ i : Idx D N, ∑ _j : Idx D N, ‖u i‖ ≤ (D : ℝ) ^ 2 * M ^ 3 := by
    obtain ⟨h1, -⟩ := FIH_sums (fun i => ‖u i‖) (fun _ => (0 : ℝ)) D M 0 0
      (fun i => norm_nonneg _) hu (fun _ => le_rfl) (fun _ => le_rfl) (by simp)
      (by rw [hMsq]; simp [Fintype.card_prod, Fintype.card_fin]) hM0 le_rfl (by linarith) le_rfl
    have hc : ∑ _j : Idx D N, (1 : ℝ) = D * M ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hMsq]
      simp [Fintype.card_prod, Fintype.card_fin]
    have hsD : Real.sqrt D ≤ D := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    calc ∑ i : Idx D N, ∑ _j : Idx D N, ‖u i‖ = (∑ i, ‖u i‖) * ∑ _j : Idx D N, (1 : ℝ) := by
          rw [← FIH_dsum]; simp
      _ ≤ (Real.sqrt D * M) * (D * M ^ 2) := by
          rw [hc]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (D * M) * (D * M ^ 2) := by gcongr
      _ = _ := by ring
  have hB0 : 0 ≤ B := by positivity
  calc ∑ i, ∑ j, ‖u i‖ * ‖wirt a (k - a) (fun w =>
        (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
        (h j i)‖
      ≤ ∑ i : Idx D N, ∑ _j : Idx D N, ‖u i‖ * (((2 * p : ℕ) : ℝ) ^ k * B) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_left ((hL i j).trans ?_) (norm_nonneg _)
        calc _ ≤ ∑ _w : (Fin (k - a) → Option (Fin (p - 1) ⊕ Fin p)) ×
              (Fin a → Option (Fin (p - 1) ⊕ Fin p)), B := Finset.sum_le_sum fun w _ => hW w i j
          _ = _ := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, FIH_words p a (k - a) hp,
                show a + (k - a) = k by omega]
    _ = (∑ i : Idx D N, ∑ _j : Idx D N, ‖u i‖) * (((2 * p : ℕ) : ℝ) ^ k * B) := by
        simp only [Finset.sum_mul]
    _ ≤ ((D : ℝ) ^ 2 * M ^ 3) * (((2 * p : ℕ) : ℝ) ^ k * B) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ ≤ _ := by
        have hexp : M ^ 3 * M ^ (2 * k + 16 * p - 6) ≤ M ^ (k + 1) * M ^ (42 * p + 36) := by
          rw [← pow_add, ← pow_add]
          exact pow_le_pow_right₀ hM1 (by omega)
        have e : ((D : ℝ) ^ 2 * M ^ 3) * (((2 * p : ℕ) : ℝ) ^ k * B) =
            (((2 * p : ℕ) : ℝ) ^ k * ((D : ℝ) ^ 2 * c₁ ^ (2 * p) * 2 ^ (2 * p))) *
              (M ^ 3 * M ^ (2 * k + 16 * p - 6)) := by rw [hB]; ring
        have e' : M ^ (k + 1) * (((2 * p : ℕ) : ℝ) ^ k * ((D : ℝ) ^ 2 * c₁ ^ (2 * p) *
            2 ^ (2 * p))) * M ^ (42 * p + 36) =
            (((2 * p : ℕ) : ℝ) ^ k * ((D : ℝ) ^ 2 * c₁ ^ (2 * p) * 2 ^ (2 * p))) *
              (M ^ (k + 1) * M ^ (42 * p + 36)) := by ring
        rw [e, e']
        exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-! ### Integration -/

private lemma FIH_lsum {α X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Finset α)
    (f : α → X → ENNReal) : ∑ x ∈ s, ∫⁻ y, f x y ∂μ ≤ ∫⁻ y, ∑ x ∈ s, f x y ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc ∫⁻ y, f a y ∂μ + ∑ x ∈ s, ∫⁻ y, f x y ∂μ ≤ ∫⁻ y, f a y ∂μ + ∫⁻ y, ∑ x ∈ s, f x y ∂μ :=
          add_le_add le_rfl ih
      _ ≤ ∫⁻ y, (f a y + ∑ x ∈ s, f x y) ∂μ := le_lintegral_add _ _
      _ = _ := by simp only [Finset.sum_insert ha]

private lemma FIH_swap' {α β γ : Type*} [Fintype α] [Fintype β] (t : Finset γ)
    (f : α → β → γ → ℝ) :
    ∑ x, ∑ y, ∑ w ∈ t, f x y w = ∑ w ∈ t, ∑ x, ∑ y, f x y w := by
  calc _ = ∑ x, ∑ w ∈ t, ∑ y, f x y w := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- From a pointwise bound `Σ_{i,j} s_i ‖W_{ij}‖ ≤ Ψ` almost everywhere with `Ψ` integrable:
`Σ_{i,j} s_i ‖E W_{ij}‖ ≤ E Ψ`. -/
private lemma FIH_int_bound {ι X : Type*} [Fintype ι] [MeasurableSpace X] (μ : Measure X)
    (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (W : ι → ι → X → ℂ) (Ψ : X → ℝ) (hΨ : Integrable Ψ μ)
    (hpt : ∀ᵐ x ∂μ, ∑ i, ∑ j, s i * ‖W i j x‖ ≤ Ψ x) :
    ∑ i, ∑ j, s i * ‖∫ x, W i j x ∂μ‖ ≤ ∫ x, Ψ x ∂μ := by
  set L : ι → ι → ENNReal := fun i j => ∫⁻ x, ENNReal.ofReal (s i * ‖W i j x‖) ∂μ with hL
  have hΨ0 : 0 ≤ᵐ[μ] Ψ := hpt.mono fun x hx =>
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hs i) (norm_nonneg _)).trans hx
  have hsum : ∑ i, ∑ j, L i j ≤ ENNReal.ofReal (∫ x, Ψ x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hΨ hΨ0]
    calc ∑ i, ∑ j, L i j ≤ ∑ i, ∫⁻ x, ∑ j, ENNReal.ofReal (s i * ‖W i j x‖) ∂μ :=
          Finset.sum_le_sum fun i _ => FIH_lsum μ _ _
      _ ≤ ∫⁻ x, ∑ i, ∑ j, ENNReal.ofReal (s i * ‖W i j x‖) ∂μ := FIH_lsum μ _ _
      _ ≤ ∫⁻ x, ENNReal.ofReal (Ψ x) ∂μ := by
          refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
          have e : ∑ i, ∑ j, ENNReal.ofReal (s i * ‖W i j x‖) =
              ENNReal.ofReal (∑ i, ∑ j, s i * ‖W i j x‖) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
              mul_nonneg (hs i) (norm_nonneg _)]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hs i) (norm_nonneg _)]
          rw [e]
          exact ENNReal.ofReal_le_ofReal hx
  have hfin : ∑ i, ∑ j, L i j ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  have hfin1 : ∀ i, ∑ j, L i j ≠ ⊤ := fun i =>
    ENNReal.sum_ne_top.mp hfin i (Finset.mem_univ i)
  have hfin2 : ∀ i j, L i j ≠ ⊤ := fun i j =>
    ENNReal.sum_ne_top.mp (hfin1 i) j (Finset.mem_univ j)
  have hpt2 : ∀ i j, s i * ‖∫ x, W i j x ∂μ‖ ≤ (L i j).toReal := by
    intro i j
    have h1 := norm_integral_le_lintegral_norm (μ := μ) (W i j)
    have e : L i j = ENNReal.ofReal (s i) * ∫⁻ x, ENNReal.ofReal ‖W i j x‖ ∂μ := by
      rw [hL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x => ?_
      exact ENNReal.ofReal_mul (hs i)
    rw [e, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hs i)]
    exact mul_le_mul_of_nonneg_left h1 (hs i)
  calc ∑ i, ∑ j, s i * ‖∫ x, W i j x ∂μ‖ ≤ ∑ i, ∑ j, (L i j).toReal :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt2 i j
    _ = (∑ i, ∑ j, L i j).toReal := by
        rw [ENNReal.toReal_sum fun i _ => hfin1 i]
        exact Finset.sum_congr rfl fun i _ =>
          (ENNReal.toReal_sum fun j _ => hfin2 i j).symm
    _ ≤ (ENNReal.ofReal (∫ x, Ψ x ∂μ)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    _ = ∫ x, Ψ x ∂μ := ENNReal.toReal_ofReal (integral_nonneg_of_ae hΨ0)

private lemma FIH_sqrt_le (m e : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hme : m ≤ e) :
    m ≤ Real.sqrt e := by
  rw [Real.le_sqrt hm0 (hm0.trans hme)]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- The order-`k` part of the isotropic moment inequality for `2 ≤ k ≤ 16p + 16` (cumulants of
order `≥ 3`, up to the order at which the expansion is truncated):
`≤ K Σ_{n=1}^{2p} (ζ̂ λ²)^{n/3} E|(H̲G)_{uv}|^{2p-n}` plus the bad-event term. -/
theorem iso_order_high' (D p k : ℕ) (hp : 1 ≤ p) (hk : 2 ≤ k) (hk' : k ≤ 16 * p + 16)
    (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ z : ℂ, ((N : ℝ))⁻¹ ≤ z.im → ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) →
      ∀ u v : Idx D N → ℂ, ∑ k, ‖u k‖ ^ 2 ≤ 1 → ∑ k, ‖v k‖ ^ 2 ≤ 1 →
      ∀ Γ Υ lb ε₀ : ℝ, 1 ≤ Γ → Γ ≤ (N : ℝ) ^ ((1 : ℝ) / 6) → z.im ≤ Υ →
        Υ ≤ (N : ℝ) * z.im →
        (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ≤ lb →
        μ (isoGood D N θ Λ z u v Γ Υ lb)ᶜ ≤ ENNReal.ofReal ε₀ →
        ‖isoTerm D N θ μ Λ z u v p k‖ ≤
          K * (∑ n ∈ Finset.Icc 1 (2 * p),
              ((Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) *
                lb ^ 2) ^ ((n : ℝ) / 3) *
              ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - n) ∂μ) +
            K * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ := by
  classical
  choose cW hcW0 hcW using fun a b => hgUnder_wirt_le D a b
  set cWs : ℝ := ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1), cW a b with hcWs
  have hcWs0 : 0 ≤ cWs := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hcW0 a b
  set c₁ : ℝ := 12 + 2 * ((k + 1 : ℕ) : ℝ) ^ (k + 1) + (k + 1) * cWs with hc₁
  have hc0 : 0 ≤ c₁ := by positivity
  choose Kc hKc using fun a : ℕ => llClass_ccum_le C a (k - a + 1)
  set Kcs : ℝ := ∑ a ∈ Finset.range (k + 1), |Kc a| with hKcs
  have hKcs0 : 0 ≤ Kcs := Finset.sum_nonneg fun a _ => abs_nonneg _
  set K₁ : ℝ := ((2 * p : ℕ) : ℝ) ^ k * (20 * D * c₁ ^ (k + 1)) with hK₁
  set K₂ : ℝ := ((2 * p : ℕ) : ℝ) ^ k * ((D : ℝ) ^ 2 * c₁ ^ (2 * p) * 2 ^ (2 * p)) with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hK0 : 0 ≤ Kcs * (K₁ + K₂) := mul_nonneg hKcs0 (add_nonneg hK₁0 hK₂0)
  refine ⟨Kcs * (K₁ + K₂), hK0, ?_⟩
  intro N θ μ hμ hθ0 hθ1 Λ hΛ hΛn z hzN hzn u v hu hv Γ Υ lb ε₀ hΓ hΓN hΥ hΥ2 hlb hε
  have hprob := hμ.prob
  set X := (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) * lb ^ 2
    with hXdef
  set δ : (Idx D N → Idx D N → ℂ) → ℝ :=
    fun h => ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ with hδ
  set S := ∑ n ∈ Finset.Icc 1 (2 * p), X ^ ((n : ℝ) / 3) * ∫ h, δ h ^ (2 * p - n) ∂μ with hS
  have hX0 : 0 ≤ X := by
    have : 0 ≤ Γ := by linarith
    positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ =>
    mul_nonneg (Real.rpow_nonneg hX0 _) (integral_nonneg fun h => by positivity)
  have hP0 : 0 ≤ (N : ℝ) ^ (21 * (p : ℝ) + 18) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hR0 : 0 ≤ Kcs * (K₁ + K₂) * S + Kcs * (K₁ + K₂) * (N : ℝ) ^ (21 * (p : ℝ) + 18) *
      Real.sqrt ε₀ :=
    add_nonneg (mul_nonneg hK0 hS0) (mul_nonneg (mul_nonneg hK0 hP0) (Real.sqrt_nonneg _))
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · -- no indices
    haveI : IsEmpty (Idx D N) := by subst hD0; infer_instance
    have h0 : isoTerm D N θ μ Λ z u v p k = 0 := Fintype.sum_empty _
    rw [h0, norm_zero]
    exact hR0
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hDpos
  have hN1 : (1 : ℝ) ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0, Nat.cast_zero, Real.zero_rpow (by norm_num)] at hΓN
      linarith
    · exact_mod_cast h0
  have hN0 : (0 : ℝ) < N := by linarith
  have hz : 0 < z.im := lt_of_lt_of_le (inv_pos.mpr hN0) hzN
  have hΓM : Γ ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact hΓN.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
  have hznN : ‖z‖ ≤ N := by
    calc ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) := hzn
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have hivn := FIH_iv_norm D N θ hθ0 hθ1 Λ hΛ hΛn u v hu hv
  -- the generic bound on the derivatives of `(H̲G)_{uv}` (`hgUnder_wirt_le`)
  have hgen : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      ∀ (i j : Idx D N) (Γ' Υ' : ℝ), 1 ≤ Γ' → z.im ≤ Υ' →
        h ∈ goodSet Λ z (isoVecs D N θ Λ u v) Γ' Υ' → ∀ l ≤ k,
        FIH_bnd (FIH_Hs D N θ h Λ z u v j i) (h j i) l ≤
          (k + 1) * cWs * (1 + ‖z‖) * Γ' ^ (l + 2) * Real.sqrt (Υ' / z.im) := by
    intro h hh i j Γ' Υ' hΓ' hΥ' hg' l hl
    have hse := FIH_setEntry_self h hh j i
    have hΓ'0 : 0 ≤ Γ' := by linarith
    have hB := FIH_bnd_le (FIH_Hs D N θ h Λ z u v j i) (h j i) l
      (cWs * (1 + ‖z‖) * Γ' ^ (l + 2) * Real.sqrt (Υ' / z.im)) fun α hα => by
        have h1 := hcW α (l - α) N θ hθ0 hθ1 Λ hΛ hΛn z hz h hh j i (h j i) u v
          (isoVecs D N θ Λ u v) Γ' Υ' (FIH_iv_u D N θ Λ u v) (FIH_iv_v D N θ Λ u v)
          (FIH_iv_e D N θ Λ u v) (FIH_iv_t D N θ Λ u v) hivn hΓ' hΥ' (by rw [hse]; exact hg')
        have e : α + (l - α) = l := by omega
        rw [e] at h1
        have h2 : cW α (l - α) ≤ cWs := by
          have h3 := Finset.single_le_sum (f := fun b => cW α b) (fun b _ => hcW0 α b)
            (Finset.mem_range.mpr (show l - α < k + 1 by omega))
          exact h3.trans (Finset.single_le_sum
            (f := fun a => ∑ b ∈ Finset.range (k + 1), cW a b)
            (fun a _ => Finset.sum_nonneg fun b _ => hcW0 a b)
            (Finset.mem_range.mpr (show α < k + 1 by omega)))
        have h3 : 0 ≤ (1 + ‖z‖) * Γ' ^ (l + 2) * Real.sqrt (Υ' / z.im) := by positivity
        calc _ ≤ cW α (l - α) * (1 + ‖z‖) * Γ' ^ (l + 2) * Real.sqrt (Υ' / z.im) := h1
          _ = cW α (l - α) * ((1 + ‖z‖) * Γ' ^ (l + 2) * Real.sqrt (Υ' / z.im)) := by ring
          _ ≤ cWs * ((1 + ‖z‖) * Γ' ^ (l + 2) * Real.sqrt (Υ' / z.im)) :=
              mul_le_mul_of_nonneg_right h2 h3
          _ = _ := by ring
    refine hB.trans ?_
    have h4 : 0 ≤ cWs * (1 + ‖z‖) * Γ' ^ (l + 2) * Real.sqrt (Υ' / z.im) := by positivity
    have h5 : (l : ℝ) + 1 ≤ k + 1 := by exact_mod_cast (show l + 1 ≤ k + 1 by omega)
    calc ((l : ℝ) + 1) * (cWs * (1 + ‖z‖) * Γ' ^ (l + 2) * Real.sqrt (Υ' / z.im))
        ≤ ((k : ℝ) + 1) * (cWs * (1 + ‖z‖) * Γ' ^ (l + 2) * Real.sqrt (Υ' / z.im)) :=
          mul_le_mul_of_nonneg_right h5 h4
      _ = _ := by ring
  -- the good event, a measurable cover of its complement, and the majorant `Ψ`
  set Ω := isoGood D N θ Λ z u v Γ Υ lb with hΩ
  set T := toMeasurable μ Ωᶜ with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable μ Ωᶜ
  have hΩT : Ωᶜ ⊆ T := subset_toMeasurable μ Ωᶜ
  set M := Real.sqrt N with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  set Ψ : (Idx D N → Idx D N → ℂ) → ℝ := fun h =>
    K₁ * (∑ n ∈ Finset.Icc 1 (2 * p), X ^ ((n : ℝ) / 3) * δ h ^ (2 * p - n)) +
      K₂ * M ^ (42 * p + 36) * T.indicator (fun _ => (1 : ℝ)) h with hΨ
  have hδm : Measurable δ := FIH_hg_meas θ Λ z u v
  have hδb : ∀ᵐ h ∂μ, δ h ≤ 1 + (opNorm Λ + ‖z‖) / z.im + 1 / z.im ^ 2 :=
    hμ.herm.mono fun h hh => hgUnder_form_le D N θ hθ0 hθ1 _ Λ hh hΛ z hz u v hu hv
  have hδq : ∀ q : ℕ, Integrable (fun h => δ h ^ q) μ := fun q =>
    Integrable.of_bound (hδm.pow_const q).aestronglyMeasurable
      ((1 + (opNorm Λ + ‖z‖) / z.im + 1 / z.im ^ 2) ^ q) (hδb.mono fun h hb => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) hb q)
  have hI1 : Integrable (fun h => K₁ * ∑ n ∈ Finset.Icc 1 (2 * p),
      X ^ ((n : ℝ) / 3) * δ h ^ (2 * p - n)) μ :=
    (integrable_finsetSum _ fun n _ => (hδq _).const_mul _).const_mul _
  have hI2 : Integrable (fun h => K₂ * M ^ (42 * p + 36) * T.indicator (fun _ => (1 : ℝ)) h) μ :=
    ((integrable_const (1 : ℝ)).indicator hTm).const_mul _
  have hΨi : Integrable Ψ μ := hI1.add hI2
  -- the bound for each order `a` of `∂_w`
  have hBa : ∀ a ∈ Finset.range (k + 1), ∑ i, ∑ j, ‖u i‖ * ‖∫ h, wirt a (k - a) (fun w =>
        (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
        (h j i) ∂μ‖ ≤ M ^ (k + 1) * ∫ h, Ψ h ∂μ := by
    intro a ha
    have ha' : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [← integral_const_mul]
    refine FIH_int_bound μ (fun i => ‖u i‖) (fun i => norm_nonneg _) _ _
      (hΨi.const_mul _) ?_
    filter_upwards [hμ.herm] with h hh
    have hind0 : 0 ≤ T.indicator (fun _ => (1 : ℝ)) h :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) h
    have hsum0 : 0 ≤ ∑ n ∈ Finset.Icc 1 (2 * p), X ^ ((n : ℝ) / 3) * δ h ^ (2 * p - n) :=
      Finset.sum_nonneg fun n _ => mul_nonneg (Real.rpow_nonneg hX0 _) (by positivity)
    by_cases hg : h ∈ Ω
    · refine (FIH_pt_good D N p k a hp hk ha' θ hθ0 hθ1 Λ hΛ hΛn z hz u v hu hv Γ Υ lb hD1 hΓ hΓM
        hΥ hΥ2 hlb cWs c₁ le_rfl hcWs0 hgen h hh hg).trans ?_
      have : 0 ≤ K₂ * M ^ (42 * p + 36) * T.indicator (fun _ => (1 : ℝ)) h := by positivity
      calc M ^ (k + 1) * K₁ * ∑ n ∈ Finset.Icc 1 (2 * p), X ^ ((n : ℝ) / 3) * δ h ^ (2 * p - n)
          = M ^ (k + 1) * (K₁ * ∑ n ∈ Finset.Icc 1 (2 * p),
              X ^ ((n : ℝ) / 3) * δ h ^ (2 * p - n)) := by ring
        _ ≤ M ^ (k + 1) * Ψ h := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            simp only [hΨ]
            linarith
    · refine (FIH_pt_bad D N p k a hp hk' ha' θ hθ0 hθ1 Λ hΛ hΛn z hz u v hu hv hD1 hN1 hzN hznN
        cWs c₁ le_rfl hcWs0 hgen h hh).trans ?_
      have hT1 : T.indicator (fun _ => (1 : ℝ)) h = 1 := Set.indicator_of_mem (hΩT hg) _
      have : 0 ≤ K₁ * ∑ n ∈ Finset.Icc 1 (2 * p), X ^ ((n : ℝ) / 3) * δ h ^ (2 * p - n) :=
        mul_nonneg hK₁0 hsum0
      calc M ^ (k + 1) * K₂ * M ^ (42 * p + 36)
          = M ^ (k + 1) * (K₂ * M ^ (42 * p + 36) * 1) := by ring
        _ ≤ M ^ (k + 1) * Ψ h := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            simp only [hΨ, hT1]
            linarith
  -- `‖isoTerm‖ ≤ Σ_a |K_a| E Ψ`
  set ν := (N : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) / 2)) with hν
  have hν0 : 0 ≤ ν := Real.rpow_nonneg hN0.le _
  have hνM : ν * M ^ (k + 1) = 1 := by
    rw [hν, hM, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      ← Real.rpow_add hN0]
    have e : -(((k + 1 : ℕ) : ℝ) / 2) + 1 / 2 * ((k + 1 : ℕ) : ℝ) = 0 := by ring
    rw [e, Real.rpow_zero]
  have hcc : ∀ a ∈ Finset.range (k + 1), ∀ i j : Idx D N,
      ‖ccum (μ.map fun h => h j i) a (k - a + 1) /
        ((a.factorial * (k - a).factorial : ℕ) : ℂ)‖ ≤ |Kc a| * ν := by
    intro a ha i j
    have ha' : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have h1 := hKc a D N θ μ hμ j i
    have e : a + (k - a + 1) = k + 1 := by omega
    rw [e] at h1
    rw [norm_div]
    have hf : (1 : ℝ) ≤ ‖((a.factorial * (k - a).factorial : ℕ) : ℂ)‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
    calc _ ≤ ‖ccum (μ.map fun h => h j i) a (k - a + 1)‖ := div_le_self (norm_nonneg _) hf
      _ ≤ Kc a * ν := h1
      _ ≤ |Kc a| * ν := mul_le_mul_of_nonneg_right (le_abs_self _) hν0
  have hC : ‖isoTerm D N θ μ Λ z u v p k‖ ≤ Kcs * ∫ h, Ψ h ∂μ := by
    unfold isoTerm
    calc _ ≤ ∑ i, ∑ j, ‖u i‖ * ∑ a ∈ Finset.range (k + 1), |Kc a| * ν * ‖∫ h, wirt a (k - a)
          (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
            (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
            starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
          (h j i) ∂μ‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun j _ => ?_))
          rw [norm_mul, Complex.norm_conj]
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun a ha => ?_)) (norm_nonneg _)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hcc a ha i j) (norm_nonneg _)
      _ = ∑ a ∈ Finset.range (k + 1), |Kc a| * ν * ∑ i, ∑ j, ‖u i‖ * ‖∫ h, wirt a (k - a)
          (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
            (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
            starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
          (h j i) ∂μ‖ := by
          simp only [Finset.mul_sum]
          refine (FIH_swap' _ _).trans (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl
            fun i _ => Finset.sum_congr rfl fun j _ => by ring)
      _ ≤ ∑ a ∈ Finset.range (k + 1), |Kc a| * ν * (M ^ (k + 1) * ∫ h, Ψ h ∂μ) :=
          Finset.sum_le_sum fun a ha =>
            mul_le_mul_of_nonneg_left (hBa a ha) (mul_nonneg (abs_nonneg _) hν0)
      _ = _ := by
          rw [hKcs, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [show |Kc a| * ν * (M ^ (k + 1) * ∫ h, Ψ h ∂μ) =
            |Kc a| * (ν * M ^ (k + 1)) * ∫ h, Ψ h ∂μ by ring, hνM, mul_one]
  -- `E Ψ`
  have hint : ∫ h, Ψ h ∂μ = K₁ * S + K₂ * M ^ (42 * p + 36) * μ.real T := by
    rw [integral_add hI1 hI2, integral_const_mul, integral_finsetSum _ fun n _ =>
      (hδq _).const_mul _, integral_const_mul, integral_indicator_const _ hTm, smul_eq_mul,
      mul_one, hS]
    congr 2
    exact Finset.sum_congr rfl fun n _ => integral_const_mul _ _
  have hMp : M ^ (42 * p + 36) = (N : ℝ) ^ (21 * (p : ℝ) + 18) := by
    rw [show 42 * p + 36 = 2 * (21 * p + 18) by ring, pow_mul, hM, Real.sq_sqrt hN0.le,
      ← Real.rpow_natCast]
    push_cast
    ring_nf
  have hTr : μ.real T ≤ Real.sqrt ε₀ := by
    have hμT : μ T ≤ ENNReal.ofReal ε₀ := by rw [hT, measure_toMeasurable]; exact hε
    rw [measureReal_def]
    by_cases he : ε₀ ≤ 0
    · rw [ENNReal.ofReal_of_nonpos he, nonpos_iff_eq_zero] at hμT
      rw [hμT, ENNReal.toReal_zero]
      exact Real.sqrt_nonneg _
    · push_neg at he
      refine FIH_sqrt_le _ _ ENNReal.toReal_nonneg ?_ (ENNReal.toReal_le_of_le_ofReal he.le hμT)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  rw [hint, hMp] at hC
  have hm0 : 0 ≤ μ.real T := measureReal_nonneg
  have t1 : Kcs * (K₂ * (N : ℝ) ^ (21 * (p : ℝ) + 18) * μ.real T) ≤
      Kcs * (K₂ * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTr (mul_nonneg hK₂0 hP0)) hKcs0
  have t2 : 0 ≤ Kcs * K₂ * S := mul_nonneg (mul_nonneg hKcs0 hK₂0) hS0
  have t3 : 0 ≤ Kcs * K₁ * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ :=
    mul_nonneg (mul_nonneg (mul_nonneg hKcs0 hK₁0) hP0) (Real.sqrt_nonneg _)
  calc ‖isoTerm D N θ μ Λ z u v p k‖
      ≤ Kcs * (K₁ * S + K₂ * (N : ℝ) ^ (21 * (p : ℝ) + 18) * μ.real T) := hC
    _ ≤ Kcs * (K₁ + K₂) * S + Kcs * (K₁ + K₂) * (N : ℝ) ^ (21 * (p : ℝ) + 18) *
        Real.sqrt ε₀ := by nlinarith

end RBMTransitionEdge

end
