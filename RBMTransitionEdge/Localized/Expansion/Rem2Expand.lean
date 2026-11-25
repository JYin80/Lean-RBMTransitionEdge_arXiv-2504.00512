module

public import RBMTransitionEdge.Localized.Expansion.PkgEval
public import RBMTransitionEdge.Localized.Expansion.Bound

@[expose] public section

/-!
# The expansion of the remainder of the further expansion into derivative structures

The remainder `𝓔^{(2)}_𝓡(p, q)` of (5.83) [concrete_expansion_tl_2_heavy_package_right] and
(5.84) [concrete_expansion_tl_2_loop] as a sum of the expectations of the derivative structures of
(5.66) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression], with the labels `2 ↦ i`, `3 ↦ j`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Functions of the array: smooth through the Hermitian part and bounded on Hermitian arrays -/

/-- `f ∘ symArr` is real-differentiable and `f` is bounded on Hermitian arrays. -/
private def R2_good {D N : ℕ} (f : (Idx D N → Idx D N → ℂ) → ℂ) : Prop :=
  Differentiable ℝ (fun h => f (symArr h)) ∧
    ∃ C : ℝ, ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → ‖f h‖ ≤ C

private lemma R2_good_const {D N : ℕ} (c : ℂ) :
    R2_good (D := D) (N := N) fun _ => c :=
  ⟨differentiable_const _, ‖c‖, fun _ _ => le_rfl⟩

private lemma R2_good_add {D N : ℕ} {f g : (Idx D N → Idx D N → ℂ) → ℂ}
    (hf : R2_good f) (hg : R2_good g) : R2_good fun h => f h + g h := by
  obtain ⟨d1, C1, b1⟩ := hf
  obtain ⟨d2, C2, b2⟩ := hg
  exact ⟨d1.add d2, C1 + C2, fun h hh => (norm_add_le _ _).trans (add_le_add (b1 h hh) (b2 h hh))⟩

private lemma R2_good_mul {D N : ℕ} {f g : (Idx D N → Idx D N → ℂ) → ℂ}
    (hf : R2_good f) (hg : R2_good g) : R2_good fun h => f h * g h := by
  obtain ⟨d1, C1, b1⟩ := hf
  obtain ⟨d2, C2, b2⟩ := hg
  refine ⟨d1.mul d2, C1 * C2, fun h hh => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (b1 h hh) (b2 h hh) (norm_nonneg _) ((norm_nonneg _).trans (b1 h hh))

private lemma R2_good_sub {D N : ℕ} {f g : (Idx D N → Idx D N → ℂ) → ℂ}
    (hf : R2_good f) (hg : R2_good g) : R2_good fun h => f h - g h := by
  have := R2_good_add hf (R2_good_mul (R2_good_const (-1)) hg)
  simpa [sub_eq_add_neg] using this

private lemma R2_good_sum {D N : ℕ} {α : Type*} (s : Finset α)
    (F : α → (Idx D N → Idx D N → ℂ) → ℂ) (hF : ∀ a ∈ s, R2_good (F a)) :
    R2_good fun h => ∑ a ∈ s, F a h := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using R2_good_const (D := D) (N := N) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact R2_good_add (hF a (Finset.mem_insert_self a s))
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

private lemma R2_good_prod {D N : ℕ} {α : Type*} (F : α → (Idx D N → Idx D N → ℂ) → ℂ) :
    ∀ L : List α, (∀ a ∈ L, R2_good (F a)) → R2_good fun h => (L.map fun a => F a h).prod
  | [], _ => by simpa using R2_good_const (D := D) (N := N) 1
  | a :: L, hL => by
    simp only [List.map_cons, List.prod_cons]
    exact R2_good_mul (hL a List.mem_cons_self)
      (R2_good_prod F L fun b hb => hL b (List.mem_cons_of_mem _ hb))

/-- Every entry of a matrix-valued function of the array is `R2_good`. -/
private def R2_goodM {D N : ℕ} (M : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ) :
    Prop :=
  ∀ k l, R2_good fun h => M h k l

private lemma R2_goodM_const {D N : ℕ} (X : Matrix (Idx D N) (Idx D N) ℂ) :
    R2_goodM fun _ => X :=
  fun k l => R2_good_const (X k l)

private lemma R2_goodM_mul {D N : ℕ}
    {A B : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ}
    (hA : R2_goodM A) (hB : R2_goodM B) : R2_goodM fun h => A h * B h := by
  intro k l
  simp only [Matrix.mul_apply]
  exact R2_good_sum _ _ fun m _ => R2_good_mul (hA k m) (hB m l)

private lemma R2_goodM_sub {D N : ℕ}
    {A B : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ}
    (hA : R2_goodM A) (hB : R2_goodM B) : R2_goodM fun h => A h - B h := by
  intro k l
  simp only [Matrix.sub_apply]
  exact R2_good_sub (hA k l) (hB k l)

private lemma R2_good_trace {D N : ℕ}
    {A : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ} (hA : R2_goodM A) :
    R2_good fun h => (A h).trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact R2_good_sum _ _ fun k _ => hA k k

private lemma R2_good_ntr {D N : ℕ}
    {A : (Idx D N → Idx D N → ℂ) → Matrix (Idx D N) (Idx D N) ℂ} (hA : R2_goodM A) :
    R2_good fun h => ntr (A h) := by
  unfold ntr
  exact R2_good_mul (R2_good_const _) (R2_good_trace hA)

/-- An entry of a matrix is bounded by the operator norm. -/
private lemma R2_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (i j : ι) : ‖A i j‖ ≤ opNorm A := by
  unfold opNorm
  have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  have h2 : ‖(EuclideanSpace.single j (1 : ℂ))‖ = 1 := by simp
  rw [h2, mul_one] at h1
  have h3 : A i j = ((Matrix.toEuclideanCLM (𝕜 := ℂ) A) (EuclideanSpace.single j (1 : ℂ))) i := by
    simp [Matrix.mulVec_single]
  rw [h3]
  exact (PiLp.norm_apply_le _ i).trans h1

/-- The entries of the resolvent of a Hermitian matrix are bounded by `|Im ξ|⁻¹`. -/
private lemma R2_res_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (ξ : ℂ) (hξ : ξ.im ≠ 0) (k l : ι) : ‖res X ξ k l‖ ≤ |ξ.im|⁻¹ := by
  rcases lt_or_gt_of_ne hξ with hneg | hpos
  · have hζ : 0 < (starRingEnd ℂ ξ).im := by simpa using hneg
    have e := res_conj X hX (starRingEnd ℂ ξ) hζ
    rw [Complex.conj_conj] at e
    rw [e, Matrix.conjTranspose_apply, norm_star]
    refine (R2_entry_le _ l k).trans ((opNorm_res_le X hX _ hζ).trans (le_of_eq ?_))
    simp [abs_of_neg hneg]
  · refine (R2_entry_le _ k l).trans ((opNorm_res_le X hX _ hpos).trans (le_of_eq ?_))
    rw [abs_of_pos hpos]

/-- The entries of a resolvent with a Hermitian deformation `Λ` and `Im ξ ≠ 0`. -/
private lemma R2_goodM_res {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (ξ : ℂ) (hξ : ξ.im ≠ 0) : R2_goodM fun h => res (Matrix.of h + Λ) ξ := by
  intro k l
  refine ⟨(contDiff_res_symArr Λ hΛ ξ hξ k l 1).differentiable (by norm_num), |ξ.im|⁻¹,
    fun h hh => R2_res_entry_le _ (hh.add hΛ) ξ hξ k l⟩

/-- A `R2_good` function is integrable for a probability law of almost surely Hermitian
arrays. -/
private lemma R2_good_integrable {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian)
    {f : (Idx D N → Idx D N → ℂ) → ℂ} (hf : R2_good f) : Integrable f μ := by
  obtain ⟨hd, C, hC⟩ := hf
  have hae : (fun h => f (symArr h)) =ᵐ[μ] f := by
    filter_upwards [hμ] with h hh
    rw [symArr_of_isHermitian h hh]
  refine Integrable.of_bound (hd.continuous.aestronglyMeasurable.congr hae) C ?_
  filter_upwards [hμ] with h hh
  exact hC h hh

/-- The one-entry slice `w ↦ setEntry h i j w` is real-differentiable. -/
private lemma R2_slice_diff {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) :
    Differentiable ℝ (fun w : ℂ => setEntry h i j w) := by
  refine differentiable_pi.2 fun k => differentiable_pi.2 fun l => ?_
  have hre : Differentiable ℝ (fun w : ℂ => ((w.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp Complex.reCLM.differentiable
  have hcj : Differentiable ℝ (fun w : ℂ => starRingEnd ℂ w) := Complex.conjCLE.differentiable
  unfold setEntry
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = i ∧ l = i
    · simpa [hkl] using hre
    · simp [hkl]
  · by_cases h1 : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hij]
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        simpa [hij, Ne.symm hij] using hcj
      · simp [hij, h1, h2]

/-- Along a slice through a Hermitian array, a `R2_good` function is real-differentiable. -/
private lemma R2_good_slice {D N : ℕ} {f : (Idx D N → Idx D N → ℂ) → ℂ} (hf : R2_good f)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    Differentiable ℝ (fun w => f (setEntry h i j w)) := by
  have e : (fun w => f (setEntry h i j w)) = (fun h' => f (symArr h')) ∘
      fun w => setEntry h i j w := by
    funext w
    simp only [Function.comp, symArr_setEntry, symArr_of_isHermitian h hh]
  rw [e]
  exact hf.1.comp (R2_slice_diff h i j)

/-! ### The rules shared by the Wirtinger derivatives `∂_w`, `∂_w̄` -/

/-- Additivity, the product rule and the derivative of a constant, at points where the
functions are real-differentiable. -/
private structure R2_Op (Dop : (ℂ → ℂ) → ℂ → ℂ) : Prop where
  add : ∀ {f g : ℂ → ℂ} {w : ℂ}, DifferentiableAt ℝ f w → DifferentiableAt ℝ g w →
    Dop (fun x => f x + g x) w = Dop f w + Dop g w
  mul : ∀ {f g : ℂ → ℂ} {w : ℂ}, DifferentiableAt ℝ f w → DifferentiableAt ℝ g w →
    Dop (fun x => f x * g x) w = Dop f w * g w + f w * Dop g w
  const : ∀ c w : ℂ, Dop (fun _ => c) w = 0

private lemma R2_op_dW : R2_Op dW where
  add {f g w} hf hg := by
    have e : fderiv ℝ (fun x => f x + g x) w = fderiv ℝ f w + fderiv ℝ g w :=
      fderiv_fun_add hf hg
    simp only [dW, e, _root_.add_apply]
    ring
  mul hf hg := (dW_mul hf hg).1
  const c w := by simp [dW]

private lemma R2_op_dWbar : R2_Op dWbar where
  add {f g w} hf hg := by
    have e : fderiv ℝ (fun x => f x + g x) w = fderiv ℝ f w + fderiv ℝ g w :=
      fderiv_fun_add hf hg
    simp only [dWbar, e, _root_.add_apply]
    ring
  mul hf hg := (dW_mul hf hg).2
  const c w := by simp [dWbar]

private lemma R2_Op.cmul {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) {f : ℂ → ℂ} {w : ℂ} (k : ℂ)
    (hf : DifferentiableAt ℝ f w) : Dop (fun x => k * f x) w = k * Dop f w := by
  rw [hO.mul (f := fun _ => k) (g := f) (differentiableAt_const k) hf, hO.const]
  ring

private lemma R2_Op.sum {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) {α : Type*} (s : Finset α)
    (F : α → ℂ → ℂ) {w : ℂ} (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) w) :
    Dop (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, Dop (F a) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hO.const 0 w
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [hO.add (f := F a) (g := fun x => ∑ b ∈ s, F b x) (hF a (Finset.mem_insert_self a s))
      (DifferentiableAt.fun_sum fun b hb => hF b (Finset.mem_insert_of_mem hb)),
      ih fun b hb => hF b (Finset.mem_insert_of_mem hb)]

private lemma R2_Op.lsum {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) {α : Type*}
    (F : α → ℂ → ℂ) {w : ℂ} :
    ∀ L : List α, (∀ a ∈ L, DifferentiableAt ℝ (F a) w) →
      Dop (fun x => (L.map fun a => F a x).sum) w = (L.map fun a => Dop (F a) w).sum
  | [], _ => by simpa using hO.const 0 w
  | a :: L, hL => by
    have hd : DifferentiableAt ℝ (fun x => (L.map fun b => F b x).sum) w := by
      have : ∀ L' : List α, (∀ b ∈ L', DifferentiableAt ℝ (F b) w) →
          DifferentiableAt ℝ (fun x => (L'.map fun b => F b x).sum) w := by
        intro L' hL'
        induction L' with
        | nil => simp
        | cons b L' ih =>
          simp only [List.map_cons, List.sum_cons]
          exact (hL' b List.mem_cons_self).add (ih fun c hc => hL' c (List.mem_cons_of_mem _ hc))
      exact this L fun b hb => hL b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons]
    rw [hO.add (f := F a) (g := fun x => (L.map fun b => F b x).sum) (hL a List.mem_cons_self) hd,
      R2_Op.lsum hO F L fun b hb => hL b (List.mem_cons_of_mem _ hb)]

/-- A product over a list is differentiable when its factors are. -/
private lemma R2_diff_prod {α : Type*} (F : α → ℂ → ℂ) {w : ℂ} :
    ∀ L : List α, (∀ a ∈ L, DifferentiableAt ℝ (F a) w) →
      DifferentiableAt ℝ (fun x => (L.map fun a => F a x).prod) w
  | [], _ => by simp
  | a :: L, hL => by
    simp only [List.map_cons, List.prod_cons]
    exact (hL a List.mem_cons_self).mul
      (R2_diff_prod F L fun b hb => hL b (List.mem_cons_of_mem _ hb))

/-- The product rule over a list: one term per factor, the derivative of that factor times the
product of the others. -/
private lemma R2_Op.prod {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) {α : Type*}
    (F : α → ℂ → ℂ) {w : ℂ} :
    ∀ L : List α, (∀ a ∈ L, DifferentiableAt ℝ (F a) w) →
      Dop (fun x => (L.map fun a => F a x).prod) w =
        ((List.range L.length).map fun ℓ =>
          (L[ℓ]?.map fun a => Dop (F a) w * ((L.eraseIdx ℓ).map fun b => F b w).prod).getD 0).sum
  | [], _ => by simpa using hO.const 1 w
  | a :: L, hL => by
    have hL' : ∀ b ∈ L, DifferentiableAt ℝ (F b) w := fun b hb => hL b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.prod_cons]
    rw [hO.mul (f := F a) (g := fun x => (L.map fun b => F b x).prod) (hL a List.mem_cons_self)
      (R2_diff_prod F L hL'), R2_Op.prod hO F L hL', List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.sum_cons, List.map_map]
    congr 1
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun ℓ _ => ?_
    simp only [Function.comp, List.getElem?_cons_succ, List.eraseIdx_cons_succ, List.map_cons,
      List.prod_cons]
    cases L[ℓ]? <;> simp only [Option.map_none, Option.map_some, Option.getD_none,
      Option.getD_some, mul_zero]
    ring

/-! ### Matrices along the slice -/

/-- The entrywise derivative of a matrix-valued function of one complex variable. -/
private def R2_dM (Dop : (ℂ → ℂ) → ℂ → ℂ) {ι : Type*} (M : ℂ → Matrix ι ι ℂ) (w : ℂ) :
    Matrix ι ι ℂ :=
  Matrix.of fun k l => Dop (fun x => M x k l) w

private lemma R2_dM_const {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) {ι : Type*}
    (X : Matrix ι ι ℂ) (w : ℂ) : R2_dM Dop (fun _ => X) w = 0 := by
  ext k l
  simp [R2_dM, hO.const]

private lemma R2_diffM_mul {ι : Type*} [Fintype ι] {A B : ℂ → Matrix ι ι ℂ} {w : ℂ}
    (hA : ∀ k l, DifferentiableAt ℝ (fun x => A x k l) w)
    (hB : ∀ k l, DifferentiableAt ℝ (fun x => B x k l) w) :
    ∀ k l, DifferentiableAt ℝ (fun x => (A x * B x) k l) w := by
  intro k l
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun m _ => (hA k m).mul (hB m l)

private lemma R2_dM_mul {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) {ι : Type*} [Fintype ι]
    {A B : ℂ → Matrix ι ι ℂ} {w : ℂ}
    (hA : ∀ k l, DifferentiableAt ℝ (fun x => A x k l) w)
    (hB : ∀ k l, DifferentiableAt ℝ (fun x => B x k l) w) :
    R2_dM Dop (fun x => A x * B x) w = R2_dM Dop A w * B w + A w * R2_dM Dop B w := by
  ext k l
  simp only [R2_dM, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [hO.sum Finset.univ (fun m x => A x k m * B x m l) fun m _ => (hA k m).mul (hB m l),
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => hO.mul (hA k m) (hB m l)

private lemma R2_dM_trace {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) {ι : Type*} [Fintype ι]
    {A : ℂ → Matrix ι ι ℂ} {w : ℂ} (hA : ∀ k l, DifferentiableAt ℝ (fun x => A x k l) w) :
    Dop (fun x => (A x).trace) w = (R2_dM Dop A w).trace := by
  simp only [Matrix.trace, Matrix.diag, R2_dM, Matrix.of_apply]
  exact hO.sum Finset.univ (fun k x => A x k k) fun k _ => hA k k

/-! ### The matrix of a word along the slice -/

/-- The matrix of one letter of a word of the class `𝓡`. -/
private def R2_lm {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ)
    (κ : ℕ → Idx D N) (x : PkgLetter) : Matrix (Idx D N) (Idx D N) ℂ :=
  match x with
  | .lw y => loopWordMat G M E L [y]
  | .ent u v => Matrix.of fun k l => if k = κ u ∧ l = κ v then (1 : ℂ) else 0

section Word

variable {D N : ℕ} (G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
  (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N)

private lemma R2_wm_nil : pkgWordMat G M E L κ [] = 1 := rfl

private lemma R2_wm_cons (x : PkgLetter) (w : List PkgLetter) :
    pkgWordMat G M E L κ (x :: w) = R2_lm G M E L κ x * pkgWordMat G M E L κ w := by
  cases x <;> rfl

private lemma R2_lm_res (a : Fin 2) : R2_lm G M E L κ (.lw (.res a)) = G a := by
  simp [R2_lm, loopWordMat]

private lemma R2_lm_det (a : Fin 2) : R2_lm G M E L κ (.lw (.det a)) = M a := by
  simp [R2_lm, loopWordMat]

private lemma R2_lm_proj (y : ℕ) : R2_lm G M E L κ (.lw (.proj y)) = E y := by
  simp [R2_lm, loopWordMat]

private lemma R2_lm_lamt (o : Fin 2) : R2_lm G M E L κ (.lw (.lamt o)) = L := by
  simp [R2_lm, loopWordMat]

end Word

/-- The resolvent letter at position `r` of a word, if there is one. -/
private def R2_hit (w : List PkgLetter) (r : ℕ) : Option (Fin 2) :=
  match w[r]? with
  | some (.lw (.res a)) => some a
  | _ => none

private lemma R2_hit_succ (x : PkgLetter) (w : List PkgLetter) (r : ℕ) :
    R2_hit (x :: w) (r + 1) = R2_hit w r := rfl

private lemma R2_diff_lm {D N : ℕ} (G : ℂ → Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ)
    (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N) {w0 : ℂ}
    (hG : ∀ a k l, DifferentiableAt ℝ (fun x => G x a k l) w0) (x : PkgLetter) :
    ∀ k l, DifferentiableAt ℝ (fun x' => R2_lm (G x') M E L κ x k l) w0 := by
  intro k l
  rcases x with ((a | a | y | o) | ⟨u, v⟩)
  · simp only [R2_lm_res]
    exact hG a k l
  · simp only [R2_lm_det]
    exact differentiableAt_const _
  · simp only [R2_lm_proj]
    exact differentiableAt_const _
  · simp only [R2_lm_lamt]
    exact differentiableAt_const _
  · exact differentiableAt_const _

private lemma R2_diff_word {D N : ℕ} (G : ℂ → Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ)
    (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N) {w0 : ℂ}
    (hG : ∀ a k l, DifferentiableAt ℝ (fun x => G x a k l) w0) (w : List PkgLetter) :
    ∀ k l, DifferentiableAt ℝ (fun x' => pkgWordMat (G x') M E L κ w k l) w0 := by
  induction w with
  | nil =>
    intro k l
    exact differentiableAt_const _
  | cons x w ih =>
    simp only [R2_wm_cons]
    exact R2_diffM_mul (R2_diff_lm G M E L κ hG x) ih

/-- The derivative of the matrix of a word: one term per resolvent letter `𝒢_a`, replaced by
`-c 𝒢_a Δ_{uv} 𝒢_a`. -/
private lemma R2_dM_word {D N : ℕ} {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop)
    (G : ℂ → Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ) (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ)
    (L : Matrix (Idx D N) (Idx D N) ℂ) (κ : ℕ → Idx D N) (u v : ℕ) (c w0 : ℂ)
    (hG : ∀ a k l, DifferentiableAt ℝ (fun x => G x a k l) w0)
    (hD : ∀ a, R2_dM Dop (fun x => G x a) w0 =
      (-c) • (G w0 a * R2_lm (G w0) M E L κ (.ent u v) * G w0 a)) (w : List PkgLetter) :
    R2_dM Dop (fun x => pkgWordMat (G x) M E L κ w) w0 =
      ((List.range w.length).map fun r => ((R2_hit w r).map fun a => (-c) •
        pkgWordMat (G w0) M E L κ (w.take r ++ [.lw (.res a), .ent u v, .lw (.res a)] ++
          w.drop (r + 1))).getD 0).sum := by
  induction w with
  | nil => simpa [R2_wm_nil] using R2_dM_const hO (1 : Matrix (Idx D N) (Idx D N) ℂ) w0
  | cons x w ih =>
    simp only [R2_wm_cons]
    rw [R2_dM_mul hO (R2_diff_lm G M E L κ hG x) (R2_diff_word G M E L κ hG w), ih,
      List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    congr 1
    · rcases x with ((a | a | y | o) | ⟨u', v'⟩)
      · simp only [R2_lm_res, hD a, R2_hit, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some, List.take_zero, List.nil_append, zero_add, List.drop_succ_cons,
          List.drop_zero, List.cons_append, R2_wm_cons, Matrix.smul_mul, Matrix.mul_assoc]
      · simp only [R2_lm_det, R2_dM_const hO, R2_hit, List.getElem?_cons_zero, Option.map_none,
          Option.getD_none, zero_mul]
      · simp only [R2_lm_proj, R2_dM_const hO, R2_hit, List.getElem?_cons_zero, Option.map_none,
          Option.getD_none, zero_mul]
      · simp only [R2_lm_lamt, R2_dM_const hO, R2_hit, List.getElem?_cons_zero, Option.map_none,
          Option.getD_none, zero_mul]
      · simp only [R2_lm, R2_dM_const hO, R2_hit, List.getElem?_cons_zero, Option.map_none,
          Option.getD_none, zero_mul]
    · rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun r _ => ?_
      simp only [Function.comp, R2_hit_succ, List.take_succ_cons, List.drop_succ_cons,
        List.cons_append, R2_wm_cons]
      cases R2_hit w r <;> simp

/-! ### Sums over lists -/

private lemma R2_sum_flatMap {α β : Type*} (g : α → List β) (F : β → ℂ) :
    ∀ L : List α, ((L.flatMap g).map F).sum = (L.map fun x => ((g x).map F).sum).sum
  | [] => rfl
  | a :: L => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, R2_sum_flatMap g F L, List.map_cons,
      List.sum_cons]

private lemma R2_sum_filterMap {α β γ : Type*} (o : α → Option γ) (k : α → γ → β) (F : β → ℂ) :
    ∀ L : List α, ((L.filterMap fun x => (o x).map (k x)).map F).sum =
      (L.map fun x => ((o x).map fun a => F (k x a)).getD 0).sum
  | [] => rfl
  | a :: L => by
    rw [List.filterMap_cons, List.map_cons, List.sum_cons, ← R2_sum_filterMap o k F L]
    cases o a <;> simp

private lemma R2_sum_getD {β γ : Type*} (o : Option γ) (g : γ → List β) (F : β → ℂ) :
    (((o.map g).getD []).map F).sum = (o.map fun x => ((g x).map F).sum).getD 0 := by
  cases o <;> rfl

private lemma R2_trace_lsum {ι α : Type*} [Fintype ι] (f : α → Matrix ι ι ℂ) :
    ∀ L : List α, ((L.map f).sum).trace = (L.map fun a => (f a).trace).sum
  | [] => by simp
  | a :: L => by rw [List.map_cons, List.sum_cons, Matrix.trace_add, R2_trace_lsum f L]; rfl

private lemma R2_prod_set {α : Type*} (f : α → ℂ) (x : α) :
    ∀ (L : List α) (ℓ : ℕ) (w : α), L[ℓ]? = some w →
      ((L.set ℓ x).map f).prod = f x * ((L.eraseIdx ℓ).map f).prod
  | [], _, _, h => by simp at h
  | a :: L, 0, w, _ => by simp
  | a :: L, ℓ + 1, w, h => by
    rw [List.getElem?_cons_succ] at h
    rw [List.set_cons_succ, List.eraseIdx_cons_succ, List.map_cons, List.prod_cons,
      R2_prod_set f x L ℓ w h, List.map_cons, List.prod_cons]
    ring

private lemma R2_lsum_comm {α : Type*} {β : Type*} (s : Finset β) (F : α → β → ℂ) :
    ∀ L : List α, (L.map fun a => ∑ b ∈ s, F a b).sum = ∑ b ∈ s, (L.map fun a => F a b).sum
  | [] => by simp
  | a :: L => by
    rw [List.map_cons, List.sum_cons, R2_lsum_comm s F L, ← Finset.sum_add_distrib]
    rfl

/-! ### The value of an expression at fixed bound indices -/

/-- The letter is a matrix `Δ`. -/
private def R2_isEnt (x : PkgLetter) : Bool :=
  match x with
  | .ent _ _ => true
  | _ => false

/-- The factor of a word: its trace if it has a letter `Δ`, its normalized trace otherwise. -/
private def R2_wv {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) (w : List PkgLetter) : ℂ :=
  if w.any R2_isEnt then (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w).trace
  else ntr (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w)

/-- The light weight `⟨(𝒢_a - 𝔐_a) E_x⟩`. -/
private def R2_wt {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D)
    (h : Idx D N → Idx D N → ℂ) (p : Fin 2 × ℕ) : ℂ :=
  ntr ((e.G h p.1 - e.M p.1) * e.E ι p.2)

/-- The coefficient `cf D^{dexp} N^{-S}`. -/
private def R2_coef (D N : ℕ) (R : PkgExpr) : ℂ :=
  (R.cf : ℂ) * (D : ℂ) ^ R.dexp * (N : ℂ) ^ (-R.S)

/-- The term of `PkgExpr.evalH` at the bound indices `ι`. -/
private def R2_val {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (κ : ℕ → Idx D N)
    (R : PkgExpr) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  R2_coef D N R * ((R.weights.map (R2_wt e ι h)).prod * (R.loops.map (R2_wv e ι κ h)).prod)

private lemma R2_evalH {D N : ℕ} (R : PkgExpr) (e : LoopEnv D N) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) {n : ℕ} (hn : R.nb = n) :
    R.evalH e κ h = ∑ ι : Fin n → Fin D, R2_val e ι κ R h := by
  subst hn
  unfold PkgExpr.evalH R2_val R2_coef
  rw [Finset.mul_sum]
  rfl

/-- The deformation `c_a Λ` of a slot is Hermitian. -/
private lemma R2_slot_herm {D N : ℕ} (e : LoopEnv D N) (a : Fin 2) :
    ((e.c a : ℂ) • lam D N e.A).IsHermitian := by
  have := lam_isHermitian D N e.A
  unfold Matrix.IsHermitian at this ⊢
  rw [Matrix.conjTranspose_smul, this]
  simp

/-- The spectral parameter of a slot is off the real axis. -/
private lemma R2_slot_im {D N : ℕ} (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0) (a : Fin 2) :
    (if e.s a then star (e.z a) else e.z a).im ≠ 0 := by
  split_ifs
  · simpa using he a
  · exact he a

private lemma R2_goodM_G {D N : ℕ} (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0) (a : Fin 2) :
    R2_goodM fun h => e.G h a :=
  R2_goodM_res _ (R2_slot_herm e a) _ (R2_slot_im e he a)

private lemma R2_goodM_word {D N n : ℕ} (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0)
    (ι : Fin n → Fin D) (κ : ℕ → Idx D N) (w : List PkgLetter) :
    R2_goodM fun h => pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w := by
  induction w with
  | nil => exact R2_goodM_const 1
  | cons x w ih =>
    simp only [R2_wm_cons]
    refine R2_goodM_mul ?_ ih
    rcases x with ((a | a | y | o) | ⟨u, v⟩)
    · simpa only [R2_lm_res] using R2_goodM_G e he a
    · simpa only [R2_lm_det] using R2_goodM_const (e.M a)
    · simpa only [R2_lm_proj] using R2_goodM_const (e.E ι y)
    · simpa only [R2_lm_lamt] using R2_goodM_const e.Lt
    · exact R2_goodM_const _

private lemma R2_good_wv {D N n : ℕ} (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0)
    (ι : Fin n → Fin D) (κ : ℕ → Idx D N) (w : List PkgLetter) :
    R2_good fun h => R2_wv e ι κ h w := by
  unfold R2_wv
  split_ifs
  · exact R2_good_trace (R2_goodM_word e he ι κ w)
  · exact R2_good_ntr (R2_goodM_word e he ι κ w)

private lemma R2_good_wt {D N n : ℕ} (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0)
    (ι : Fin n → Fin D) (p : Fin 2 × ℕ) : R2_good fun h => R2_wt e ι h p :=
  R2_good_ntr (R2_goodM_mul (R2_goodM_sub (R2_goodM_G e he p.1) (R2_goodM_const _))
    (R2_goodM_const _))

private lemma R2_good_val {D N n : ℕ} (e : LoopEnv D N) (he : ∀ a, (e.z a).im ≠ 0)
    (ι : Fin n → Fin D) (κ : ℕ → Idx D N) (R : PkgExpr) :
    R2_good fun h => R2_val e ι κ R h :=
  R2_good_mul (R2_good_const _) (R2_good_mul
    (R2_good_prod (fun p h => R2_wt e ι h p) R.weights fun p _ => R2_good_wt e he ι p)
    (R2_good_prod (fun w h => R2_wv e ι κ h w) R.loops fun w _ => R2_good_wv e he ι κ w))

/-! ### One derivative of an expression -/

/-- The term of `PkgExpr.dent` at a resolvent of a loop. -/
private def R2_ins (R : PkgExpr) (ℓ : ℕ) (w : List PkgLetter) (r : ℕ) (a : Fin 2) (u v : ℕ) :
    PkgExpr :=
  { R with
    cf := -R.cf, dexp := if !(w.any R2_isEnt) then R.dexp - 1 else R.dexp,
    S := if !(w.any R2_isEnt) then R.S + 1 else R.S,
    loops := R.loops.set ℓ (w.take r ++ [.lw (.res a), .ent u v, .lw (.res a)] ++
      w.drop (r + 1)) }

/-- The term of `PkgExpr.dent` at a light weight. -/
private def R2_wins (R : PkgExpr) (j : ℕ) (p : Fin 2 × ℕ) (u v : ℕ) : PkgExpr :=
  { R with
    cf := -R.cf, dexp := R.dexp - 1, S := R.S + 1, weights := R.weights.eraseIdx j,
    loops := R.loops ++ [[.lw (.res p.1), .ent u v, .lw (.res p.1), .lw (.proj p.2)]] }

private lemma R2_dent_eq (R : PkgExpr) (u v : ℕ) : R.dent u v =
    ((List.range R.loops.length).flatMap fun ℓ => (R.loops[ℓ]?.map fun w =>
      (List.range w.length).filterMap fun r =>
        (R2_hit w r).map fun a => R2_ins R ℓ w r a u v).getD []) ++
    ((List.range R.weights.length).filterMap fun j =>
      R.weights[j]?.map fun p => R2_wins R j p u v) := by
  unfold PkgExpr.dent
  congr 1
  · congr 1
    funext ℓ
    rcases hl : R.loops[ℓ]? with _ | w
    · rfl
    · simp only [Option.map_some, Option.getD_some]
      congr 1
      funext r
      unfold R2_hit
      rcases hw : w[r]? with _ | ((a | a | y | o) | ⟨u', v'⟩) <;> rfl
  · congr 1
    funext j
    rcases hj : R.weights[j]? with _ | ⟨b, y⟩ <;> rfl

private lemma R2_dM_sub_const {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) {ι : Type*}
    {A : ℂ → Matrix ι ι ℂ} (X : Matrix ι ι ℂ) {w : ℂ}
    (hA : ∀ k l, DifferentiableAt ℝ (fun x => A x k l) w) :
    R2_dM Dop (fun x => A x - X) w = R2_dM Dop A w := by
  ext k l
  simp only [R2_dM, Matrix.of_apply, Matrix.sub_apply]
  rw [show (fun x => A x k l - X k l) = fun x => A x k l + (-X k l) by funext x; ring,
    hO.add (f := fun x => A x k l) (g := fun _ => -X k l) (hA k l) (differentiableAt_const _),
    hO.const, add_zero]

private lemma R2_wv_any {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (κ : ℕ → Idx D N)
    (h : Idx D N → Idx D N → ℂ) {w : List PkgLetter} (hw : w.any R2_isEnt = true) :
    R2_wv e ι κ h w = (pkgWordMat (e.G h) e.M (e.E ι) e.Lt κ w).trace := by
  simp [R2_wv, hw]

private lemma R2_card (D N : ℕ) : ((Fintype.card (Idx D N) : ℕ) : ℂ) = (D : ℂ) * N := by
  simp [Fintype.card_prod]

private lemma R2_zpow_D {D : ℕ} (hD : (D : ℂ) ≠ 0) (d : ℤ) :
    (D : ℂ) ^ (d - 1) = (D : ℂ) ^ d * (D : ℂ)⁻¹ :=
  zpow_sub_one₀ hD d

private lemma R2_zpow_N {N : ℕ} (hN : (N : ℂ) ≠ 0) (S : ℤ) :
    (N : ℂ) ^ (-(S + 1)) = (N : ℂ) ^ (-S) * (N : ℂ)⁻¹ := by
  rw [neg_add, zpow_add₀ hN, _root_.zpow_neg_one]

section Leibniz

variable {D N n : ℕ} (e : LoopEnv D N) (ι : Fin n → Fin D) (κ : ℕ → Idx D N)
  (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)

private lemma R2_diffG (he : ∀ a, (e.z a).im ≠ 0) (hh : (Matrix.of h).IsHermitian) :
    ∀ a k l w0, DifferentiableAt ℝ (fun x => e.G (setEntry h i j x) a k l) w0 :=
  fun a k l w0 => R2_good_slice (R2_goodM_G e he a k l) h hh i j w0

/-- The derivative of the factor of a word along the slice. -/
private lemma R2_dwv (he : ∀ a, (e.z a).im ≠ 0) (hh : (Matrix.of h).IsHermitian)
    {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) (u v : ℕ) (c w0 : ℂ)
    (hD : ∀ a, R2_dM Dop (fun x => e.G (setEntry h i j x) a) w0 =
      (-c) • (e.G (setEntry h i j w0) a *
        R2_lm (e.G (setEntry h i j w0)) e.M (e.E ι) e.Lt κ (.ent u v) * e.G (setEntry h i j w0) a))
    (w : List PkgLetter) :
    Dop (fun x => R2_wv e ι κ (setEntry h i j x) w) w0 =
      ((List.range w.length).map fun r => ((R2_hit w r).map fun a =>
        (if w.any R2_isEnt then 1 else ((Fintype.card (Idx D N) : ℂ))⁻¹) *
          ((-c) * (pkgWordMat (e.G (setEntry h i j w0)) e.M (e.E ι) e.Lt κ
            (w.take r ++ [.lw (.res a), .ent u v, .lw (.res a)] ++ w.drop (r + 1))).trace)).getD
        0).sum := by
  have hG := R2_diffG e h i j he hh
  have hW := R2_dM_word hO (fun x => e.G (setEntry h i j x)) e.M (e.E ι) e.Lt κ u v c w0
    (fun a k l => hG a k l w0) hD w
  have hdw := R2_diff_word (fun x => e.G (setEntry h i j x)) e.M (e.E ι) e.Lt κ
    (fun a k l => hG a k l w0) w
  have hdt : DifferentiableAt ℝ (fun x =>
      (pkgWordMat (e.G (setEntry h i j x)) e.M (e.E ι) e.Lt κ w).trace) w0 := by
    simp only [Matrix.trace, Matrix.diag]
    exact DifferentiableAt.fun_sum fun k _ => hdw k k
  unfold R2_wv
  by_cases hb : w.any R2_isEnt = true
  · simp only [hb, ite_true, one_mul]
    rw [R2_dM_trace hO hdw, hW, R2_trace_lsum]
    congr 1
    refine List.map_congr_left fun r _ => ?_
    cases R2_hit w r <;> simp [Matrix.trace_smul]
  · simp only [hb, ite_false, Bool.false_eq_true]
    unfold ntr
    rw [hO.cmul _ hdt, R2_dM_trace hO hdw, hW, R2_trace_lsum, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun r _ => ?_
    cases R2_hit w r <;> simp [Matrix.trace_smul]

/-- The derivative of a light weight along the slice. -/
private lemma R2_dwt (he : ∀ a, (e.z a).im ≠ 0) (hh : (Matrix.of h).IsHermitian)
    {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) (u v : ℕ) (c w0 : ℂ)
    (hD : ∀ a, R2_dM Dop (fun x => e.G (setEntry h i j x) a) w0 =
      (-c) • (e.G (setEntry h i j w0) a *
        R2_lm (e.G (setEntry h i j w0)) e.M (e.E ι) e.Lt κ (.ent u v) * e.G (setEntry h i j w0) a))
    (p : Fin 2 × ℕ) :
    Dop (fun x => R2_wt e ι (setEntry h i j x) p) w0 =
      ((Fintype.card (Idx D N) : ℂ))⁻¹ * ((-c) * (pkgWordMat (e.G (setEntry h i j w0)) e.M
        (e.E ι) e.Lt κ [.lw (.res p.1), .ent u v, .lw (.res p.1), .lw (.proj p.2)]).trace) := by
  have hG := R2_diffG e h i j he hh
  have hs : ∀ k l, DifferentiableAt ℝ
      (fun x => (e.G (setEntry h i j x) p.1 - e.M p.1) k l) w0 := by
    intro k l
    simp only [Matrix.sub_apply]
    exact (hG p.1 k l w0).sub (differentiableAt_const _)
  have hc : ∀ k l, DifferentiableAt ℝ (fun _ : ℂ => (e.E ι p.2) k l) w0 :=
    fun k l => differentiableAt_const _
  have hm := R2_diffM_mul hs hc
  have hdt : DifferentiableAt ℝ (fun x =>
      ((e.G (setEntry h i j x) p.1 - e.M p.1) * e.E ι p.2).trace) w0 := by
    simp only [Matrix.trace, Matrix.diag]
    exact DifferentiableAt.fun_sum fun k _ => hm k k
  unfold R2_wt ntr
  rw [hO.cmul _ hdt, R2_dM_trace hO hm, R2_dM_mul hO hs hc, R2_dM_const hO,
    R2_dM_sub_const hO _ (fun k l => hG p.1 k l w0), hD]
  simp only [mul_zero, add_zero, R2_wm_cons, R2_lm_res, R2_lm_proj, R2_wm_nil, mul_one,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]

/-- One derivative of the value of an expression along the slice is `c` times the sum over the
expressions of `PkgExpr.dent`. -/
private lemma R2_dval (he : ∀ a, (e.z a).im ≠ 0) (hh : (Matrix.of h).IsHermitian)
    (hD0 : (D : ℂ) ≠ 0) (hN0 : (N : ℂ) ≠ 0)
    {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) (u v : ℕ) (c w0 : ℂ)
    (hD : ∀ a, R2_dM Dop (fun x => e.G (setEntry h i j x) a) w0 =
      (-c) • (e.G (setEntry h i j w0) a *
        R2_lm (e.G (setEntry h i j w0)) e.M (e.E ι) e.Lt κ (.ent u v) * e.G (setEntry h i j w0) a))
    (R : PkgExpr) :
    Dop (fun x => R2_val e ι κ R (setEntry h i j x)) w0 =
      c * ((R.dent u v).map fun R' => R2_val e ι κ R' (setEntry h i j w0)).sum := by
  have hdwt : ∀ p, DifferentiableAt ℝ (fun x => R2_wt e ι (setEntry h i j x) p) w0 :=
    fun p => R2_good_slice (R2_good_wt e he ι p) h hh i j w0
  have hdwv : ∀ w, DifferentiableAt ℝ (fun x => R2_wv e ι κ (setEntry h i j x) w) w0 :=
    fun w => R2_good_slice (R2_good_wv e he ι κ w) h hh i j w0
  have hWt := R2_diff_prod (fun p x => R2_wt e ι (setEntry h i j x) p) R.weights
    (fun p _ => hdwt p)
  have hLp := R2_diff_prod (fun w x => R2_wv e ι κ (setEntry h i j x) w) R.loops
    (fun w _ => hdwv w)
  have hcard := R2_card D N
  have e1 : (fun x => R2_val e ι κ R (setEntry h i j x)) = fun x => R2_coef D N R *
      ((R.weights.map fun p => R2_wt e ι (setEntry h i j x) p).prod *
        (R.loops.map fun w => R2_wv e ι κ (setEntry h i j x) w).prod) := rfl
  rw [e1, hO.cmul (f := fun x =>
      (R.weights.map fun p => R2_wt e ι (setEntry h i j x) p).prod *
        (R.loops.map fun w => R2_wv e ι κ (setEntry h i j x) w).prod) _ (hWt.mul hLp),
    hO.mul hWt hLp,
    R2_Op.prod hO _ R.weights (fun p _ => hdwt p), R2_Op.prod hO _ R.loops (fun w _ => hdwv w),
    R2_dent_eq, List.map_append, List.sum_append, R2_sum_flatMap, R2_sum_filterMap]
  simp only [R2_sum_getD, R2_sum_filterMap]
  rw [mul_add, mul_add, add_comm, ← List.sum_map_mul_left, ← List.sum_map_mul_left,
    ← List.sum_map_mul_right, ← List.sum_map_mul_left, ← List.sum_map_mul_left,
    ← List.sum_map_mul_left]
  congr 1
  · refine congrArg List.sum (List.map_congr_left fun ℓ _ => ?_)
    rcases hl : R.loops[ℓ]? with _ | w
    · simp
    · simp only [Option.map_some, Option.getD_some]
      rw [R2_dwv e ι κ h i j he hh hO u v c w0 hD w, ← List.sum_map_mul_right,
        ← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
      rcases R2_hit w r with _ | a
      · simp
      · simp only [Option.map_some, Option.getD_some]
        unfold R2_val R2_ins R2_coef
        simp only
        rw [R2_prod_set _ _ R.loops ℓ w hl, R2_wv_any e ι κ _ (by simp [R2_isEnt])]
        rcases hb : w.any R2_isEnt
        · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false, hcard,
            R2_zpow_D hD0, R2_zpow_N hN0, Int.cast_neg]
          ring
        · simp only [Bool.not_true, ite_true, Bool.false_eq_true, ite_false, Int.cast_neg]
          ring
  · refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
    rcases hk : R.weights[k]? with _ | p
    · simp
    · simp only [Option.map_some, Option.getD_some]
      rw [R2_dwt e ι κ h i j he hh hO u v c w0 hD p]
      unfold R2_val R2_wins R2_coef
      simp only
      rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
        R2_wv_any e ι κ _ (by simp [R2_isEnt])]
      simp only [hcard, R2_zpow_D hD0, R2_zpow_N hN0, Int.cast_neg]
      ring

end Leibniz

/-- The matrix `A Δ_{uv} B` at `(k, l)` is `A_{k κ u} B_{κ v l}`. -/
private lemma R2_mul_ent {D N : ℕ} (A B G M : Fin 2 → Matrix (Idx D N) (Idx D N) ℂ)
    (E : ℕ → Matrix (Idx D N) (Idx D N) ℂ) (L : Matrix (Idx D N) (Idx D N) ℂ)
    (κ : ℕ → Idx D N) (u v : ℕ) (a : Fin 2) (k l : Idx D N) :
    (A a * R2_lm G M E L κ (.ent u v) * B a) k l = A a k (κ u) * B a (κ v) l := by
  simp only [Matrix.mul_apply, R2_lm, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq', ite_mul]


/-! ### Iterated derivatives at the labels `2 ↦ i`, `3 ↦ j` -/

section Iter

variable {D N n : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)

/-- `∂_w 𝒢 = -c 𝒢 Δ_{23} 𝒢` at the labels `2 ↦ i`, `3 ↦ j` (`res_dW`). -/
private lemma R2_hD_dW (ι : Fin n → Fin D) (he : ∀ a, (e.z a).im ≠ 0)
    (hh : (Matrix.of h).IsHermitian) (κ : ℕ → Idx D N) (h2 : κ 2 = i) (h3 : κ 3 = j) (a : Fin 2)
    (w0 : ℂ) :
    R2_dM dW (fun x => e.G (setEntry h i j x) a) w0 =
      (-(if i = j then (1 / 2 : ℂ) else 1)) • (e.G (setEntry h i j w0) a *
        R2_lm (e.G (setEntry h i j w0)) e.M (e.E ι) e.Lt κ (.ent 2 3) *
          e.G (setEntry h i j w0) a) := by
  ext k l
  rw [Matrix.smul_apply, R2_mul_ent, h2, h3, smul_eq_mul]
  have := congrFun (res_dW _ (R2_slot_herm e a) _ (R2_slot_im e he a) h hh i j k l).1 w0
  simp only [R2_dM, Matrix.of_apply]
  exact this.trans (by unfold LoopEnv.G; ring)

/-- `∂_w̄ 𝒢 = -c 𝒢 Δ_{32} 𝒢` at the labels `2 ↦ i`, `3 ↦ j` (`res_dW`). -/
private lemma R2_hD_dWbar (ι : Fin n → Fin D) (he : ∀ a, (e.z a).im ≠ 0)
    (hh : (Matrix.of h).IsHermitian) (κ : ℕ → Idx D N) (h2 : κ 2 = i) (h3 : κ 3 = j) (a : Fin 2)
    (w0 : ℂ) :
    R2_dM dWbar (fun x => e.G (setEntry h i j x) a) w0 =
      (-(if i = j then (1 / 2 : ℂ) else 1)) • (e.G (setEntry h i j w0) a *
        R2_lm (e.G (setEntry h i j w0)) e.M (e.E ι) e.Lt κ (.ent 3 2) *
          e.G (setEntry h i j w0) a) := by
  ext k l
  rw [Matrix.smul_apply, R2_mul_ent, h2, h3, smul_eq_mul]
  have := congrFun (res_dW _ (R2_slot_herm e a) _ (R2_slot_im e he a) h hh i j k l).2 w0
  simp only [R2_dM, Matrix.of_apply]
  exact this.trans (by unfold LoopEnv.G; ring)

/-- A list sum of functions that are differentiable at a point is differentiable there. -/
private lemma R2_diff_lsum {F : PkgExpr → ℂ → ℂ} {w0 : ℂ} :
    ∀ L : List PkgExpr, (∀ R ∈ L, DifferentiableAt ℝ (F R) w0) →
      DifferentiableAt ℝ (fun x => (L.map fun R => F R x).sum) w0
  | [], _ => by simp
  | R :: L, hL => by
    simp only [List.map_cons, List.sum_cons]
    exact (hL R List.mem_cons_self).add
      (R2_diff_lsum L fun R' hR' => hL R' (List.mem_cons_of_mem _ hR'))

/-- One derivative of the sum over the bound indices of a list of expressions. -/
private lemma R2_dlist (κ : ℕ → Idx D N) (he : ∀ a, (e.z a).im ≠ 0)
    (hh : (Matrix.of h).IsHermitian) (hD0 : (D : ℂ) ≠ 0) (hN0 : (N : ℂ) ≠ 0)
    {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) (u v : ℕ) (c : ℂ)
    (hD : ∀ (ι : Fin n → Fin D) (a : Fin 2) (w0 : ℂ),
      R2_dM Dop (fun x => e.G (setEntry h i j x) a) w0 =
      (-c) • (e.G (setEntry h i j w0) a *
        R2_lm (e.G (setEntry h i j w0)) e.M (e.E ι) e.Lt κ (.ent u v) * e.G (setEntry h i j w0) a))
    (K : ℂ) (L : List PkgExpr) :
    Dop (fun x => ∑ ι : Fin n → Fin D,
        K * (L.map fun R => R2_val e ι κ R (setEntry h i j x)).sum) =
      fun x => ∑ ι : Fin n → Fin D, K * c *
        ((L.flatMap fun R => R.dent u v).map fun R => R2_val e ι κ R (setEntry h i j x)).sum := by
  funext w0
  have hd : ∀ (ι : Fin n → Fin D), ∀ R ∈ L,
      DifferentiableAt ℝ (fun x => R2_val e ι κ R (setEntry h i j x)) w0 :=
    fun ι R _ => R2_good_slice (R2_good_val e he ι κ R) h hh i j w0
  have hds : ∀ ι : Fin n → Fin D, DifferentiableAt ℝ
      (fun x => (L.map fun R => R2_val e ι κ R (setEntry h i j x)).sum) w0 :=
    fun ι => R2_diff_lsum L (hd ι)
  rw [hO.sum Finset.univ (fun ι x => K * (L.map fun R => R2_val e ι κ R (setEntry h i j x)).sum)
    fun ι _ => (hds ι).const_mul K]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [hO.cmul _ (hds ι), R2_Op.lsum hO (fun R x => R2_val e ι κ R (setEntry h i j x)) L (hd ι),
    R2_sum_flatMap, mul_assoc]
  congr 1
  rw [← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun R _ =>
    R2_dval e ι κ h i j he hh hD0 hN0 hO u v c w0 (hD ι · w0) R)

/-- Iterated derivatives of the sum over the bound indices of a list of expressions. -/
private lemma R2_iter (κ : ℕ → Idx D N) (he : ∀ a, (e.z a).im ≠ 0)
    (hh : (Matrix.of h).IsHermitian) (hD0 : (D : ℂ) ≠ 0) (hN0 : (N : ℂ) ≠ 0)
    {Dop : (ℂ → ℂ) → ℂ → ℂ} (hO : R2_Op Dop) (u v : ℕ) (c : ℂ)
    (hD : ∀ (ι : Fin n → Fin D) (a : Fin 2) (w0 : ℂ),
      R2_dM Dop (fun x => e.G (setEntry h i j x) a) w0 =
      (-c) • (e.G (setEntry h i j w0) a *
        R2_lm (e.G (setEntry h i j w0)) e.M (e.E ι) e.Lt κ (.ent u v) * e.G (setEntry h i j w0) a))
    (m : ℕ) : ∀ (K : ℂ) (L : List PkgExpr),
    Dop^[m] (fun x => ∑ ι : Fin n → Fin D,
        K * (L.map fun R => R2_val e ι κ R (setEntry h i j x)).sum) =
      fun x => ∑ ι : Fin n → Fin D, K * c ^ m *
        (((fun L : List PkgExpr => L.flatMap fun R => R.dent u v)^[m] L).map
          fun R => R2_val e ι κ R (setEntry h i j x)).sum := by
  induction m with
  | zero => intro K L; simp
  | succ m ih =>
    intro K L
    rw [Function.iterate_succ_apply', ih, R2_dlist e h i j κ he hh hD0 hN0 hO u v c hD,
      Function.iterate_succ_apply']
    funext x
    refine Finset.sum_congr rfl fun ι _ => ?_
    ring

/-- `∂^p_w ∂^q_w̄` of the value of an expression, summed over the bound indices, along the slice
`w ↦ setEntry h i j w` at the labels `2 ↦ i`, `3 ↦ j`: `c^{p+q}` times the sum over
`PkgExpr.dwirt 2 3 p q`. -/
private lemma R2_wirt (κ : ℕ → Idx D N) (he : ∀ a, (e.z a).im ≠ 0)
    (hh : (Matrix.of h).IsHermitian) (hD0 : (D : ℂ) ≠ 0) (hN0 : (N : ℂ) ≠ 0)
    (h2 : κ 2 = i) (h3 : κ 3 = j) (R : PkgExpr) (p q : ℕ) :
    wirt p q (fun x => ∑ ι : Fin n → Fin D, R2_val e ι κ R (setEntry h i j x)) =
      fun x => (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) *
        ((R.dwirt 2 3 p q).map fun R' =>
          ∑ ι : Fin n → Fin D, R2_val e ι κ R' (setEntry h i j x)).sum := by
  have e0 : (fun x => ∑ ι : Fin n → Fin D, R2_val e ι κ R (setEntry h i j x)) =
      fun x => ∑ ι : Fin n → Fin D,
        1 * ([R].map fun R' => R2_val e ι κ R' (setEntry h i j x)).sum := by
    funext x
    simp
  unfold wirt
  rw [e0, R2_iter e h i j κ he hh hD0 hN0 R2_op_dWbar 3 2 _
      (fun ι a w0 => R2_hD_dWbar e h i j ι he hh κ h2 h3 a w0) q,
    R2_iter e h i j κ he hh hD0 hN0 R2_op_dW 2 3 _
      (fun ι a w0 => R2_hD_dW e h i j ι he hh κ h2 h3 a w0) p]
  funext x
  unfold PkgExpr.dwirt
  rw [R2_lsum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  ring

end Iter

/-! ### The bound block indices along `PkgExpr.dwirt` -/

/-- A property kept by `PkgExpr.dent` holds on all of `PkgExpr.dwirt`. -/
private lemma R2_iter_mem (P : PkgExpr → Prop) (u v : ℕ)
    (hP : ∀ R, P R → ∀ R' ∈ R.dent u v, P R') :
    ∀ (m : ℕ) (L : List PkgExpr), (∀ R ∈ L, P R) →
      ∀ R ∈ (fun L : List PkgExpr => L.flatMap fun R => R.dent u v)^[m] L, P R := by
  intro m
  induction m with
  | zero => intro L hL; exact hL
  | succ m ih =>
    intro L hL R hR
    rw [Function.iterate_succ_apply'] at hR
    obtain ⟨R₀, hR₀, hR⟩ := List.mem_flatMap.1 hR
    exact hP R₀ (ih L hL R₀ hR₀) R hR

/-- Every term of `PkgExpr.dent` keeps the bound indices. -/
private lemma R2_dent_nb (R : PkgExpr) (u v : ℕ) : ∀ R' ∈ R.dent u v, R'.nb = R.nb := by
  intro R' hR'
  rw [R2_dent_eq] at hR'
  rcases List.mem_append.1 hR' with hR' | hR'
  · obtain ⟨ℓ, -, hR'⟩ := List.mem_flatMap.1 hR'
    rcases hl : R.loops[ℓ]? with _ | w
    · simp [hl] at hR'
    · simp only [hl, Option.map_some, Option.getD_some, List.mem_filterMap] at hR'
      obtain ⟨r, -, hr⟩ := hR'
      rcases hp : R2_hit w r with _ | a
      · simp [hp] at hr
      · simp only [hp, Option.map_some, Option.some.injEq] at hr
        subst hr
        rfl
  · obtain ⟨k, -, hk⟩ := List.mem_filterMap.1 hR'
    rcases hw : R.weights[k]? with _ | p
    · simp [hw] at hk
    · simp only [hw, Option.map_some, Option.some.injEq] at hk
      subst hk
      rfl

/-- Every expression of `PkgExpr.dwirt 2 3 p q` has the bound indices of `R`. -/
private lemma R2_dwirt_nb (R : PkgExpr) (p q : ℕ) : ∀ R' ∈ R.dwirt 2 3 p q, R'.nb = R.nb := by
  have hP : ∀ u v : ℕ, ∀ R₁ : PkgExpr, R₁.nb = R.nb → ∀ R' ∈ R₁.dent u v, R'.nb = R.nb :=
    fun u v R₁ h1 R' hR' => (R2_dent_nb R₁ u v R' hR').trans h1
  unfold PkgExpr.dwirt
  refine R2_iter_mem _ 2 3 (hP 2 3) p _ ?_
  exact R2_iter_mem _ 3 2 (hP 3 2) q [R] (by simp)

/-! ### Integrals -/

private lemma R2_integral_list {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (F : PkgExpr → (Idx D N → Idx D N → ℂ) → ℂ) (hF : ∀ R, Integrable (F R) μ) :
    ∀ L : List PkgExpr,
      ∫ h, (L.map fun R => F R h).sum ∂μ = (L.map fun R => ∫ h, F R h ∂μ).sum := by
  have hI : ∀ L : List PkgExpr, Integrable (fun h => (L.map fun R => F R h).sum) μ := by
    intro L
    induction L with
    | nil => simp
    | cons R L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hF R).add ih
  intro L
  induction L with
  | nil => simp
  | cons R L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hF R) (hI L), ih]

/-- A Hermitian array is unchanged by writing its own entry `(i, j)` back. -/
private lemma R2_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) : setEntry h i j (h i j) = h := by
  funext k l
  unfold setEntry
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = i ∧ l = i
    · obtain ⟨hk, hl⟩ := hkl
      have h1 : star (h i i) = h i i := by simpa using hh.apply i i
      have h2 : (h i i).im = 0 := by
        have := congrArg Complex.im h1
        simp only [Complex.star_def, Complex.conj_im] at this
        linarith
      simp only [hk, hl, and_self, ite_true]
      exact Complex.ext (by simp) (by simp [h2])
    · simp [hkl]
  · by_cases h1 : k = i ∧ l = j
    · obtain ⟨hk, hl⟩ := h1
      simp [hij, hk, hl]
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨hk, hl⟩ := h2
        have : star (h i j) = h j i := by simpa using hh.apply j i
        simp only [hij, hk, hl, ite_false, and_self, ite_true, Ne.symm hij]
        rw [← this]
        simp
      · simp [hij, h1, h2]

/-- The expansion of the remainder `𝓔^{(2)}_𝓡(p, q)` of (5.83)
[concrete_expansion_tl_2_heavy_package_right] and (5.84) [concrete_expansion_tl_2_loop] into the
derivative structures of `fpkg`, as (5.66) [R_cT_typt_1_k_1_geq_1_k_2-geq_1_explicit_expression]
with the labels `2 ↦ i`, `3 ↦ j`. -/
theorem pkg_rem2_expand (D N : ℕ) (C : ℕ → ℝ) (R : PkgExpr) (e : LoopEnv D N)
    (he : ∀ a, (e.z a).im ≠ 0) (μ : Measure (Idx D N → Idx D N → ℂ)) (hμ : LLClass D N C 1 μ)
    (κ : ℕ → Idx D N) (p q : ℕ) :
    R.rem2PQ e μ κ p q = ∑ i : Idx D N, ∑ j : Idx D N,
      if i.1 = j.1 then
        ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
          (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) *
          ((R.fpkg.dwirt 2 3 p q).map fun R' =>
            ∫ h, R'.evalH e (fun l => if l = 2 then i else if l = 3 then j else κ l) h ∂μ).sum
      else 0 := by
  have := hμ.prob
  have hint : ∀ (κ' : ℕ → Idx D N) (R' : PkgExpr), Integrable (fun h => R'.evalH e κ' h) μ := by
    intro κ' R'
    have e4 : (fun h => R'.evalH e κ' h) =
        fun h => ∑ ι : Fin R'.nb → Fin D, R2_val e ι κ' R' h :=
      funext fun h => R2_evalH R' e κ' h rfl
    rw [e4]
    exact integrable_finsetSum _ fun ι _ => R2_good_integrable hμ.herm (R2_good_val e he ι κ' R')
  unfold PkgExpr.rem2PQ
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hP : i.1 = j.1
  · simp only [hP, ite_true]
    set κ' : ℕ → Idx D N := fun l => if l = 2 then i else if l = 3 then j else κ l with hκ'
    have h2 : κ' 2 = i := by simp [hκ']
    have h3 : κ' 3 = j := by simp [hκ']
    have hD0 : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fin.pos i.1).ne'
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fin.pos i.2).ne'
    have hae : (fun h => wirt p q (fun w => R.fpkg.evalH e κ' (setEntry h i j w)) (h i j)) =ᵐ[μ]
        fun h => (if i = j then (1 / 2 : ℂ) else 1) ^ (p + q) *
          ((R.fpkg.dwirt 2 3 p q).map fun R' => R'.evalH e κ' h).sum := by
      filter_upwards [hμ.herm] with h hh
      have e1 : (fun w => R.fpkg.evalH e κ' (setEntry h i j w)) =
          fun x => ∑ ι : Fin R.fpkg.nb → Fin D, R2_val e ι κ' R.fpkg (setEntry h i j x) :=
        funext fun w => R2_evalH _ e κ' _ rfl
      rw [e1, R2_wirt e h i j κ' he hh hD0 hN0 h2 h3 R.fpkg p q]
      simp only [R2_setEntry_self h hh i j]
      congr 1
      refine congrArg List.sum (List.map_congr_left fun R' hR' => ?_)
      exact (R2_evalH R' e κ' h (R2_dwirt_nb R.fpkg p q R' hR')).symm
    rw [mul_assoc, integral_congr_ae hae, integral_const_mul,
      R2_integral_list (fun R' h => R'.evalH e κ' h) (hint κ')]
  · simp [hP]

end RBMTransitionEdge

end
