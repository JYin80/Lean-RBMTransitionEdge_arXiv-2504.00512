module

public import RBMTransitionEdge.LocalLaw.FluctAvgQ
public import RBMTransitionEdge.LocalLaw.ExpansionHP

@[expose] public section

/-!
# The bound on the matrix `Q` of fluctuation averaging

The moment inequality for the entries of `Q`, one round of its self-improvement at a single `N`
with explicit exponents, the self-improving step in the form of stochastic domination
(Definition 2.8 [stoch_domination]), and the resulting bound `Q ≺ ϖ_φ`, for (2.30) [eq:HGline] in
the class.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge
-- part x

/-! ### part a -/

/-- Smooth functions of one complex variable, as functions of two real variables. -/
private def QSI_Sm (f : ℂ → ℂ) : Prop := ContDiff ℝ ∞ f

private lemma QSI_Sm.diff {f : ℂ → ℂ} (hf : QSI_Sm f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

private lemma QSI_Sm.fd {f : ℂ → ℂ} (hf : QSI_Sm f) : ContDiff ℝ ∞ (fderiv ℝ f) :=
  hf.fderiv_right (m := ∞) (by simp)

private lemma QSI_Sm.fdu {f : ℂ → ℂ} (hf : QSI_Sm f) (u : ℂ) : QSI_Sm (fun z => fderiv ℝ f z u) :=
  hf.fd.clm_apply contDiff_const

private lemma QSI_Sm.add {f g : ℂ → ℂ} (hf : QSI_Sm f) (hg : QSI_Sm g) :
    QSI_Sm (fun x => f x + g x) := ContDiff.add hf hg

private lemma QSI_Sm.mul {f g : ℂ → ℂ} (hf : QSI_Sm f) (hg : QSI_Sm g) :
    QSI_Sm (fun x => f x * g x) := ContDiff.mul hf hg

private lemma QSI_Sm.cmul {f : ℂ → ℂ} (c : ℂ) (hf : QSI_Sm f) : QSI_Sm (fun x => c * f x) :=
  ContDiff.mul contDiff_const hf

private lemma QSI_Sm.const (c : ℂ) : QSI_Sm (fun _ => c) := contDiff_const

private lemma QSI_Sm.conj {f : ℂ → ℂ} (hf : QSI_Sm f) : QSI_Sm (fun x => starRingEnd ℂ (f x)) :=
  Complex.conjCLE.contDiff.comp hf

private lemma QSI_Sm.sum {ι : Type*} (s : Finset ι) {u : ι → ℂ → ℂ} (hu : ∀ t ∈ s, QSI_Sm (u t)) :
    QSI_Sm (fun x => ∑ t ∈ s, u t x) := ContDiff.sum hu

private lemma QSI_Sm.dw {f : ℂ → ℂ} (hf : QSI_Sm f) : QSI_Sm (dW f) := by
  have a := hf.fdu 1
  have b := hf.fdu Complex.I
  exact ((a.sub (contDiff_const.mul b)).div_const 2)

private lemma QSI_Sm.dwb {f : ℂ → ℂ} (hf : QSI_Sm f) : QSI_Sm (dWbar f) := by
  have a := hf.fdu 1
  have b := hf.fdu Complex.I
  exact ((a.add (contDiff_const.mul b)).div_const 2)

private lemma QSI_Sm.itw {f : ℂ → ℂ} (hf : QSI_Sm f) (n : ℕ) : QSI_Sm (dW^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.dw

private lemma QSI_Sm.itwb {f : ℂ → ℂ} (hf : QSI_Sm f) (n : ℕ) : QSI_Sm (dWbar^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.dwb

/-- Additivity of the Wirtinger derivatives. -/
private lemma QSI_dW_add {f g : ℂ → ℂ} (hf : QSI_Sm f) (hg : QSI_Sm g) :
    dW (fun x => f x + g x) = (fun x => dW f x + dW g x) ∧
      dWbar (fun x => f x + g x) = (fun x => dWbar f x + dWbar g x) := by
  constructor <;> funext w <;>
  · have e : fderiv ℝ (fun x => f x + g x) w = fderiv ℝ f w + fderiv ℝ g w :=
      fderiv_add (hf.diff w) (hg.diff w)
    simp only [dW, dWbar, e, _root_.add_apply]
    ring

/-- The Wirtinger derivatives commute with constant factors. -/
private lemma QSI_dW_cmul {f : ℂ → ℂ} (c : ℂ) (hf : QSI_Sm f) :
    dW (fun x => c * f x) = (fun x => c * dW f x) ∧
      dWbar (fun x => c * f x) = (fun x => c * dWbar f x) := by
  constructor <;> funext w <;>
  · have e : fderiv ℝ (fun x => c * f x) w = c • fderiv ℝ f w := fderiv_const_mul (hf.diff w) c
    simp only [dW, dWbar, e, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

/-- The product rule as an identity of functions. -/
private lemma QSI_dW_mul {f g : ℂ → ℂ} (hf : QSI_Sm f) (hg : QSI_Sm g) :
    dW (fun x => f x * g x) = (fun x => dW f x * g x + f x * dW g x) ∧
      dWbar (fun x => f x * g x) = (fun x => dWbar f x * g x + f x * dWbar g x) :=
  ⟨funext fun w => (dW_mul (hf.diff w) (hg.diff w)).1,
    funext fun w => (dW_mul (hf.diff w) (hg.diff w)).2⟩

/-- A derivation-like operator on smooth functions. -/
private structure QSI_Der (T : (ℂ → ℂ) → (ℂ → ℂ)) : Prop where
  sm : ∀ f, QSI_Sm f → QSI_Sm (T f)
  add : ∀ f g, QSI_Sm f → QSI_Sm g → T (fun x => f x + g x) = fun x => T f x + T g x
  cmul : ∀ (c : ℂ) f, QSI_Sm f → T (fun x => c * f x) = fun x => c * T f x
  mul : ∀ f g, QSI_Sm f → QSI_Sm g →
    T (fun x => f x * g x) = fun x => T f x * g x + f x * T g x

private lemma QSI_Der_dW : QSI_Der dW :=
  ⟨fun _ hf => hf.dw, fun _ _ hf hg => (QSI_dW_add hf hg).1, fun c _ hf => (QSI_dW_cmul c hf).1,
    fun _ _ hf hg => (QSI_dW_mul hf hg).1⟩

private lemma QSI_Der_dWbar : QSI_Der dWbar :=
  ⟨fun _ hf => hf.dwb, fun _ _ hf hg => (QSI_dW_add hf hg).2,
    fun c _ hf => (QSI_dW_cmul c hf).2, fun _ _ hf hg => (QSI_dW_mul hf hg).2⟩

private lemma QSI_Der.iter_sm {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) {f : ℂ → ℂ} (hf : QSI_Sm f)
    (n : ℕ) : QSI_Sm (T^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact hT.sm _ ih

/-- A derivation-like operator is linear on finite sums. -/
private lemma QSI_Der.sum {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (u : ι → ℂ → ℂ) (hu : ∀ t ∈ s, QSI_Sm (u t)) :
    T (fun x => ∑ t ∈ s, c t * u t x) = fun x => ∑ t ∈ s, c t * T (u t) x := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 := hT.cmul 0 (fun _ => 0) (QSI_Sm.const 0)
    simp only [zero_mul] at h0
    simpa using h0
  | insert t s ht ih =>
    have hs : ∀ t' ∈ s, QSI_Sm (u t') := fun t' h' => hu t' (Finset.mem_insert_of_mem h')
    simp only [Finset.sum_insert ht]
    rw [hT.add _ _ ((hu t (Finset.mem_insert_self t s)).cmul (c t))
      (QSI_Sm.sum s fun t' h' => (hs t' h').cmul (c t')), hT.cmul _ _ (hu t
        (Finset.mem_insert_self t s)), ih hs]

private lemma QSI_Der.iter_sum {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (u : ι → ℂ → ℂ) (hu : ∀ t ∈ s, QSI_Sm (u t)) (n : ℕ) :
    T^[n] (fun x => ∑ t ∈ s, c t * u t x) = fun x => ∑ t ∈ s, c t * T^[n] (u t) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hT.sum s c _ fun t ht => hT.iter_sm (hu t ht) n]
    funext x
    simp only [Function.iterate_succ_apply']

/-- The Leibniz rule for the iterates of a derivation-like operator. -/
private lemma QSI_Der.leib {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) {f g : ℂ → ℂ} (hf : QSI_Sm f)
    (hg : QSI_Sm g) (n : ℕ) :
    T^[n] (fun x => f x * g x) = fun x => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((n.choose ij.1 : ℕ) : ℂ) * (T^[ij.1] f x * T^[ij.2] g x) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      hT.sum _ (fun ij : ℕ × ℕ => ((n.choose ij.1 : ℕ) : ℂ))
        (fun (ij : ℕ × ℕ) x => T^[ij.1] f x * T^[ij.2] g x)
        fun ij _ => (hT.iter_sm hf _).mul (hT.iter_sm hg _)]
    funext x
    rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j => T^[i] f x * T^[j] g x) n]
    simp only [hT.mul _ _ (hT.iter_sm hf _) (hT.iter_sm hg _), mul_add, Finset.sum_add_distrib,
      Function.iterate_succ_apply']
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [← Nat.choose_symm_of_eq_add hij.symm]

/-- The Leibniz rule for `wirt`. -/
private lemma QSI_wirt_mul {f g : ℂ → ℂ} (hf : QSI_Sm f) (hg : QSI_Sm g) (a b : ℕ) :
    wirt a b (fun x => f x * g x) = fun x => ∑ aa ∈ Finset.HasAntidiagonal.antidiagonal a,
      ∑ bb ∈ Finset.HasAntidiagonal.antidiagonal b, ((a.choose aa.1 : ℕ) : ℂ) * ((b.choose bb.1 : ℕ) : ℂ) *
        (wirt aa.1 bb.1 f x * wirt aa.2 bb.2 g x) := by
  unfold wirt
  rw [QSI_Der_dWbar.leib hf hg b, QSI_Der_dW.iter_sum _ _ _
    (fun bb _ => (hf.itwb _).mul (hg.itwb _)) a]
  funext x
  simp only [QSI_Der_dW.leib (hf.itwb _) (hg.itwb _) a, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun aa _ => Finset.sum_congr rfl fun bb _ => ?_
  ring

/-- The second derivative applied to a fixed vector. -/
private lemma QSI_fderiv_apply {f : ℂ → ℂ} (hf : QSI_Sm f) (u z v : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ f y u) z v = fderiv ℝ (fderiv ℝ f) z v u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z := (hf.fd.differentiable (by simp)) z
  rw [fderiv_clm_apply hd (differentiableAt_const u)]
  simp

/-- The derivative of `(a + c b) / 2`. -/
private lemma QSI_fderiv_comb {a b : ℂ → ℂ} (ha : QSI_Sm a) (hb : QSI_Sm b) (c z v : ℂ) :
    fderiv ℝ (fun y => (a y + c * b y) / 2) z v = (fderiv ℝ a z v + c * fderiv ℝ b z v) / 2 := by
  have e : (fun y => (a y + c * b y) / 2) = fun y => (a y + c * b y) * (1 / 2) := by
    funext y; ring
  have hab : DifferentiableAt ℝ (fun y => a y + c * b y) z :=
    (ha.diff z).add ((hb.diff z).const_mul c)
  rw [e, fderiv_mul_const hab, fderiv_fun_add (ha.diff z) ((hb.diff z).const_mul c),
    fderiv_const_mul (hb.diff z) c]
  simp only [ContinuousLinearMap.smul_apply, _root_.add_apply, smul_eq_mul]
  ring

/-- The Wirtinger derivatives commute on smooth functions. -/
private lemma QSI_dW_dWbar {f : ℂ → ℂ} (hf : QSI_Sm f) : dW (dWbar f) = dWbar (dW f) := by
  funext z
  have hsym : IsSymmSndFDerivAt ℝ f z :=
    (hf.contDiffAt).isSymmSndFDerivAt (by simp)
  have e1 : dWbar f = fun y => (fderiv ℝ f y 1 + Complex.I * fderiv ℝ f y Complex.I) / 2 := rfl
  have e2 : dW f = fun y => (fderiv ℝ f y 1 + (-Complex.I) * fderiv ℝ f y Complex.I) / 2 := by
    funext y; simp only [dW]; ring
  have h1 := hf.fdu 1
  have hI := hf.fdu Complex.I
  simp only [dW, dWbar]
  rw [e1, e2, QSI_fderiv_comb h1 hI, QSI_fderiv_comb h1 hI, QSI_fderiv_comb h1 hI,
    QSI_fderiv_comb h1 hI]
  simp only [QSI_fderiv_apply hf]
  rw [hsym 1 Complex.I]
  ring

private lemma QSI_dWbar_iter_dW {f : ℂ → ℂ} (hf : QSI_Sm f) (b : ℕ) :
    dWbar (dW^[b] f) = dW^[b] (dWbar f) := by
  induction b generalizing f with
  | zero => rfl
  | succ b ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih hf.dw, QSI_dW_dWbar hf]

private lemma QSI_comm {f : ℂ → ℂ} (hf : QSI_Sm f) (a b : ℕ) :
    dWbar^[a] (dW^[b] f) = dW^[b] (dWbar^[a] f) := by
  induction a generalizing f with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, QSI_dWbar_iter_dW hf]
    exact ih hf.dwb

private lemma QSI_iter_conj {f : ℂ → ℂ} (hf : QSI_Sm f) (n : ℕ) :
    dWbar^[n] (fun x => starRingEnd ℂ (f x)) = (fun x => starRingEnd ℂ (dW^[n] f x)) ∧
      dW^[n] (fun x => starRingEnd ℂ (f x)) = (fun x => starRingEnd ℂ (dWbar^[n] f x)) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    constructor
    · rw [Function.iterate_succ_apply', ih.1]
      funext x
      rw [(dW_conj ((hf.itw n).diff x)).2, Function.iterate_succ_apply']
    · rw [Function.iterate_succ_apply', ih.2]
      funext x
      rw [(dW_conj ((hf.itwb n).diff x)).1, Function.iterate_succ_apply']

/-- `∂^a ∂̄^b f̄ = conj(∂^b ∂̄^a f)`. -/
private lemma QSI_wirt_conj {f : ℂ → ℂ} (hf : QSI_Sm f) (a b : ℕ) :
    wirt a b (fun x => starRingEnd ℂ (f x)) = fun x => starRingEnd ℂ (wirt b a f x) := by
  unfold wirt
  rw [(QSI_iter_conj hf b).1, (QSI_iter_conj (hf.itw b) a).2, QSI_comm hf a b]


/-! ### Slices -/

private lemma QSI_slice_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (w : ℂ) : (Matrix.of (setEntry h i j w)).IsHermitian := by
  have := symArr_isHermitian (setEntry h i j w)
  rwa [symArr_setEntry, symArr_of_isHermitian h hh] at this

private lemma QSI_contDiff_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) :
    ContDiff ℝ ∞ (fun w : ℂ => setEntry h i j w) := by
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  unfold setEntry
  by_cases h1 : i = j
  · by_cases h2 : k = i ∧ l = i
    · simp only [if_pos h1, if_pos h2]
      exact (Complex.ofRealCLM.comp Complex.reCLM).contDiff
    · simp only [if_pos h1, if_neg h2]
      exact contDiff_const
  · by_cases h2 : k = i ∧ l = j
    · simp only [if_neg h1, if_pos h2]
      exact contDiff_id
    · by_cases h3 : k = j ∧ l = i
      · simp only [if_neg h1, if_neg h2, if_pos h3]
        exact Complex.conjCLE.contDiff
      · simp only [if_neg h1, if_neg h2, if_neg h3]
        exact contDiff_const

private lemma QSI_Sm_resPoly {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) :
    QSI_Sm (fun w => resPolyEval P (setEntry h i j w)) := by
  have e : (fun w => resPolyEval P (setEntry h i j w)) =
      (fun h' => resPolyEval P (symArr h')) ∘ (fun w => setEntry h i j w) := by
    funext w
    simp only [Function.comp, symArr_setEntry, symArr_of_isHermitian h hh]
  rw [e]
  exact (contDiff_infty.2 fun n => contDiff_resPoly_symArr P hP n).comp (QSI_contDiff_slice h i j)

private lemma QSI_star_single {D N : ℕ} (p : Idx D N) :
    star (Pi.single p (1 : ℂ) : Idx D N → ℂ) = Pi.single p 1 := by
  funext s
  by_cases h : s = p <;> simp [h]

private lemma QSI_mulVec_single {D N : ℕ} (M : Matrix (Idx D N) (Idx D N) ℂ) (q p : Idx D N) :
    (M *ᵥ Pi.single q (1 : ℂ)) p = M p q := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

private lemma QSI_f_ee {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (p q : Idx D N) :
    resFactorEval (Pi.single p 1, Pi.single q 1, Λ, z) h = res (Matrix.of h + Λ) z p q := by
  unfold resFactorEval
  simp only
  rw [QSI_star_single, single_dotProduct, one_mul, QSI_mulVec_single]

private lemma QSI_f_eM {D N : ℕ} (Λ M : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (p q : Idx D N) :
    resFactorEval (Pi.single p 1, M *ᵥ Pi.single q 1, Λ, z) h =
      (res (Matrix.of h + Λ) z * M) p q := by
  unfold resFactorEval
  simp only
  rw [QSI_star_single, single_dotProduct, one_mul, Matrix.mulVec_mulVec, QSI_mulVec_single]

private lemma QSI_eval_single {D N : ℕ} (f : ResFactor D N) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval [((1 : ℂ), [f])] h = resFactorEval f h := by
  simp [resPolyEval, resMonoEval]

/-- A form along a slice is smooth. -/
private lemma QSI_Sm_form {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (x y : Idx D N → ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    QSI_Sm (fun w => resFactorEval (x, y, Λ, z) (setEntry h i j w)) := by
  have := QSI_Sm_resPoly h hh i j [((1 : ℂ), [(x, y, Λ, z)])] (by
    intro t ht f hf
    simp only [List.mem_singleton] at ht
    subst ht
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨hΛ, hz⟩)
  simpa only [QSI_eval_single] using this

/-- The derivatives of a form along the slice `w ↦ setEntry h i j w`. -/
private lemma QSI_dW_form {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (x y : Idx D N → ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    dW (fun w => resFactorEval (x, y, Λ, z) (setEntry h i j w)) = (fun w =>
        -(if i = j then (1 / 2 : ℂ) else 1) *
          (resFactorEval (x, Pi.single i 1, Λ, z) (setEntry h i j w) *
            resFactorEval (Pi.single j 1, y, Λ, z) (setEntry h i j w))) ∧
      dWbar (fun w => resFactorEval (x, y, Λ, z) (setEntry h i j w)) = (fun w =>
        -(if i = j then (1 / 2 : ℂ) else 1) *
          (resFactorEval (x, Pi.single j 1, Λ, z) (setEntry h i j w) *
            resFactorEval (Pi.single i 1, y, Λ, z) (setEntry h i j w))) := by
  have hP := resPoly_dW h hh i j [((1 : ℂ), [(x, y, Λ, z)])] (by
    intro t ht f hf
    simp only [List.mem_singleton] at ht
    subst ht
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨hΛ, hz⟩)
  simp only [QSI_eval_single] at hP
  rw [hP.1, hP.2]
  constructor <;> funext w <;> simp [resPolyD, resMonoD, resPolyEval, resMonoEval] <;> ring

/-! ### Matrix-valued functions -/

/-- Entrywise derivative of a matrix-valued function. -/
private def QSI_mD {ι : Type*} (T : (ℂ → ℂ) → (ℂ → ℂ)) (Φ : ℂ → Matrix ι ι ℂ) : ℂ → Matrix ι ι ℂ :=
  fun w => Matrix.of fun a b => T (fun w' => Φ w' a b) w

/-- Entrywise smoothness. -/
private def QSI_MSm {ι : Type*} (Φ : ℂ → Matrix ι ι ℂ) : Prop := ∀ a b, QSI_Sm (fun w => Φ w a b)

private lemma QSI_Der.one {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) : T (fun _ => 1) = fun _ => 0 := by
  have h := hT.mul (fun _ => 1) (fun _ => 1) (QSI_Sm.const 1) (QSI_Sm.const 1)
  simp only [mul_one, one_mul] at h
  funext x
  have := congrFun h x
  linear_combination -this

private lemma QSI_Der.const {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) (c : ℂ) :
    T (fun _ => c) = fun _ => 0 := by
  have h := hT.cmul c (fun _ => 1) (QSI_Sm.const 1)
  simp only [mul_one] at h
  rw [h, hT.one]
  funext x
  simp

private lemma QSI_Der.sub {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) {f g : ℂ → ℂ} (hf : QSI_Sm f)
    (hg : QSI_Sm g) : T (fun x => f x - g x) = fun x => T f x - T g x := by
  have e : (fun x => f x - g x) = fun x => f x + (-1) * g x := by funext x; ring
  rw [e, hT.add _ _ hf (hg.cmul (-1)), hT.cmul _ _ hg]
  funext x
  ring

private lemma QSI_MSm.add {ι : Type*} {Φ Ψ : ℂ → Matrix ι ι ℂ} (hΦ : QSI_MSm Φ) (hΨ : QSI_MSm Ψ) :
    QSI_MSm (fun w => Φ w + Ψ w) := fun a b => (hΦ a b).add (hΨ a b)

private lemma QSI_MSm.sub {ι : Type*} {Φ Ψ : ℂ → Matrix ι ι ℂ} (hΦ : QSI_MSm Φ) (hΨ : QSI_MSm Ψ) :
    QSI_MSm (fun w => Φ w - Ψ w) := fun a b => by
  have := (hΦ a b).add ((hΨ a b).cmul (-1))
  simpa [sub_eq_add_neg] using this

private lemma QSI_MSm.mul {ι : Type*} [Fintype ι] {Φ Ψ : ℂ → Matrix ι ι ℂ} (hΦ : QSI_MSm Φ)
    (hΨ : QSI_MSm Ψ) : QSI_MSm (fun w => Φ w * Ψ w) := fun a b => by
  simp only [Matrix.mul_apply]
  exact QSI_Sm.sum _ fun m _ => (hΦ a m).mul (hΨ m b)

private lemma QSI_MSm.const {ι : Type*} (M : Matrix ι ι ℂ) : QSI_MSm (fun _ => M) :=
  fun _ _ => QSI_Sm.const _

private lemma QSI_MSm.smul {ι : Type*} {Φ : ℂ → Matrix ι ι ℂ} (s : ℂ → ℂ) (hs : QSI_Sm s)
    (hΦ : QSI_MSm Φ) : QSI_MSm (fun w => s w • Φ w) := fun a b => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hs.mul (hΦ a b)

private lemma QSI_MSm.sum {ι κ : Type*} (s : Finset κ) {Φ : κ → ℂ → Matrix ι ι ℂ}
    (hΦ : ∀ t ∈ s, QSI_MSm (Φ t)) : QSI_MSm (fun w => ∑ t ∈ s, Φ t w) := fun a b => by
  simp only [Matrix.sum_apply]
  exact QSI_Sm.sum s fun t ht => hΦ t ht a b

private lemma QSI_MSm.trace {ι : Type*} [Fintype ι] {Φ : ℂ → Matrix ι ι ℂ} (hΦ : QSI_MSm Φ) :
    QSI_Sm (fun w => (Φ w).trace) := by
  simp only [Matrix.trace, Matrix.diag]
  exact QSI_Sm.sum _ fun a _ => hΦ a a

section
variable {ι : Type*} {T : (ℂ → ℂ) → (ℂ → ℂ)}

private lemma QSI_mD_add (hT : QSI_Der T) {Φ Ψ : ℂ → Matrix ι ι ℂ} (hΦ : QSI_MSm Φ) (hΨ : QSI_MSm Ψ) :
    QSI_mD T (fun w => Φ w + Ψ w) = fun w => QSI_mD T Φ w + QSI_mD T Ψ w := by
  funext w; ext a b
  simp only [QSI_mD, Matrix.of_apply, Matrix.add_apply]
  rw [hT.add _ _ (hΦ a b) (hΨ a b)]

private lemma QSI_mD_sub (hT : QSI_Der T) {Φ Ψ : ℂ → Matrix ι ι ℂ} (hΦ : QSI_MSm Φ) (hΨ : QSI_MSm Ψ) :
    QSI_mD T (fun w => Φ w - Ψ w) = fun w => QSI_mD T Φ w - QSI_mD T Ψ w := by
  funext w; ext a b
  simp only [QSI_mD, Matrix.of_apply, Matrix.sub_apply]
  rw [hT.sub (hΦ a b) (hΨ a b)]

private lemma QSI_mD_mul [Fintype ι] (hT : QSI_Der T) {Φ Ψ : ℂ → Matrix ι ι ℂ} (hΦ : QSI_MSm Φ)
    (hΨ : QSI_MSm Ψ) :
    QSI_mD T (fun w => Φ w * Ψ w) = fun w => QSI_mD T Φ w * Ψ w + Φ w * QSI_mD T Ψ w := by
  funext w; ext a b
  simp only [QSI_mD, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  have e : (fun w' => ∑ m, Φ w' a m * Ψ w' m b) = fun w' => ∑ m, (1 : ℂ) * (Φ w' a m * Ψ w' m b) :=
    by funext w'; simp
  rw [e, hT.sum _ (fun _ => 1) _ fun m _ => (hΦ a m).mul (hΨ m b)]
  simp only [one_mul, hT.mul _ _ (hΦ _ _) (hΨ _ _), Finset.sum_add_distrib]

private lemma QSI_mD_const (hT : QSI_Der T) (M : Matrix ι ι ℂ) : QSI_mD T (fun _ => M) = fun _ => 0 := by
  funext w; ext a b
  simp only [QSI_mD, Matrix.of_apply, Matrix.zero_apply]
  rw [hT.const]

private lemma QSI_mD_cmul (hT : QSI_Der T) (c : ℂ) {Φ : ℂ → Matrix ι ι ℂ} (hΦ : QSI_MSm Φ) :
    QSI_mD T (fun w => c • Φ w) = fun w => c • QSI_mD T Φ w := by
  funext w; ext a b
  simp only [QSI_mD, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hT.cmul _ _ (hΦ a b)]

private lemma QSI_mD_smul (hT : QSI_Der T) (s : ℂ → ℂ) (hs : QSI_Sm s) {Φ : ℂ → Matrix ι ι ℂ}
    (hΦ : QSI_MSm Φ) :
    QSI_mD T (fun w => s w • Φ w) = fun w => T s w • Φ w + s w • QSI_mD T Φ w := by
  funext w; ext a b
  simp only [QSI_mD, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
  rw [hT.mul _ _ hs (hΦ a b)]

private lemma QSI_mD_sum (hT : QSI_Der T) {κ : Type*} (s : Finset κ) {Φ : κ → ℂ → Matrix ι ι ℂ}
    (hΦ : ∀ t ∈ s, QSI_MSm (Φ t)) :
    QSI_mD T (fun w => ∑ t ∈ s, Φ t w) = fun w => ∑ t ∈ s, QSI_mD T (Φ t) w := by
  funext w; ext a b
  simp only [QSI_mD, Matrix.of_apply, Matrix.sum_apply]
  have e : (fun w' => ∑ t ∈ s, Φ t w' a b) = fun w' => ∑ t ∈ s, (1 : ℂ) * Φ t w' a b := by
    funext w'; simp
  rw [e, hT.sum s (fun _ => 1) _ fun t ht => hΦ t ht a b]
  simp

private lemma QSI_mD_trace [Fintype ι] (hT : QSI_Der T) {Φ : ℂ → Matrix ι ι ℂ} (hΦ : QSI_MSm Φ) :
    T (fun w => (Φ w).trace) = fun w => (QSI_mD T Φ w).trace := by
  simp only [Matrix.trace, Matrix.diag]
  have e : (fun w => ∑ a, Φ w a a) = fun w => ∑ a, (1 : ℂ) * Φ w a a := by funext w; simp
  rw [e, hT.sum _ (fun _ => 1) _ fun a _ => hΦ a a]
  funext w
  simp [QSI_mD]

end

/-! ### `S_θ` and the coefficients `c_a` -/

/-- The coefficient of the entries of `S_θ`. -/
private def QSI_kap (D N : ℕ) (θ : ℝ) (r m : Idx D N) : ℂ :=
  (θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = m.1 then 1 else 0) + ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹

private lemma QSI_ntr_eq (D N : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr M = ((D : ℂ) * N)⁻¹ * ∑ r, M r r := by
  simp [ntr, Matrix.trace, Fintype.card_prod]

private lemma QSI_sTheta_apply (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ) (p q : Idx D N) :
    sTheta D N θ R p q = if p = q then ∑ r, QSI_kap D N θ r p * R r r else 0 := by
  have hD : (D : ℂ) ≠ 0 := by
    have : 0 < D := p.1.pos
    exact_mod_cast this.ne'
  have hDn : (D : ℂ) * ((D : ℂ) * N)⁻¹ = (N : ℂ)⁻¹ := by
    field_simp
  have hblk : ∀ a : Fin D, (D : ℂ) * ntr (R * Ea D N a) =
      (N : ℂ)⁻¹ * ∑ r, (if r.1 = a then R r r else 0) := by
    intro a
    rw [QSI_ntr_eq]
    have : ∑ r, (R * Ea D N a) r r = ∑ r, (if r.1 = a then R r r else 0) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp [Ea, Matrix.mul_diagonal]
    rw [this, ← hDn]
    ring
  by_cases h : p = q
  · subst h
    have hEa : ∀ a : Fin D, Ea D N a p p = if p.1 = a then (1 : ℂ) else 0 := by
      intro a
      simp [Ea]
    simp only [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, hEa,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, ite_true]
    have e1 : ∑ a : Fin D, (D : ℂ) * ntr (R * Ea D N a) * (if p.1 = a then (1 : ℂ) else 0) =
        (D : ℂ) * ntr (R * Ea D N p.1) := by
      simp [Finset.sum_ite_eq]
    rw [e1, hblk, QSI_ntr_eq]
    simp only [QSI_kap, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    have e2 : ∀ r : Idx D N, (θ : ℂ) * (N : ℂ)⁻¹ * (if r.1 = p.1 then (1 : ℂ) else 0) * R r r =
        (θ : ℂ) * ((N : ℂ)⁻¹ * if r.1 = p.1 then R r r else 0) := by
      intro r
      split_ifs <;> ring
    simp only [e2]
    push_cast
    simp only [mul_assoc]
  · simp [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Ea, h]

private lemma QSI_sTheta_smul (D N : ℕ) (θ : ℝ) (c : ℂ) (R : Matrix (Idx D N) (Idx D N) ℂ) :
    sTheta D N θ (c • R) = c • sTheta D N θ R := by
  ext p q
  simp only [QSI_sTheta_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  · simp

private lemma QSI_MSm.sTheta {D N : ℕ} (θ : ℝ) {Φ : ℂ → Matrix (Idx D N) (Idx D N) ℂ}
    (hΦ : QSI_MSm Φ) : QSI_MSm (fun w => sTheta D N θ (Φ w)) := fun p q => by
  simp only [QSI_sTheta_apply]
  by_cases h : p = q
  · simp only [h, ite_true]
    exact QSI_Sm.sum _ fun r _ => (hΦ r r).cmul _
  · simp only [h, ite_false]
    exact QSI_Sm.const 0

private lemma QSI_mD_sTheta {D N : ℕ} {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) (θ : ℝ)
    {Φ : ℂ → Matrix (Idx D N) (Idx D N) ℂ} (hΦ : QSI_MSm Φ) :
    QSI_mD T (fun w => sTheta D N θ (Φ w)) = fun w => sTheta D N θ (QSI_mD T Φ w) := by
  funext w; ext p q
  simp only [QSI_mD, Matrix.of_apply, QSI_sTheta_apply]
  by_cases h : p = q
  · simp only [h, ite_true]
    rw [hT.sum _ _ _ fun r _ => hΦ r r]
  · simp only [h, ite_false]
    rw [hT.const]

/-- The coefficient `c_a(R) = θ N⁻¹ tr(E_a R B) + (1 - θ)(DN)⁻¹ tr(R B)` of `Q`. -/
private def QSI_cA (D N : ℕ) (θ : ℝ) (B : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D)
    (R : Matrix (Idx D N) (Idx D N) ℂ) : ℂ :=
  (θ : ℂ) * (N : ℂ)⁻¹ * (Ea D N a * R * B).trace +
    ((1 - θ : ℝ) : ℂ) * ((D : ℂ) * N)⁻¹ * (R * B).trace

private lemma QSI_cA_smul (D N : ℕ) (θ : ℝ) (B : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D) (c : ℂ)
    (R : Matrix (Idx D N) (Idx D N) ℂ) : QSI_cA D N θ B a (c • R) = c * QSI_cA D N θ B a R := by
  simp only [QSI_cA, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ring

private lemma QSI_Sm_cA {D N : ℕ} (θ : ℝ) (B : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D)
    {Φ : ℂ → Matrix (Idx D N) (Idx D N) ℂ} (hΦ : QSI_MSm Φ) :
    QSI_Sm (fun w => QSI_cA D N θ B a (Φ w)) := by
  unfold QSI_cA
  exact (((QSI_MSm.const _).mul hΦ).mul (QSI_MSm.const B)).trace.cmul _ |>.add
    ((hΦ.mul (QSI_MSm.const B)).trace.cmul _)

private lemma QSI_T_cA {D N : ℕ} {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) (θ : ℝ)
    (B : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D) {Φ : ℂ → Matrix (Idx D N) (Idx D N) ℂ}
    (hΦ : QSI_MSm Φ) :
    T (fun w => QSI_cA D N θ B a (Φ w)) = fun w => QSI_cA D N θ B a (QSI_mD T Φ w) := by
  unfold QSI_cA
  have h1 : QSI_MSm (fun w => Ea D N a * Φ w * B) := ((QSI_MSm.const _).mul hΦ).mul
    (QSI_MSm.const B)
  have h2 : QSI_MSm (fun w => Φ w * B) := hΦ.mul (QSI_MSm.const B)
  rw [hT.add _ _ (h1.trace.cmul _) (h2.trace.cmul _), hT.cmul _ _ h1.trace,
    hT.cmul _ _ h2.trace, QSI_mD_trace hT h1, QSI_mD_trace hT h2,
    QSI_mD_mul hT ((QSI_MSm.const _).mul hΦ) (QSI_MSm.const B),
    QSI_mD_mul hT (QSI_MSm.const _) hΦ, QSI_mD_mul hT hΦ (QSI_MSm.const B)]
  simp only [QSI_mD_const hT]
  funext w
  simp


/-! ### part c -/

private lemma QSI_mul_single_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (A C : Matrix ι ι ℂ)
    (x y k l : ι) : (A * Matrix.single x y (1 : ℂ) * C) k l = A k x * C y l := by
  have h1 : ∀ m, (A * Matrix.single x y (1 : ℂ)) k m = if y = m then A k x else 0 := by
    intro m
    rw [Matrix.mul_apply]
    by_cases hm : y = m
    · subst hm
      rw [Finset.sum_eq_single x]
      · simp [Matrix.single_apply]
      · intro b _ hb; simp [Matrix.single_apply, Ne.symm hb]
      · simp
    · simp [Matrix.single_apply, hm]
  rw [Matrix.mul_apply]
  simp only [h1, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- The resolvent along a slice. -/
private def QSI_G {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (w : ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  res (Matrix.of (setEntry h i j w) + Λ) z

section
variable {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N)
  (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
include hh hΛ hz

private lemma QSI_MSm_G : QSI_MSm (QSI_G h i j Λ z) := fun a b => by
  have := QSI_Sm_form h hh i j (Pi.single a 1) (Pi.single b 1) Λ hΛ z hz.ne'
  simpa only [QSI_f_ee, QSI_G] using this

private lemma QSI_mD_G :
    QSI_mD dW (QSI_G h i j Λ z) = (fun w => (-(if i = j then (1 / 2 : ℂ) else 1)) •
        (QSI_G h i j Λ z w * Matrix.single i j 1 * QSI_G h i j Λ z w)) ∧
      QSI_mD dWbar (QSI_G h i j Λ z) = (fun w => (-(if i = j then (1 / 2 : ℂ) else 1)) •
        (QSI_G h i j Λ z w * Matrix.single j i 1 * QSI_G h i j Λ z w)) := by
  constructor <;> funext w <;> ext a b
  · have := (res_dW Λ hΛ z hz.ne' h hh i j a b).1
    simp only [QSI_mD, Matrix.of_apply, QSI_G, this, Matrix.smul_apply, smul_eq_mul,
      QSI_mul_single_mul]
  · have := (res_dW Λ hΛ z hz.ne' h hh i j a b).2
    simp only [QSI_mD, Matrix.of_apply, QSI_G, this, Matrix.smul_apply, smul_eq_mul,
      QSI_mul_single_mul]

end

/-- `Φ(R) = R B - R B L R + R B S_θ(R) R + Σ_a c_a(R) R E_a R`, so that `DN Q = Φ(G)` with
`L = Λ - z`. -/
private def QSI_Phi (D N : ℕ) (θ : ℝ) (B L : Matrix (Idx D N) (Idx D N) ℂ)
    (R : Matrix (Idx D N) (Idx D N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  R * B - R * B * L * R + R * B * sTheta D N θ R * R +
    ∑ a, QSI_cA D N θ B a R • (R * Ea D N a * R)

/-- The derivative of `Φ` at `R` in the direction `M`. -/
private def QSI_dPhi (D N : ℕ) (θ : ℝ) (B L : Matrix (Idx D N) (Idx D N) ℂ)
    (R M : Matrix (Idx D N) (Idx D N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  M * B - (M * B * L * R + R * B * L * M) +
    (M * B * sTheta D N θ R * R + R * B * sTheta D N θ M * R + R * B * sTheta D N θ R * M) +
    ∑ a, (QSI_cA D N θ B a M • (R * Ea D N a * R) +
      QSI_cA D N θ B a R • (M * Ea D N a * R + R * Ea D N a * M))

/-- The remainder `Ψ(R) = R B E R - R B S_θ(R E R) R - Σ_a c_a(R E R) R E_a R`. -/
private def QSI_Psi (D N : ℕ) (θ : ℝ) (B E : Matrix (Idx D N) (Idx D N) ℂ)
    (R : Matrix (Idx D N) (Idx D N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  R * B * E * R - R * B * sTheta D N θ (R * E * R) * R -
    ∑ a, QSI_cA D N θ B a (R * E * R) • (R * Ea D N a * R)

section
variable {T : (ℂ → ℂ) → (ℂ → ℂ)} {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma QSI_mD_mul3 (hT : QSI_Der T) {A B C : ℂ → Matrix ι ι ℂ} (hA : QSI_MSm A)
    (hB : QSI_MSm B) (hC : QSI_MSm C) :
    QSI_mD T (fun w => A w * B w * C w) = fun w =>
      QSI_mD T A w * B w * C w + A w * QSI_mD T B w * C w + A w * B w * QSI_mD T C w := by
  rw [QSI_mD_mul hT (hA.mul hB) hC, QSI_mD_mul hT hA hB]
  funext w
  simp only [Matrix.add_mul]

private lemma QSI_mD_mul4 (hT : QSI_Der T) {A B C E : ℂ → Matrix ι ι ℂ} (hA : QSI_MSm A)
    (hB : QSI_MSm B) (hC : QSI_MSm C) (hE : QSI_MSm E) :
    QSI_mD T (fun w => A w * B w * C w * E w) = fun w =>
      QSI_mD T A w * B w * C w * E w + A w * QSI_mD T B w * C w * E w +
        A w * B w * QSI_mD T C w * E w + A w * B w * C w * QSI_mD T E w := by
  rw [QSI_mD_mul hT ((hA.mul hB).mul hC) hE, QSI_mD_mul3 hT hA hB hC]
  funext w
  simp only [Matrix.add_mul]

end

private lemma QSI_MSm_Phi {D N : ℕ} (θ : ℝ) (B L : Matrix (Idx D N) (Idx D N) ℂ)
    {Φ : ℂ → Matrix (Idx D N) (Idx D N) ℂ} (hΦ : QSI_MSm Φ) :
    QSI_MSm (fun w => QSI_Phi D N θ B L (Φ w)) := by
  unfold QSI_Phi
  have hB := QSI_MSm.const B
  have hL := QSI_MSm.const L
  exact (((hΦ.mul hB).sub (((hΦ.mul hB).mul hL).mul hΦ)).add
    (((hΦ.mul hB).mul (hΦ.sTheta θ)).mul hΦ)).add
    (QSI_MSm.sum _ fun a _ => QSI_MSm.smul _ (QSI_Sm_cA θ B a hΦ)
      ((hΦ.mul (QSI_MSm.const _)).mul hΦ))

private lemma QSI_mD_Phi {D N : ℕ} {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) (θ : ℝ)
    (B L : Matrix (Idx D N) (Idx D N) ℂ) {Φ : ℂ → Matrix (Idx D N) (Idx D N) ℂ}
    (hΦ : QSI_MSm Φ) :
    QSI_mD T (fun w => QSI_Phi D N θ B L (Φ w)) =
      fun w => QSI_dPhi D N θ B L (Φ w) (QSI_mD T Φ w) := by
  have hB := QSI_MSm.const B
  have hL := QSI_MSm.const L
  have hEa : ∀ a, QSI_MSm (fun _ : ℂ => Ea D N a) := fun a => QSI_MSm.const _
  have hS := hΦ.sTheta θ
  have e : (fun w => QSI_Phi D N θ B L (Φ w)) = fun w =>
      Φ w * B - Φ w * B * L * Φ w + Φ w * B * sTheta D N θ (Φ w) * Φ w +
        ∑ a, QSI_cA D N θ B a (Φ w) • (Φ w * Ea D N a * Φ w) := rfl
  rw [e, QSI_mD_add hT (((hΦ.mul hB).sub (((hΦ.mul hB).mul hL).mul hΦ)).add
      (((hΦ.mul hB).mul hS).mul hΦ))
      (QSI_MSm.sum _ fun a _ => QSI_MSm.smul _ (QSI_Sm_cA θ B a hΦ) ((hΦ.mul (hEa a)).mul hΦ)),
    QSI_mD_add hT ((hΦ.mul hB).sub (((hΦ.mul hB).mul hL).mul hΦ)) (((hΦ.mul hB).mul hS).mul hΦ),
    QSI_mD_sub hT (hΦ.mul hB) (((hΦ.mul hB).mul hL).mul hΦ),
    QSI_mD_mul hT hΦ hB, QSI_mD_mul4 hT hΦ hB hL hΦ, QSI_mD_mul4 hT hΦ hB hS hΦ,
    QSI_mD_sTheta hT θ hΦ,
    QSI_mD_sum hT _ fun a _ => QSI_MSm.smul _ (QSI_Sm_cA θ B a hΦ) ((hΦ.mul (hEa a)).mul hΦ)]
  simp only [QSI_mD_smul hT _ (QSI_Sm_cA θ B _ hΦ) ((hΦ.mul (hEa _)).mul hΦ),
    QSI_mD_mul3 hT hΦ (hEa _) hΦ, QSI_T_cA hT θ B _ hΦ, QSI_mD_const hT]
  funext w
  simp only [QSI_dPhi, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private lemma QSI_alg0 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (R B L E S0 S1 : Matrix ι ι ℂ) (f g : κ → ℂ) (Ea' : κ → Matrix ι ι ℂ) (c : ℂ) :
    (-c) • (R * E * R) * B - ((-c) • (R * E * R) * B * L * R + R * B * L * ((-c) • (R * E * R))) +
      ((-c) • (R * E * R) * B * S0 * R + R * B * ((-c) • S1) * R +
        R * B * S0 * ((-c) • (R * E * R))) +
      ∑ a, (((-c) * g a) • (R * Ea' a * R) +
        f a • ((-c) • (R * E * R) * Ea' a * R + R * Ea' a * ((-c) • (R * E * R)))) =
    (-c) • (R * E * (R * B - R * B * L * R + R * B * S0 * R + ∑ a, f a • (R * Ea' a * R)) +
        (R * B - R * B * L * R + R * B * S0 * R + ∑ a, f a • (R * Ea' a * R)) * E * R) +
      c • (R * B * E * R - R * B * S1 * R - ∑ a, g a • (R * Ea' a * R)) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, Finset.smul_sum,
    smul_smul, Matrix.mul_assoc, Finset.sum_add_distrib, neg_mul, neg_smul, Finset.sum_neg_distrib,
    mul_comm c, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
  abel

/-- The algebraic identity behind the derivative of `Q` for the profile `S_θ`. -/
private lemma QSI_alg {D N : ℕ} (θ : ℝ) (B L E R : Matrix (Idx D N) (Idx D N) ℂ) (c : ℂ) :
    QSI_dPhi D N θ B L R ((-c) • (R * E * R)) =
      (-c) • (R * E * QSI_Phi D N θ B L R + QSI_Phi D N θ B L R * E * R) +
        c • QSI_Psi D N θ B E R := by
  simp only [QSI_dPhi, QSI_Phi, QSI_Psi, QSI_sTheta_smul, QSI_cA_smul]
  exact QSI_alg0 R B L E (sTheta D N θ R) (sTheta D N θ (R * E * R)) (fun a => QSI_cA D N θ B a R)
    (fun a => QSI_cA D N θ B a (R * E * R)) (Ea D N) c


private lemma QSI_hgUnder_eq (D N : ℕ) (θ : ℝ) (H Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hH : H.IsHermitian) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    hgUnder D N θ H Λ z = 1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (H + Λ) z +
      sTheta D N θ (res (H + Λ) z) * res (H + Λ) z := by
  have hres := (res_mul_sub (H + Λ) (hH.add hΛ) z hz).1
  have hHG : H * res (H + Λ) z = 1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
      res (H + Λ) z := by
    have : H * res (H + Λ) z = (H + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
        res (H + Λ) z - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (H + Λ) z := by
      rw [← Matrix.sub_mul]
      congr 1
      abel
    rw [this, hres]
  unfold hgUnder
  rw [hHG]

/-- `Q = (DN)⁻¹ Φ(G)` for Hermitian `H`. -/
private lemma QSI_qMat_eq (D N : ℕ) (θ : ℝ) (H Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hH : H.IsHermitian) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    qMat D N θ H Λ B z = ((D : ℂ) * N)⁻¹ •
      QSI_Phi D N θ B (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) (res (H + Λ) z) := by
  unfold qMat QSI_Phi
  rw [QSI_hgUnder_eq D N θ H Λ hH hΛ z hz]
  congr 1
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc,
    QSI_cA]

section
variable {D N : ℕ} (θ : ℝ) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
  (i j : Idx D N) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
  (hz : 0 < z.im)
include hh hΛ hz

private lemma QSI_qMat_slice :
    (fun w => qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z) = fun w => ((D : ℂ) * N)⁻¹ •
      QSI_Phi D N θ B (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) (QSI_G h i j Λ z w) := by
  funext w
  exact QSI_qMat_eq D N θ _ Λ B (QSI_slice_herm h hh i j w) hΛ z hz

private lemma QSI_MSm_Q : QSI_MSm (fun w => qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z) := by
  rw [QSI_qMat_slice θ h hh i j Λ B hΛ z hz]
  exact QSI_MSm.smul _ (QSI_Sm.const _) (QSI_MSm_Phi θ B _ (QSI_MSm_G h hh i j Λ hΛ z hz))

/-- The derivative of `Q` for the profile `S_θ` ((2.30) [eq:HGline]), at the level of matrices: the derivative of
`Q` in the direction `E` is `-c (G E Q + Q E G) + c (DN)⁻¹ Ψ_E(G)`. -/
private lemma QSI_mD_Q :
    QSI_mD dW (fun w => qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z) = (fun w =>
        (-(if i = j then (1 / 2 : ℂ) else 1)) •
          (QSI_G h i j Λ z w * Matrix.single i j 1 *
              qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z +
            qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z * Matrix.single i j 1 *
              QSI_G h i j Λ z w) +
          (if i = j then (1 / 2 : ℂ) else 1) • (((D : ℂ) * N)⁻¹ •
            QSI_Psi D N θ B (Matrix.single i j 1) (QSI_G h i j Λ z w))) ∧
    QSI_mD dWbar (fun w => qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z) = (fun w =>
        (-(if i = j then (1 / 2 : ℂ) else 1)) •
          (QSI_G h i j Λ z w * Matrix.single j i 1 *
              qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z +
            qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z * Matrix.single j i 1 *
              QSI_G h i j Λ z w) +
          (if i = j then (1 / 2 : ℂ) else 1) • (((D : ℂ) * N)⁻¹ •
            QSI_Psi D N θ B (Matrix.single j i 1) (QSI_G h i j Λ z w))) := by
  have hG := QSI_MSm_G h hh i j Λ hΛ z hz
  have hP := QSI_MSm_Phi θ B (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) hG
  obtain ⟨d1, d2⟩ := QSI_mD_G h hh i j Λ hΛ z hz
  have hq := fun w => congrFun (QSI_qMat_slice θ h hh i j Λ B hΛ z hz) w
  rw [QSI_qMat_slice θ h hh i j Λ B hΛ z hz]
  constructor
  · rw [QSI_mD_cmul QSI_Der_dW _ hP, QSI_mD_Phi QSI_Der_dW θ B _ hG, d1]
    funext w
    simp only [Pi.smul_apply]
    rw [QSI_alg, hq w]
    simp only [smul_add, Matrix.mul_smul, Matrix.smul_mul, smul_comm ((D : ℂ) * N)⁻¹]
  · rw [QSI_mD_cmul QSI_Der_dWbar _ hP, QSI_mD_Phi QSI_Der_dWbar θ B _ hG, d2]
    funext w
    simp only [Pi.smul_apply]
    rw [QSI_alg, hq w]
    simp only [smul_add, Matrix.mul_smul, Matrix.smul_mul, smul_comm ((D : ℂ) * N)⁻¹]

end

/-- The derivative of `Ψ_E` at `R` in the direction `M`. -/
private def QSI_dPsi (D N : ℕ) (θ : ℝ) (B E : Matrix (Idx D N) (Idx D N) ℂ)
    (R M : Matrix (Idx D N) (Idx D N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  M * B * E * R + R * B * E * M -
    (M * B * sTheta D N θ (R * E * R) * R + R * B * sTheta D N θ (M * E * R + R * E * M) * R +
      R * B * sTheta D N θ (R * E * R) * M) -
    ∑ a, (QSI_cA D N θ B a (M * E * R + R * E * M) • (R * Ea D N a * R) +
      QSI_cA D N θ B a (R * E * R) • (M * Ea D N a * R + R * Ea D N a * M))

private lemma QSI_MSm_Psi {D N : ℕ} (θ : ℝ) (B E : Matrix (Idx D N) (Idx D N) ℂ)
    {Φ : ℂ → Matrix (Idx D N) (Idx D N) ℂ} (hΦ : QSI_MSm Φ) :
    QSI_MSm (fun w => QSI_Psi D N θ B E (Φ w)) := by
  unfold QSI_Psi
  have hB := QSI_MSm.const B
  have hE := QSI_MSm.const E
  have hRER := (hΦ.mul hE).mul hΦ
  exact ((((hΦ.mul hB).mul hE).mul hΦ).sub (((hΦ.mul hB).mul (hRER.sTheta θ)).mul hΦ)).sub
    (QSI_MSm.sum _ fun a _ => QSI_MSm.smul _ (QSI_Sm_cA θ B a hRER)
      ((hΦ.mul (QSI_MSm.const _)).mul hΦ))

private lemma QSI_mD_Psi {D N : ℕ} {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) (θ : ℝ)
    (B E : Matrix (Idx D N) (Idx D N) ℂ) {Φ : ℂ → Matrix (Idx D N) (Idx D N) ℂ}
    (hΦ : QSI_MSm Φ) :
    QSI_mD T (fun w => QSI_Psi D N θ B E (Φ w)) =
      fun w => QSI_dPsi D N θ B E (Φ w) (QSI_mD T Φ w) := by
  have hB := QSI_MSm.const B
  have hE := QSI_MSm.const E
  have hEa : ∀ a, QSI_MSm (fun _ : ℂ => Ea D N a) := fun a => QSI_MSm.const _
  have hRER := (hΦ.mul hE).mul hΦ
  have hS := hRER.sTheta θ
  have e : (fun w => QSI_Psi D N θ B E (Φ w)) = fun w =>
      Φ w * B * E * Φ w - Φ w * B * sTheta D N θ (Φ w * E * Φ w) * Φ w -
        ∑ a, QSI_cA D N θ B a (Φ w * E * Φ w) • (Φ w * Ea D N a * Φ w) := rfl
  rw [e, QSI_mD_sub hT ((((hΦ.mul hB).mul hE).mul hΦ).sub (((hΦ.mul hB).mul hS).mul hΦ))
      (QSI_MSm.sum _ fun a _ => QSI_MSm.smul _ (QSI_Sm_cA θ B a hRER) ((hΦ.mul (hEa a)).mul hΦ)),
    QSI_mD_sub hT (((hΦ.mul hB).mul hE).mul hΦ) (((hΦ.mul hB).mul hS).mul hΦ),
    QSI_mD_mul4 hT hΦ hB hE hΦ, QSI_mD_mul4 hT hΦ hB hS hΦ,
    QSI_mD_sTheta hT θ hRER, QSI_mD_mul3 hT hΦ hE hΦ,
    QSI_mD_sum hT _ fun a _ => QSI_MSm.smul _ (QSI_Sm_cA θ B a hRER) ((hΦ.mul (hEa a)).mul hΦ)]
  simp only [QSI_mD_smul hT _ (QSI_Sm_cA θ B _ hRER) ((hΦ.mul (hEa _)).mul hΦ),
    QSI_mD_mul3 hT hΦ (hEa _) hΦ, QSI_T_cA hT θ B _ hRER, QSI_mD_mul3 hT hΦ hE hΦ,
    QSI_mD_const hT]
  funext w
  simp only [QSI_dPsi, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

section
variable {D N : ℕ} (θ : ℝ) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
  (i j : Idx D N) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
  (hz : 0 < z.im)
include hh hΛ hz

/-- The second derivatives of `Q`: the derivative `T'` of the identity `QSI_mD_Q` for `T`. -/
private lemma QSI_mD2_Q {T T' : (ℂ → ℂ) → (ℂ → ℂ)} (hT' : QSI_Der T') (E : Matrix (Idx D N) (Idx D N) ℂ)
    (c : ℂ)
    (hQ : QSI_mD T (fun w => qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z) = (fun w =>
        (-c) • (QSI_G h i j Λ z w * E * qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z +
            qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z * E * QSI_G h i j Λ z w) +
          c • (((D : ℂ) * N)⁻¹ • QSI_Psi D N θ B E (QSI_G h i j Λ z w)))) :
    QSI_mD T' (QSI_mD T (fun w => qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z)) = (fun w =>
        (-c) • (QSI_mD T' (QSI_G h i j Λ z) w * E *
              qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z +
            QSI_G h i j Λ z w * E *
              QSI_mD T' (fun w => qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z) w +
            QSI_mD T' (fun w => qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z) w * E *
              QSI_G h i j Λ z w +
            qMat D N θ (Matrix.of (setEntry h i j w)) Λ B z * E *
              QSI_mD T' (QSI_G h i j Λ z) w) +
          c • (((D : ℂ) * N)⁻¹ •
            QSI_dPsi D N θ B E (QSI_G h i j Λ z w) (QSI_mD T' (QSI_G h i j Λ z) w))) := by
  have hG := QSI_MSm_G h hh i j Λ hΛ z hz
  have hQm := QSI_MSm_Q θ h hh i j Λ B hΛ z hz
  have hE := QSI_MSm.const E
  have hPs := QSI_MSm_Psi θ B E hG
  rw [hQ, QSI_mD_add hT' (QSI_MSm.smul _ (QSI_Sm.const _) (((hG.mul hE).mul hQm).add
      ((hQm.mul hE).mul hG))) (QSI_MSm.smul _ (QSI_Sm.const _)
        (QSI_MSm.smul _ (QSI_Sm.const _) hPs)),
    QSI_mD_cmul hT' _ (((hG.mul hE).mul hQm).add ((hQm.mul hE).mul hG)),
    QSI_mD_cmul hT' _ (QSI_MSm.smul _ (QSI_Sm.const _) hPs), QSI_mD_cmul hT' _ hPs,
    QSI_mD_add hT' ((hG.mul hE).mul hQm) ((hQm.mul hE).mul hG), QSI_mD_mul3 hT' hG hE hQm,
    QSI_mD_mul3 hT' hQm hE hG, QSI_mD_Psi hT' θ B E hG, QSI_mD_const hT']
  funext w
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, add_assoc]

end


/-! ### part d -/

private lemma QSI_msm' {ι : Type*} [Fintype ι] [DecidableEq ι] (A C : Matrix ι ι ℂ) (x y k l : ι) :
    (A * (Matrix.single x y (1 : ℂ) * C)) k l = A k x * C y l := by
  rw [← Matrix.mul_assoc, QSI_mul_single_mul]

private lemma QSI_kap_norm (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (r m : Idx D N) :
    ‖QSI_kap D N θ r m‖ ≤ (N : ℝ)⁻¹ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast r.2.pos
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast r.1.pos
  have h1 : 0 ≤ 1 - θ := by linarith
  have e : QSI_kap D N θ r m = ((θ * (N : ℝ)⁻¹ * (if r.1 = m.1 then 1 else 0) +
      (1 - θ) * ((D : ℝ) * N)⁻¹ : ℝ) : ℂ) := by
    unfold QSI_kap; push_cast; split_ifs <;> simp
  have hDN : ((D : ℝ) * N)⁻¹ ≤ (N : ℝ)⁻¹ := by
    rw [mul_inv]
    have : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
    nlinarith [inv_pos.2 hN]
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
  split_ifs <;> nlinarith [inv_pos.2 hN]

private lemma QSI_sum_mul_le {ι : Type*} [Fintype ι] (x y : ι → ℂ) (W : ℝ)
    (hx : ∑ r, ‖x r‖ ^ 2 ≤ W) (hy : ∑ r, ‖y r‖ ^ 2 ≤ W) : ∑ r, ‖x r‖ * ‖y r‖ ≤ W := by
  have h1 : ∀ r, ‖x r‖ * ‖y r‖ ≤ (‖x r‖ ^ 2 + ‖y r‖ ^ 2) / 2 := fun r => by
    nlinarith [sq_nonneg (‖x r‖ - ‖y r‖)]
  refine (Finset.sum_le_sum fun r _ => h1 r).trans ?_
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  linarith

/-- The bounds at a point of the good event. -/
structure QSI_Pt {D N : ℕ} (G B Q : Matrix (Idx D N) (Idx D N) ℂ) (Γ Wd lam : ℝ) : Prop where
  g : ∀ a b, ‖G a b‖ ≤ Γ
  gb : ∀ a b, ‖(G * B) a b‖ ≤ Γ
  row : ∀ a, ∑ m, ‖G a m‖ ^ 2 ≤ Wd
  col : ∀ b, ∑ m, ‖G m b‖ ^ 2 ≤ Wd
  rowB : ∀ a, ∑ m, ‖(G * B) a m‖ ^ 2 ≤ Wd
  q : ∀ a b, ‖Q a b‖ ≤ lam

section
variable {D N : ℕ} {G B Q : Matrix (Idx D N) (Idx D N) ℂ} {Γ Wd lam : ℝ}

private lemma QSI_Pt.cs (hP : QSI_Pt G B Q Γ Wd lam) (a b : Idx D N) :
    ∑ m, ‖G a m‖ * ‖G m b‖ ≤ Wd := QSI_sum_mul_le _ _ _ (hP.row a) (hP.col b)

private lemma QSI_Pt.csB (hP : QSI_Pt G B Q Γ Wd lam) (a b : Idx D N) :
    ∑ m, ‖(G * B) a m‖ * ‖G m b‖ ≤ Wd := QSI_sum_mul_le _ _ _ (hP.rowB a) (hP.col b)

private lemma QSI_Pt.cs2 (hP : QSI_Pt G B Q Γ Wd lam) (x y : Idx D N) :
    ∑ m, ‖G m x‖ * ‖G y m‖ ≤ Wd := QSI_sum_mul_le _ _ _ (hP.col x) (hP.row y)

private lemma QSI_Pt.cs3 (hP : QSI_Pt G B Q Γ Wd lam) (x y : Idx D N) :
    ∑ m, ‖G m x‖ * ‖(G * B) y m‖ ≤ Wd := QSI_sum_mul_le _ _ _ (hP.col x) (hP.rowB y)

private lemma QSI_Pt.Γ0 (hP : QSI_Pt G B Q Γ Wd lam) (a : Idx D N) : 0 ≤ Γ :=
  (norm_nonneg _).trans (hP.g a a)

private lemma QSI_Pt.W0 (hP : QSI_Pt G B Q Γ Wd lam) (a : Idx D N) : 0 ≤ Wd :=
  (Finset.sum_nonneg fun _ _ => by positivity).trans (hP.row a)

end

/-- A diagonal matrix in a product. -/
private lemma QSI_diag_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X S Y : Matrix ι ι ℂ) (s : ℝ)
    (hS : ∀ r, ‖S r r‖ ≤ s) (hS0 : ∀ r q, r ≠ q → S r q = 0) (k l : ι) :
    ‖(X * S * Y) k l‖ ≤ s * ∑ r, ‖X k r‖ * ‖Y r l‖ := by
  have e : ∀ r, (X * S) k r = X k r * S r r := by
    intro r
    rw [Matrix.mul_apply, Finset.sum_eq_single r]
    · intro q _ hq; rw [hS0 q r hq, mul_zero]
    · simp
  rw [Matrix.mul_apply]
  simp only [e]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [norm_mul, norm_mul]
  have := hS r
  have h0 : 0 ≤ ‖X k r‖ * ‖Y r l‖ := by positivity
  nlinarith [norm_nonneg (X k r), norm_nonneg (Y r l)]

private lemma QSI_sTheta_offdiag (D N : ℕ) (θ : ℝ) (Y : Matrix (Idx D N) (Idx D N) ℂ) (r q : Idx D N)
    (h : r ≠ q) : sTheta D N θ Y r q = 0 := by
  rw [QSI_sTheta_apply, if_neg h]

private lemma QSI_sTheta_diag_le (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Y : Matrix (Idx D N) (Idx D N) ℂ) (r : Idx D N) :
    ‖sTheta D N θ Y r r‖ ≤ (N : ℝ)⁻¹ * ∑ s, ‖Y s s‖ := by
  rw [QSI_sTheta_apply, if_pos rfl, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (QSI_kap_norm D N θ hθ0 hθ1 s r) (norm_nonneg _)

private lemma QSI_Ea_apply (D N : ℕ) (X Y : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D) (k l : Idx D N) :
    (X * Ea D N a * Y) k l = ∑ m, if m.1 = a then X k m * Y m l else 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Ea, Matrix.mul_diagonal]
  split_ifs <;> simp

private lemma QSI_Ea_sum_le (D N : ℕ) (X Y : Matrix (Idx D N) (Idx D N) ℂ) (k l : Idx D N) :
    ∑ a, ‖(X * Ea D N a * Y) k l‖ ≤ ∑ m, ‖X k m‖ * ‖Y m l‖ := by
  simp only [QSI_Ea_apply]
  calc ∑ a, ‖∑ m, if m.1 = a then X k m * Y m l else 0‖
      ≤ ∑ a, ∑ m, ‖if m.1 = a then X k m * Y m l else 0‖ :=
        Finset.sum_le_sum fun a _ => norm_sum_le _ _
    _ = ∑ m, ∑ a, ‖if m.1 = a then X k m * Y m l else 0‖ := Finset.sum_comm
    _ = ∑ m, ‖X k m‖ * ‖Y m l‖ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_eq_single m.1]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · simp

private lemma QSI_trEa (D N : ℕ) (M : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D) :
    (Ea D N a * M).trace = ∑ r, if r.1 = a then M r r else 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, Ea, Matrix.diagonal_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

private lemma QSI_cA_le (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (B Y : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D) (hN : 0 < N) (hD : 0 < D) :
    ‖QSI_cA D N θ B a Y‖ ≤ (N : ℝ)⁻¹ * ∑ r, ‖(Y * B) r r‖ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set X := ∑ r, ‖(Y * B) r r‖ with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have t1 : ‖(Ea D N a * Y * B).trace‖ ≤ X := by
    rw [Matrix.mul_assoc, QSI_trEa]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    split_ifs <;> simp
  have t2 : ‖(Y * B).trace‖ ≤ X := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact norm_sum_le _ _
  have hDN : ((D : ℝ) * N)⁻¹ ≤ (N : ℝ)⁻¹ := by
    rw [mul_inv]
    have : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD'
    nlinarith [inv_pos.2 hN']
  unfold QSI_cA
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have n1 : ‖(θ : ℂ)‖ = θ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ0]
  have n2 : ‖((1 - θ : ℝ) : ℂ)‖ = 1 - θ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have n3 : ‖((N : ℂ))⁻¹‖ = (N : ℝ)⁻¹ := by simp
  have n4 : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by simp
  rw [n1, n2, n3, n4]
  have h1 : θ * (N : ℝ)⁻¹ * ‖(Ea D N a * Y * B).trace‖ ≤ θ * (N : ℝ)⁻¹ * X :=
    mul_le_mul_of_nonneg_left t1 (by positivity)
  have h2 : (1 - θ) * ((D : ℝ) * N)⁻¹ * ‖(Y * B).trace‖ ≤ (1 - θ) * (N : ℝ)⁻¹ * X := by
    have : (1 - θ) * ((D : ℝ) * N)⁻¹ ≤ (1 - θ) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hDN (by linarith)
    exact mul_le_mul this t2 (norm_nonneg _) (by have := inv_pos.2 hN'; nlinarith)
  nlinarith

private lemma QSI_sum_smul_Ea_le (D N : ℕ) (c : Fin D → ℂ) (s : ℝ) (hc : ∀ a, ‖c a‖ ≤ s)
    (X Y : Matrix (Idx D N) (Idx D N) ℂ) (k l : Idx D N) :
    ‖(∑ a, c a • (X * Ea D N a * Y)) k l‖ ≤ s * ∑ m, ‖X k m‖ * ‖Y m l‖ := by
  rw [Matrix.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have hs : 0 ≤ s := (norm_nonneg _).trans (hc ⟨0, (Fin.pos (k.1))⟩)
  calc ∑ a, ‖(c a • (X * Ea D N a * Y)) k l‖ ≤ ∑ a, s * ‖(X * Ea D N a * Y) k l‖ := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right (hc a) (norm_nonneg _)
    _ = s * ∑ a, ‖(X * Ea D N a * Y) k l‖ := by rw [Finset.mul_sum]
    _ ≤ s * ∑ m, ‖X k m‖ * ‖Y m l‖ := mul_le_mul_of_nonneg_left (QSI_Ea_sum_le D N X Y k l) hs

section
variable {D N : ℕ} {G B Q : Matrix (Idx D N) (Idx D N) ℂ} {Γ Wd lam : ℝ} (θ : ℝ)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
include hθ0 hθ1

private lemma QSI_Pt.S_le (hP : QSI_Pt G B Q Γ Wd lam) (x y : Idx D N) (k l : Idx D N) :
    ‖(G * B * sTheta D N θ (G * Matrix.single x y (1 : ℂ) * G) * G) k l‖ ≤ (N : ℝ)⁻¹ * Wd * Wd := by
  have hS : ∀ r, ‖sTheta D N θ (G * Matrix.single x y (1 : ℂ) * G) r r‖ ≤ (N : ℝ)⁻¹ * Wd := by
    intro r
    refine (QSI_sTheta_diag_le D N θ hθ0 hθ1 _ r).trans ?_
    simp only [QSI_mul_single_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hP.cs2 x y) (by positivity)
  refine (QSI_diag_mul_le _ _ _ _ hS (QSI_sTheta_offdiag D N θ _) k l).trans ?_
  have := hP.csB k l
  have h0 : 0 ≤ (N : ℝ)⁻¹ * Wd := mul_nonneg (by positivity) (hP.W0 k)
  calc (N : ℝ)⁻¹ * Wd * ∑ r, ‖(G * B) k r‖ * ‖G r l‖ ≤ (N : ℝ)⁻¹ * Wd * Wd :=
        mul_le_mul_of_nonneg_left this h0

private lemma QSI_Pt.cA_le (hP : QSI_Pt G B Q Γ Wd lam) (x y : Idx D N) (a : Fin D) :
    ‖QSI_cA D N θ B a (G * Matrix.single x y (1 : ℂ) * G)‖ ≤ (N : ℝ)⁻¹ * Wd := by
  refine (QSI_cA_le D N θ hθ0 hθ1 B _ a x.2.pos x.1.pos).trans ?_
  have e : ∀ r, ((G * Matrix.single x y (1 : ℂ) * G) * B) r r = G r x * (G * B) y r := by
    intro r
    rw [Matrix.mul_assoc, QSI_mul_single_mul]
  simp only [e, norm_mul]
  exact mul_le_mul_of_nonneg_left (hP.cs3 x y) (by positivity)

/-- The bound on `Ψ_E`, `E = e_x e_y^*`, at a point of the good event. -/
private lemma QSI_Pt.Psi_le (hP : QSI_Pt G B Q Γ Wd lam) (x y k l : Idx D N) :
    ‖QSI_Psi D N θ B (Matrix.single x y (1 : ℂ)) G k l‖ ≤
      ‖(G * B) k x‖ * ‖G y l‖ + 2 * ((N : ℝ)⁻¹ * Wd * Wd) := by
  unfold QSI_Psi
  rw [Matrix.sub_apply, Matrix.sub_apply]
  have t1 : (G * B * Matrix.single x y (1 : ℂ) * G) k l = (G * B) k x * G y l := QSI_mul_single_mul _ _ _ _ _ _
  have t2 := hP.S_le θ hθ0 hθ1 x y k l
  have t3 := QSI_sum_smul_Ea_le D N _ _ (fun a => hP.cA_le θ hθ0 hθ1 x y a) G G k l
  have t3' : ‖(∑ a, QSI_cA D N θ B a (G * Matrix.single x y (1 : ℂ) * G) • (G * Ea D N a * G)) k l‖ ≤
      (N : ℝ)⁻¹ * Wd * Wd := t3.trans (mul_le_mul_of_nonneg_left (hP.cs k l)
        (mul_nonneg (by positivity) (hP.W0 k)))
  rw [t1]
  calc ‖(G * B) k x * G y l - (G * B * sTheta D N θ (G * Matrix.single x y (1 : ℂ) * G) * G) k l -
        (∑ a, QSI_cA D N θ B a (G * Matrix.single x y (1 : ℂ) * G) • (G * Ea D N a * G)) k l‖
      ≤ ‖(G * B) k x * G y l‖ + ‖(G * B * sTheta D N θ (G * Matrix.single x y (1 : ℂ) * G) * G) k l‖ +
        ‖(∑ a, QSI_cA D N θ B a (G * Matrix.single x y (1 : ℂ) * G) • (G * Ea D N a * G)) k l‖ :=
        norm_sub_le_of_le (norm_sub_le _ _) le_rfl
    _ ≤ _ := by rw [norm_mul]; linarith

end

private lemma QSI_dPsi_smul (D N : ℕ) (θ : ℝ) (B E R M : Matrix (Idx D N) (Idx D N) ℂ) (c : ℂ) :
    QSI_dPsi D N θ B E R (c • M) = c • QSI_dPsi D N θ B E R M := by
  unfold QSI_dPsi
  have e1 : c • M * E * R + R * E * c • M = c • (M * E * R + R * E * M) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add]
  have e2 : ∀ a, QSI_cA D N θ B a (c • (M * E * R) + c • (R * E * M)) =
      QSI_cA D N θ B a (M * E * R + R * E * M) * c := fun a => by
    rw [← smul_add, QSI_cA_smul, mul_comm]
  rw [e1, QSI_sTheta_smul]
  simp only [QSI_cA_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, Finset.smul_sum,
    smul_smul, mul_comm c, e2]

section
variable {D N : ℕ} {G B Q : Matrix (Idx D N) (Idx D N) ℂ} {Γ Wd lam : ℝ} (θ : ℝ)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
include hθ0 hθ1

/-- The bound on the derivative of `Ψ_E` in the direction `E' = e_{x'} e_{y'}^*`. -/
private lemma QSI_Pt.dPsi_le (hP : QSI_Pt G B Q Γ Wd lam) (x y x' y' k l : Idx D N) (c : ℂ)
    (hc : ‖c‖ ≤ 1) :
    ‖QSI_dPsi D N θ B (Matrix.single x y (1 : ℂ)) G
        (c • (G * Matrix.single x' y' (1 : ℂ) * G)) k l‖ ≤
      Γ * (‖G k x'‖ * ‖G y l‖ + ‖(G * B) k x‖ * ‖G y' l‖) + 8 * (Γ * ((N : ℝ)⁻¹ * Wd * Wd)) := by
  rw [QSI_dPsi_smul, Matrix.smul_apply, smul_eq_mul, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) hc).trans ?_
  set E := Matrix.single x y (1 : ℂ) with hE
  set E' := Matrix.single x' y' (1 : ℂ) with hE'
  set X := G * E' * G with hX
  have hΓ := hP.Γ0 k
  have hW := hP.W0 k
  have hNi : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hNW : 0 ≤ (N : ℝ)⁻¹ * Wd * Wd := by positivity
  -- the rank-one terms
  have t1 : ‖(X * B * E * G) k l‖ ≤ Γ * (‖G k x'‖ * ‖G y l‖) := by
    have e : X * B * E * G = G * (E' * ((G * B) * (E * G))) := by simp only [hX, Matrix.mul_assoc]
    rw [e, QSI_msm', QSI_msm', norm_mul, norm_mul]
    have := hP.gb y' x
    have h0 : 0 ≤ ‖G k x'‖ * ‖G y l‖ := by positivity
    nlinarith [norm_nonneg (G k x'), norm_nonneg (G y l), norm_nonneg ((G * B) y' x)]
  have t2 : ‖(G * B * E * X) k l‖ ≤ Γ * (‖(G * B) k x‖ * ‖G y' l‖) := by
    have e : G * B * E * X = (G * B) * (E * (G * (E' * G))) := by
      simp only [hX, Matrix.mul_assoc]
    rw [e, QSI_msm', QSI_msm', norm_mul, norm_mul]
    have := hP.g y x'
    have h0 : 0 ≤ ‖(G * B) k x‖ * ‖G y' l‖ := by positivity
    nlinarith [norm_nonneg (G y x'), norm_nonneg ((G * B) k x), norm_nonneg (G y' l)]
  -- the `S_θ` terms
  have hSl := hP.S_le θ hθ0 hθ1 x y
  have t3 : ‖(X * B * sTheta D N θ (G * E * G) * G) k l‖ ≤ Γ * ((N : ℝ)⁻¹ * Wd * Wd) := by
    have e : X * B * sTheta D N θ (G * E * G) * G =
        G * (E' * (G * B * sTheta D N θ (G * E * G) * G)) := by simp only [hX, Matrix.mul_assoc]
    rw [e, QSI_msm', norm_mul]
    exact mul_le_mul (hP.g k x') (hSl y' l) (norm_nonneg _) hΓ
  have t5 : ‖(G * B * sTheta D N θ (G * E * G) * X) k l‖ ≤ Γ * ((N : ℝ)⁻¹ * Wd * Wd) := by
    have e : G * B * sTheta D N θ (G * E * G) * X =
        (G * B * sTheta D N θ (G * E * G) * G) * (E' * G) := by simp only [hX, Matrix.mul_assoc]
    rw [e, QSI_msm', norm_mul, mul_comm Γ]
    exact mul_le_mul (hSl k x') (hP.g y' l) (norm_nonneg _) hNW
  have t4 : ‖(G * B * sTheta D N θ (X * E * G + G * E * X) * G) k l‖ ≤
      2 * (Γ * ((N : ℝ)⁻¹ * Wd * Wd)) := by
    have hd : ∀ r, ‖sTheta D N θ (X * E * G + G * E * X) r r‖ ≤ (N : ℝ)⁻¹ * (2 * (Γ * Wd)) := by
      intro r
      refine (QSI_sTheta_diag_le D N θ hθ0 hθ1 _ r).trans (mul_le_mul_of_nonneg_left ?_ hNi)
      have e1 : ∀ s, (X * E * G) s s = G s x' * (G y' x * G y s) := by
        intro s
        have : X * E * G = G * (E' * (G * (E * G))) := by simp only [hX, Matrix.mul_assoc]
        rw [this, QSI_msm', QSI_msm']
      have e2 : ∀ s, (G * E * X) s s = G s x * (G y x' * G y' s) := by
        intro s
        have : G * E * X = G * (E * (G * (E' * G))) := by simp only [hX, Matrix.mul_assoc]
        rw [this, QSI_msm', QSI_msm']
      have b1 : ∑ s, ‖(X * E * G) s s‖ ≤ Γ * Wd := by
        simp only [e1, norm_mul]
        calc ∑ s, ‖G s x'‖ * (‖G y' x‖ * ‖G y s‖) ≤ ∑ s, Γ * (‖G s x'‖ * ‖G y s‖) :=
              Finset.sum_le_sum fun s _ => by
                have := hP.g y' x
                nlinarith [norm_nonneg (G s x'), norm_nonneg (G y s), norm_nonneg (G y' x),
                  mul_nonneg (norm_nonneg (G s x')) (norm_nonneg (G y s))]
          _ = Γ * ∑ s, ‖G s x'‖ * ‖G y s‖ := by rw [Finset.mul_sum]
          _ ≤ Γ * Wd := mul_le_mul_of_nonneg_left (hP.cs2 x' y) hΓ
      have b2 : ∑ s, ‖(G * E * X) s s‖ ≤ Γ * Wd := by
        simp only [e2, norm_mul]
        calc ∑ s, ‖G s x‖ * (‖G y x'‖ * ‖G y' s‖) ≤ ∑ s, Γ * (‖G s x‖ * ‖G y' s‖) :=
              Finset.sum_le_sum fun s _ => by
                have := hP.g y x'
                nlinarith [norm_nonneg (G s x), norm_nonneg (G y' s), norm_nonneg (G y x'),
                  mul_nonneg (norm_nonneg (G s x)) (norm_nonneg (G y' s))]
          _ = Γ * ∑ s, ‖G s x‖ * ‖G y' s‖ := by rw [Finset.mul_sum]
          _ ≤ Γ * Wd := mul_le_mul_of_nonneg_left (hP.cs2 x y') hΓ
      calc ∑ s, ‖(X * E * G + G * E * X) s s‖ ≤ ∑ s, (‖(X * E * G) s s‖ + ‖(G * E * X) s s‖) :=
            Finset.sum_le_sum fun s _ => by rw [Matrix.add_apply]; exact norm_add_le _ _
        _ ≤ 2 * (Γ * Wd) := by rw [Finset.sum_add_distrib]; linarith
    refine (QSI_diag_mul_le _ _ _ _ hd (QSI_sTheta_offdiag D N θ _) k l).trans ?_
    have := hP.csB k l
    calc (N : ℝ)⁻¹ * (2 * (Γ * Wd)) * ∑ r, ‖(G * B) k r‖ * ‖G r l‖ ≤
          (N : ℝ)⁻¹ * (2 * (Γ * Wd)) * Wd :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * (Γ * ((N : ℝ)⁻¹ * Wd * Wd)) := by ring
  -- the coefficient terms
  have t6 : ‖(∑ a, QSI_cA D N θ B a (X * E * G + G * E * X) • (G * Ea D N a * G)) k l‖ ≤
      2 * (Γ * ((N : ℝ)⁻¹ * Wd * Wd)) := by
    have hc6 : ∀ a, ‖QSI_cA D N θ B a (X * E * G + G * E * X)‖ ≤ (N : ℝ)⁻¹ * (2 * (Γ * Wd)) := by
      intro a
      refine (QSI_cA_le D N θ hθ0 hθ1 B _ a x.2.pos x.1.pos).trans
        (mul_le_mul_of_nonneg_left ?_ hNi)
      have e1 : ∀ r, ((X * E * G) * B) r r = G r x' * (G y' x * (G * B) y r) := by
        intro r
        have : X * E * G * B = G * (E' * (G * (E * (G * B)))) := by
          simp only [hX, Matrix.mul_assoc]
        rw [this, QSI_msm', QSI_msm']
      have e2 : ∀ r, ((G * E * X) * B) r r = G r x * (G y x' * (G * B) y' r) := by
        intro r
        have : G * E * X * B = G * (E * (G * (E' * (G * B)))) := by
          simp only [hX, Matrix.mul_assoc]
        rw [this, QSI_msm', QSI_msm']
      have b1 : ∑ r, ‖((X * E * G) * B) r r‖ ≤ Γ * Wd := by
        simp only [e1, norm_mul]
        calc ∑ r, ‖G r x'‖ * (‖G y' x‖ * ‖(G * B) y r‖) ≤ ∑ r, Γ * (‖G r x'‖ * ‖(G * B) y r‖) :=
              Finset.sum_le_sum fun r _ => by
                have := hP.g y' x
                nlinarith [norm_nonneg (G r x'), norm_nonneg ((G * B) y r), norm_nonneg (G y' x),
                  mul_nonneg (norm_nonneg (G r x')) (norm_nonneg ((G * B) y r))]
          _ = Γ * ∑ r, ‖G r x'‖ * ‖(G * B) y r‖ := by rw [Finset.mul_sum]
          _ ≤ Γ * Wd := mul_le_mul_of_nonneg_left (hP.cs3 x' y) hΓ
      have b2 : ∑ r, ‖((G * E * X) * B) r r‖ ≤ Γ * Wd := by
        simp only [e2, norm_mul]
        calc ∑ r, ‖G r x‖ * (‖G y x'‖ * ‖(G * B) y' r‖) ≤ ∑ r, Γ * (‖G r x‖ * ‖(G * B) y' r‖) :=
              Finset.sum_le_sum fun r _ => by
                have := hP.g y x'
                nlinarith [norm_nonneg (G r x), norm_nonneg ((G * B) y' r), norm_nonneg (G y x'),
                  mul_nonneg (norm_nonneg (G r x)) (norm_nonneg ((G * B) y' r))]
          _ = Γ * ∑ r, ‖G r x‖ * ‖(G * B) y' r‖ := by rw [Finset.mul_sum]
          _ ≤ Γ * Wd := mul_le_mul_of_nonneg_left (hP.cs3 x y') hΓ
      calc ∑ r, ‖((X * E * G + G * E * X) * B) r r‖ ≤
            ∑ r, (‖((X * E * G) * B) r r‖ + ‖((G * E * X) * B) r r‖) :=
            Finset.sum_le_sum fun r _ => by rw [Matrix.add_mul, Matrix.add_apply]; exact norm_add_le _ _
        _ ≤ 2 * (Γ * Wd) := by rw [Finset.sum_add_distrib]; linarith
    refine (QSI_sum_smul_Ea_le D N _ _ hc6 G G k l).trans ?_
    calc (N : ℝ)⁻¹ * (2 * (Γ * Wd)) * ∑ m, ‖G k m‖ * ‖G m l‖ ≤ (N : ℝ)⁻¹ * (2 * (Γ * Wd)) * Wd :=
          mul_le_mul_of_nonneg_left (hP.cs k l) (by positivity)
      _ = 2 * (Γ * ((N : ℝ)⁻¹ * Wd * Wd)) := by ring
  have t7 : ‖(∑ a, QSI_cA D N θ B a (G * E * G) • (X * Ea D N a * G)) k l +
      (∑ a, QSI_cA D N θ B a (G * E * G) • (G * Ea D N a * X)) k l‖ ≤
      2 * (Γ * ((N : ℝ)⁻¹ * Wd * Wd)) := by
    have hc7 := fun a => hP.cA_le θ hθ0 hθ1 x y a
    refine (norm_add_le _ _).trans ?_
    have u1 := QSI_sum_smul_Ea_le D N _ _ hc7 X G k l
    have u2 := QSI_sum_smul_Ea_le D N _ _ hc7 G X k l
    have eX : ∀ m, X k m = G k x' * G y' m := fun m => QSI_mul_single_mul _ _ _ _ _ _
    have eX2 : ∀ m, X m l = G m x' * G y' l := fun m => QSI_mul_single_mul _ _ _ _ _ _
    have v1 : ∑ m, ‖X k m‖ * ‖G m l‖ ≤ Γ * Wd := by
      simp only [eX, norm_mul]
      calc ∑ m, ‖G k x'‖ * ‖G y' m‖ * ‖G m l‖ = ‖G k x'‖ * ∑ m, ‖G y' m‖ * ‖G m l‖ := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
        _ ≤ Γ * Wd := mul_le_mul (hP.g k x') (hP.cs y' l)
            (Finset.sum_nonneg fun _ _ => by positivity) hΓ
    have v2 : ∑ m, ‖G k m‖ * ‖X m l‖ ≤ Γ * Wd := by
      simp only [eX2, norm_mul]
      calc ∑ m, ‖G k m‖ * (‖G m x'‖ * ‖G y' l‖) = ‖G y' l‖ * ∑ m, ‖G k m‖ * ‖G m x'‖ := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
        _ ≤ Γ * Wd := mul_le_mul (hP.g y' l) (hP.cs k x')
            (Finset.sum_nonneg fun _ _ => by positivity) hΓ
    have w1 := u1.trans (mul_le_mul_of_nonneg_left v1 (by positivity))
    have w2 := u2.trans (mul_le_mul_of_nonneg_left v2 (by positivity))
    nlinarith
  -- assemble
  unfold QSI_dPsi
  simp only [Matrix.sub_apply, Matrix.add_apply, Finset.sum_add_distrib, smul_add]
  set a1 := (X * B * E * G) k l
  set a2 := (G * B * E * X) k l
  set a3 := (X * B * sTheta D N θ (G * E * G) * G) k l
  set a4 := (G * B * sTheta D N θ (X * E * G + G * E * X) * G) k l
  set a5 := (G * B * sTheta D N θ (G * E * G) * X) k l
  set a6 := (∑ a, QSI_cA D N θ B a (X * E * G + G * E * X) • (G * Ea D N a * G)) k l
  set a7 := (∑ a, QSI_cA D N θ B a (G * E * G) • (X * Ea D N a * G)) k l
  set a8 := (∑ a, QSI_cA D N θ B a (G * E * G) • (G * Ea D N a * X)) k l
  have n1 : ‖a1 + a2 - (a3 + a4 + a5) - (a6 + (a7 + a8))‖ ≤
      ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖a4‖ + ‖a5‖ + ‖a6‖ + ‖a7 + a8‖ := by
    have q1 := norm_sub_le (a1 + a2 - (a3 + a4 + a5)) (a6 + (a7 + a8))
    have q2 := norm_sub_le (a1 + a2) (a3 + a4 + a5)
    have q3 := norm_add_le a1 a2
    have q4 := norm_add_le (a3 + a4) a5
    have q5 := norm_add_le a3 a4
    have q6 := norm_add_le a6 (a7 + a8)
    linarith
  refine n1.trans ?_
  nlinarith

end


/-! ### part e -/

private lemma QSI_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
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

open scoped Matrix.Norms.L2Operator in
private lemma QSI_mulVec_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
    (u : ι → ℂ) : ∑ k, ‖(T *ᵥ u) k‖ ^ 2 ≤ opNorm T ^ 2 * ∑ k, ‖u k‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec T (WithLp.toLp 2 u)
  have h1 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖ ^ 2 = ∑ k, ‖u k‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  have h2 : ‖(EuclideanSpace.equiv ι ℂ).symm (T *ᵥ (WithLp.toLp 2 u).ofLp)‖ ^ 2 =
      ∑ k, ‖(T *ᵥ u) k‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h3 : ‖(EuclideanSpace.equiv ι ℂ).symm (T *ᵥ (WithLp.toLp 2 u).ofLp)‖ ^ 2 ≤
      (‖T‖ * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [h2, mul_pow, h1] at h3
  exact h3

open scoped Matrix.Norms.L2Operator in
private lemma QSI_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) : opNorm Tᴴ = opNorm T := by
  change ‖Tᴴ‖ = ‖T‖
  exact Matrix.l2_opNorm_conjTranspose T

/-- The point bounds from the good event `avgGood` at a Hermitian array. -/
private lemma QSI_Pt_of_good {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (hB : opNorm B ≤ 1) (z : ℂ) (hz : 0 < z.im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (Γ Υ lam : ℝ)
    (hg : h ∈ avgGood D N θ Λ B z Γ Υ lam) :
    QSI_Pt (res (Matrix.of h + Λ) z) B (qMat D N θ (Matrix.of h) Λ B z) Γ (Υ / z.im) lam := by
  obtain ⟨hgs, hq⟩ := hg
  set G := res (Matrix.of h + Λ) z with hG
  have he : ∀ p : Idx D N, (Pi.single p 1 : Idx D N → ℂ) ∈ avgVecs D N Λ B := fun p => by
    unfold avgVecs; simp
  have hBe : ∀ p : Idx D N, (B *ᵥ Pi.single p 1 : Idx D N → ℂ) ∈ avgVecs D N Λ B := fun p => by
    unfold avgVecs; simp
  have hIm : ∀ p, (G p p).im ≤ Υ := fun p => by
    have := (hgs _ (he p) _ (he p)).2
    have e : star (Pi.single p (1 : ℂ)) ⬝ᵥ (G *ᵥ Pi.single p 1) = G p p := QSI_f_ee Λ z h p p
    rwa [e] at this
  have hX : (Matrix.of h + Λ).IsHermitian := hh.add hΛ
  have hw := fun p => ward_diag (Matrix.of h + Λ) hX z hz p
  have hrow : ∀ p, ∑ m, ‖G p m‖ ^ 2 ≤ Υ / z.im := fun p => by
    rw [(hw p).2]
    exact div_le_div_of_nonneg_right (hIm p) hz.le
  have hcol : ∀ q, ∑ m, ‖G m q‖ ^ 2 ≤ Υ / z.im := fun q => by
    rw [(hw q).1]
    exact div_le_div_of_nonneg_right (hIm q) hz.le
  refine ⟨fun a b => ?_, fun a b => ?_, hrow, hcol, fun p => ?_, hq⟩
  · have := (hgs _ (he a) _ (he b)).1
    have e : star (Pi.single a (1 : ℂ)) ⬝ᵥ (G *ᵥ Pi.single b 1) = G a b := QSI_f_ee Λ z h a b
    rwa [e] at this
  · have := (hgs _ (he a) _ (hBe b)).1
    have e : star (Pi.single a (1 : ℂ)) ⬝ᵥ (G *ᵥ (B *ᵥ Pi.single b 1)) = (G * B) a b :=
      QSI_f_eM Λ B z h a b
    rwa [e] at this
  · have key := QSI_mulVec_sq Bᴴ (fun s => starRingEnd ℂ (G p s))
    have e : ∀ m, ‖(Bᴴ *ᵥ fun s => starRingEnd ℂ (G p s)) m‖ = ‖(G * B) p m‖ := by
      intro m
      rw [← Complex.norm_conj, Matrix.mulVec, dotProduct, map_sum, Matrix.mul_apply]
      refine congrArg _ (Finset.sum_congr rfl fun s _ => ?_)
      simp [Matrix.conjTranspose_apply, mul_comm]
    simp only [e, Complex.norm_conj, QSI_opNorm_conjTranspose] at key
    refine key.trans ?_
    have h0 : 0 ≤ ∑ k, ‖G p k‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hB0 : 0 ≤ opNorm B := norm_nonneg _
    calc opNorm B ^ 2 * ∑ k, ‖G p k‖ ^ 2 ≤ 1 * (Υ / z.im) :=
          mul_le_mul (by nlinarith) (hrow p) h0 zero_le_one
      _ = Υ / z.im := one_mul _

/-- The Ward weights of row `k` and column `l`. -/
private def QSI_wa {D N : ℕ} (G B : Matrix (Idx D N) (Idx D N) ℂ) (k s : Idx D N) : ℝ :=
  ‖G k s‖ + ‖(G * B) k s‖

private lemma QSI_wa_nonneg {D N : ℕ} (G B : Matrix (Idx D N) (Idx D N) ℂ) (k s : Idx D N) :
    0 ≤ QSI_wa G B k s := by unfold QSI_wa; positivity

section
variable {D N : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (h : Idx D N → Idx D N → ℂ)
  (hh : (Matrix.of h).IsHermitian) (p q : Idx D N) (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
  (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) {Γ Wd lam : ℝ}
  (hP : QSI_Pt (res (Matrix.of h + Λ) z) B (qMat D N θ (Matrix.of h) Λ B z) Γ Wd lam)
include hθ0 hθ1 hh hΛ hz hP

private lemma QSI_G_self : QSI_G h p q Λ z (h p q) = res (Matrix.of h + Λ) z := by
  unfold QSI_G; rw [QSI_setEntry_self h hh p q]

/-- The first derivatives of `Q_{kl}` at the point, through `eq:der_Q`. -/
private lemma QSI_rho1_core {T : (ℂ → ℂ) → (ℂ → ℂ)} (x y : Idx D N) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (hxy : (x = p ∧ y = q) ∨ (x = q ∧ y = p))
    (hQ : QSI_mD T (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z) = (fun w =>
        (-c) • (QSI_G h p q Λ z w * Matrix.single x y 1 *
            qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z +
          qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z * Matrix.single x y 1 *
            QSI_G h p q Λ z w) +
          c • (((D : ℂ) * N)⁻¹ • QSI_Psi D N θ B (Matrix.single x y 1) (QSI_G h p q Λ z w))))
    (k l : Idx D N) :
    ‖T (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z k l) (h p q)‖ ≤
      lam * (QSI_wa (res (Matrix.of h + Λ) z) B k p + QSI_wa (res (Matrix.of h + Λ) z) B k q +
        ‖res (Matrix.of h + Λ) z p l‖ + ‖res (Matrix.of h + Λ) z q l‖) +
      ((D : ℝ) * N)⁻¹ * (QSI_wa (res (Matrix.of h + Λ) z) B k p * ‖res (Matrix.of h + Λ) z q l‖ +
        QSI_wa (res (Matrix.of h + Λ) z) B k q * ‖res (Matrix.of h + Λ) z p l‖ +
        2 * ((N : ℝ)⁻¹ * Wd * Wd)) := by
  set G := res (Matrix.of h + Λ) z with hG
  set Q0 := qMat D N θ (Matrix.of h) Λ B z with hQ0
  have e1 : T (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z k l) (h p q) =
      QSI_mD T (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z) (h p q) k l := rfl
  rw [e1, hQ]
  simp only [QSI_G_self θ hθ0 hθ1 h hh p q Λ B hΛ z hz hP, QSI_setEntry_self h hh p q]
  rw [← hG, ← hQ0]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, QSI_mul_single_mul]
  have hΓ := hP.Γ0 k
  have hW := hP.W0 k
  have hDN : (0 : ℝ) ≤ ((D : ℝ) * N)⁻¹ := by positivity
  have hPsi := hP.Psi_le θ hθ0 hθ1 x y k l
  have nDN : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by simp
  have ax : ‖G k x‖ ≤ QSI_wa G B k p + QSI_wa G B k q := by
    unfold QSI_wa; rcases hxy with ⟨hx, -⟩ | ⟨hx, -⟩ <;> rw [hx] <;> nlinarith [norm_nonneg (G k p), norm_nonneg (G k q),
      norm_nonneg ((G * B) k p), norm_nonneg ((G * B) k q)]
  have by' : ‖G y l‖ ≤ ‖G p l‖ + ‖G q l‖ := by
    rcases hxy with ⟨-, hy⟩ | ⟨-, hy⟩ <;> rw [hy] <;> nlinarith [norm_nonneg (G p l), norm_nonneg (G q l)]
  have abxy : ‖(G * B) k x‖ * ‖G y l‖ ≤ QSI_wa G B k p * ‖G q l‖ + QSI_wa G B k q * ‖G p l‖ := by
    have h1 : ‖(G * B) k x‖ ≤ QSI_wa G B k x := by unfold QSI_wa; linarith [norm_nonneg (G k x)]
    have h2 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (G y l))
    have w1 := QSI_wa_nonneg G B k p
    have w2 := QSI_wa_nonneg G B k q
    have n1 := norm_nonneg (G p l)
    have n2 := norm_nonneg (G q l)
    rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy] at h2 ⊢ <;>
      nlinarith [mul_nonneg w1 n1, mul_nonneg w1 n2, mul_nonneg w2 n1, mul_nonneg w2 n2]
  have hl0 : 0 ≤ lam := (norm_nonneg _).trans (hP.q k l)
  have A1 : ‖G k x * Q0 y l + Q0 k x * G y l‖ ≤
      lam * (QSI_wa G B k p + QSI_wa G B k q + ‖G p l‖ + ‖G q l‖) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have q1 := hP.q y l
    have q2 := hP.q k x
    have u1 : ‖G k x‖ * ‖Q0 y l‖ ≤ (QSI_wa G B k p + QSI_wa G B k q) * lam :=
      mul_le_mul ax q1 (norm_nonneg _) (by linarith [QSI_wa_nonneg G B k p, QSI_wa_nonneg G B k q])
    have u2 : ‖Q0 k x‖ * ‖G y l‖ ≤ lam * (‖G p l‖ + ‖G q l‖) :=
      mul_le_mul q2 by' (norm_nonneg _) hl0
    nlinarith
  have A2 : ‖QSI_Psi D N θ B (Matrix.single x y 1) G k l‖ ≤
      QSI_wa G B k p * ‖G q l‖ + QSI_wa G B k q * ‖G p l‖ + 2 * ((N : ℝ)⁻¹ * Wd * Wd) := by
    linarith
  calc ‖-c * (G k x * Q0 y l + Q0 k x * G y l) +
        c * (((D : ℂ) * N)⁻¹ * QSI_Psi D N θ B (Matrix.single x y 1) G k l)‖
      ≤ ‖c‖ * ‖G k x * Q0 y l + Q0 k x * G y l‖ +
          ‖c‖ * (((D : ℝ) * N)⁻¹ * ‖QSI_Psi D N θ B (Matrix.single x y 1) G k l‖) := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_neg, norm_mul, norm_mul, nDN]
    _ ≤ 1 * ‖G k x * Q0 y l + Q0 k x * G y l‖ +
          1 * (((D : ℝ) * N)⁻¹ * ‖QSI_Psi D N θ B (Matrix.single x y 1) G k l‖) := by
        gcongr
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left A2 hDN
        nlinarith

/-- The second derivatives of `Q_{kl}` at the point. -/
private lemma QSI_rho2_core {T T' : (ℂ → ℂ) → (ℂ → ℂ)} (hT' : QSI_Der T') (x y x' y' : Idx D N) (c : ℂ)
    (hc : ‖c‖ ≤ 1) (hx : x = p ∨ x = q) (hy : y = p ∨ y = q) (hx' : x' = p ∨ x' = q)
    (hy' : y' = p ∨ y' = q)
    (hQ : QSI_mD T (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z) = (fun w =>
        (-c) • (QSI_G h p q Λ z w * Matrix.single x y 1 *
            qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z +
          qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z * Matrix.single x y 1 *
            QSI_G h p q Λ z w) +
          c • (((D : ℂ) * N)⁻¹ • QSI_Psi D N θ B (Matrix.single x y 1) (QSI_G h p q Λ z w))))
    (hG' : QSI_mD T' (QSI_G h p q Λ z) = fun w =>
      (-c) • (QSI_G h p q Λ z w * Matrix.single x' y' 1 * QSI_G h p q Λ z w))
    (g1 : ℝ)
    (hQ' : ∀ a b, ‖QSI_mD T' (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z)
      (h p q) a b‖ ≤ g1)
    (k l : Idx D N) :
    ‖T' (fun w => T (fun w' => qMat D N θ (Matrix.of (setEntry h p q w')) Λ B z k l) w) (h p q)‖ ≤
      (Γ * lam + g1) * (QSI_wa (res (Matrix.of h + Λ) z) B k p +
        QSI_wa (res (Matrix.of h + Λ) z) B k q +
        ‖res (Matrix.of h + Λ) z p l‖ + ‖res (Matrix.of h + Λ) z q l‖) +
      ((D : ℝ) * N)⁻¹ * (2 * Γ * ((QSI_wa (res (Matrix.of h + Λ) z) B k p +
        QSI_wa (res (Matrix.of h + Λ) z) B k q) *
        (‖res (Matrix.of h + Λ) z p l‖ + ‖res (Matrix.of h + Λ) z q l‖)) +
        8 * (Γ * ((N : ℝ)⁻¹ * Wd * Wd))) := by
  set G := res (Matrix.of h + Λ) z with hG
  set Q0 := qMat D N θ (Matrix.of h) Λ B z with hQ0
  set Q' := QSI_mD T' (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z) (h p q)
    with hQ'def
  have e1 : T' (fun w => T (fun w' => qMat D N θ (Matrix.of (setEntry h p q w')) Λ B z k l) w)
      (h p q) = QSI_mD T' (QSI_mD T (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z))
        (h p q) k l := rfl
  rw [e1, QSI_mD2_Q θ h hh p q Λ B hΛ z hz hT' _ c hQ, hG']
  simp only [QSI_G_self θ hθ0 hθ1 h hh p q Λ B hΛ z hz hP, QSI_setEntry_self h hh p q]
  rw [← hG, ← hQ0, ← hQ'def]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, QSI_mul_single_mul]
  have hΓ := hP.Γ0 k
  have hW := hP.W0 k
  have hDN : (0 : ℝ) ≤ ((D : ℝ) * N)⁻¹ := by positivity
  have nDN : ‖((D : ℂ) * N)⁻¹‖ = ((D : ℝ) * N)⁻¹ := by simp
  have hl0 : 0 ≤ lam := (norm_nonneg _).trans (hP.q k l)
  have hg0 : 0 ≤ g1 := (norm_nonneg _).trans (hQ' k l)
  set wa := QSI_wa G B k p + QSI_wa G B k q with hwa
  set bb := ‖G p l‖ + ‖G q l‖ with hbb
  have wa0 : 0 ≤ wa := add_nonneg (QSI_wa_nonneg G B k p) (QSI_wa_nonneg G B k q)
  have bb0 : 0 ≤ bb := by positivity
  have aG : ∀ s, s = p ∨ s = q → ‖G k s‖ ≤ wa := fun s hs => by
    rw [hwa]; unfold QSI_wa
    rcases hs with hs | hs <;> rw [hs] <;> nlinarith [norm_nonneg (G k p), norm_nonneg (G k q),
      norm_nonneg ((G * B) k p), norm_nonneg ((G * B) k q)]
  have aGB : ∀ s, s = p ∨ s = q → ‖(G * B) k s‖ ≤ wa := fun s hs => by
    rw [hwa]; unfold QSI_wa
    rcases hs with hs | hs <;> rw [hs] <;> nlinarith [norm_nonneg (G k p), norm_nonneg (G k q),
      norm_nonneg ((G * B) k p), norm_nonneg ((G * B) k q)]
  have bG : ∀ s, s = p ∨ s = q → ‖G s l‖ ≤ bb := fun s hs => by
    rw [hbb]
    rcases hs with hs | hs <;> rw [hs] <;> nlinarith [norm_nonneg (G p l), norm_nonneg (G q l)]
  have hdP := hP.dPsi_le θ hθ0 hθ1 x y x' y' k l (-c) (by rwa [norm_neg])
  have hd2 : ‖G k x'‖ * ‖G y l‖ + ‖(G * B) k x‖ * ‖G y' l‖ ≤ 2 * (wa * bb) := by
    have u1 := mul_le_mul (aG x' hx') (bG y hy) (norm_nonneg _) wa0
    have u2 := mul_le_mul (aGB x hx) (bG y' hy') (norm_nonneg _) wa0
    linarith
  have A1 : ‖-c * (G k x' * G y' x) * Q0 y l + G k x * Q' y l + Q' k x * G y l +
      Q0 k x * (-c * (G y x' * G y' l))‖ ≤ (Γ * lam + g1) * (wa + bb) := by
    have m1 : ‖-c * (G k x' * G y' x) * Q0 y l‖ ≤ Γ * lam * wa := by
      rw [norm_mul, norm_mul, norm_neg, norm_mul]
      have := mul_le_mul (mul_le_mul (aG x' hx') (hP.g y' x) (norm_nonneg _) wa0) (hP.q y l)
        (norm_nonneg _) (by positivity)
      have hc' : ‖c‖ * (‖G k x'‖ * ‖G y' x‖) * ‖Q0 y l‖ ≤ ‖G k x'‖ * ‖G y' x‖ * ‖Q0 y l‖ := by
        have : 0 ≤ ‖G k x'‖ * ‖G y' x‖ * ‖Q0 y l‖ := by positivity
        nlinarith [norm_nonneg c]
      nlinarith
    have m2 : ‖G k x * Q' y l‖ ≤ g1 * wa := by
      rw [norm_mul, mul_comm g1]
      exact mul_le_mul (aG x hx) (hQ' y l) (norm_nonneg _) wa0
    have m3 : ‖Q' k x * G y l‖ ≤ g1 * bb := by
      rw [norm_mul]
      exact mul_le_mul (hQ' k x) (bG y hy) (norm_nonneg _) hg0
    have m4 : ‖Q0 k x * (-c * (G y x' * G y' l))‖ ≤ Γ * lam * bb := by
      rw [norm_mul, norm_mul, norm_neg, norm_mul]
      have := mul_le_mul (hP.q k x) (mul_le_mul (hP.g y x') (bG y' hy') (norm_nonneg _) hΓ)
        (by positivity) hl0
      have hc' : ‖Q0 k x‖ * (‖c‖ * (‖G y x'‖ * ‖G y' l‖)) ≤ ‖Q0 k x‖ * (‖G y x'‖ * ‖G y' l‖) := by
        have : 0 ≤ ‖Q0 k x‖ * (‖G y x'‖ * ‖G y' l‖) := by positivity
        nlinarith [norm_nonneg c, norm_nonneg (Q0 k x)]
      nlinarith
    have t : ‖-c * (G k x' * G y' x) * Q0 y l + G k x * Q' y l + Q' k x * G y l +
        Q0 k x * (-c * (G y x' * G y' l))‖ ≤ ‖-c * (G k x' * G y' x) * Q0 y l‖ +
          ‖G k x * Q' y l‖ + ‖Q' k x * G y l‖ + ‖Q0 k x * (-c * (G y x' * G y' l))‖ :=
      norm_add₄_le
    nlinarith
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_neg, norm_mul, nDN]
  have hc0 := norm_nonneg c
  set A := ‖-c * (G k x' * G y' x) * Q0 y l + G k x * Q' y l + Q' k x * G y l +
      Q0 k x * (-c * (G y x' * G y' l))‖
  set P := ‖QSI_dPsi D N θ B (Matrix.single x y 1) G (-c • (G * Matrix.single x' y' 1 * G)) k l‖
  have hA0 : 0 ≤ A := norm_nonneg _
  have hP0 : 0 ≤ P := norm_nonneg _
  have e1 : ‖c‖ * A ≤ A := by nlinarith
  have e2 : ‖c‖ * (((D : ℝ) * N)⁻¹ * P) ≤ ((D : ℝ) * N)⁻¹ * P := by
    have : 0 ≤ ((D : ℝ) * N)⁻¹ * P := by positivity
    nlinarith
  have e3 : ((D : ℝ) * N)⁻¹ * P ≤ ((D : ℝ) * N)⁻¹ * (2 * Γ * (wa * bb) +
      8 * (Γ * ((N : ℝ)⁻¹ * Wd * Wd))) := by
    apply mul_le_mul_of_nonneg_left _ hDN
    have := mul_le_mul_of_nonneg_left hd2 hΓ
    nlinarith
  linarith

/-- `ρ₁`: the first derivatives of `Q_{kl}` along the slice in the entry `(p, q)`. -/
private lemma QSI_rho1 (a b : ℕ) (hab : a + b = 1) (k l : Idx D N) :
    ‖wirt a b (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z k l) (h p q)‖ ≤
      lam * (QSI_wa (res (Matrix.of h + Λ) z) B k p + QSI_wa (res (Matrix.of h + Λ) z) B k q +
        ‖res (Matrix.of h + Λ) z p l‖ + ‖res (Matrix.of h + Λ) z q l‖) +
      ((D : ℝ) * N)⁻¹ * (QSI_wa (res (Matrix.of h + Λ) z) B k p * ‖res (Matrix.of h + Λ) z q l‖ +
        QSI_wa (res (Matrix.of h + Λ) z) B k q * ‖res (Matrix.of h + Λ) z p l‖ +
        2 * ((N : ℝ)⁻¹ * Wd * Wd)) := by
  obtain ⟨hQ1, hQ2⟩ := QSI_mD_Q θ h hh p q Λ B hΛ z hz
  have h1 : (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by omega
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact QSI_rho1_core θ hθ0 hθ1 h hh p q Λ B hΛ z hz hP p q _ (by split_ifs <;> norm_num)
      (Or.inl ⟨rfl, rfl⟩) hQ1 k l
  · exact QSI_rho1_core θ hθ0 hθ1 h hh p q Λ B hΛ z hz hP q p _ (by split_ifs <;> norm_num)
      (Or.inr ⟨rfl, rfl⟩) hQ2 k l

/-- `ρ₂`: the second derivatives of `Q_{kl}` along the slice in the entry `(p, q)`. -/
private lemma QSI_rho2 (g1 : ℝ)
    (hg1 : ∀ a b, a + b = 1 → ∀ y l', ‖wirt a b
      (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z y l') (h p q)‖ ≤ g1)
    (a b : ℕ) (hab : a + b = 2) (k l : Idx D N) :
    ‖wirt a b (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z k l) (h p q)‖ ≤
      (Γ * lam + g1) * (QSI_wa (res (Matrix.of h + Λ) z) B k p +
        QSI_wa (res (Matrix.of h + Λ) z) B k q +
        ‖res (Matrix.of h + Λ) z p l‖ + ‖res (Matrix.of h + Λ) z q l‖) +
      ((D : ℝ) * N)⁻¹ * (2 * Γ * ((QSI_wa (res (Matrix.of h + Λ) z) B k p +
        QSI_wa (res (Matrix.of h + Λ) z) B k q) *
        (‖res (Matrix.of h + Λ) z p l‖ + ‖res (Matrix.of h + Λ) z q l‖)) +
        8 * (Γ * ((N : ℝ)⁻¹ * Wd * Wd))) := by
  obtain ⟨hQ1, hQ2⟩ := QSI_mD_Q θ h hh p q Λ B hΛ z hz
  obtain ⟨hG1, hG2⟩ := QSI_mD_G h hh p q Λ hΛ z hz
  have hw1 : ∀ a' b', ‖QSI_mD dW (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z)
      (h p q) a' b'‖ ≤ g1 := fun a' b' => hg1 1 0 rfl a' b'
  have hw2 : ∀ a' b', ‖QSI_mD dWbar (fun w => qMat D N θ (Matrix.of (setEntry h p q w)) Λ B z)
      (h p q) a' b'‖ ≤ g1 := fun a' b' => hg1 0 1 rfl a' b'
  have h1 : (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 1) ∨ (a = 0 ∧ b = 2) := by omega
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact QSI_rho2_core θ hθ0 hθ1 h hh p q Λ B hΛ z hz hP QSI_Der_dW p q p q _ (by split_ifs <;> norm_num)
      (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) hQ1 hG1 g1 hw1 k l
  · exact QSI_rho2_core θ hθ0 hθ1 h hh p q Λ B hΛ z hz hP QSI_Der_dW q p p q _ (by split_ifs <;> norm_num)
      (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) hQ2 hG1 g1 hw1 k l
  · exact QSI_rho2_core θ hθ0 hθ1 h hh p q Λ B hΛ z hz hP QSI_Der_dWbar q p q p _ (by split_ifs <;> norm_num)
      (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) hQ2 hG2 g1 hw2 k l

end


/-! ### part f -/

private lemma QSI_iter_cmul {T : (ℂ → ℂ) → (ℂ → ℂ)} (hT : QSI_Der T) (c : ℂ) {f : ℂ → ℂ}
    (hf : QSI_Sm f) (n : ℕ) : T^[n] (fun x => c * f x) = fun x => c * T^[n] f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hT.cmul _ _ (hT.iter_sm hf n),
      Function.iterate_succ_apply']

private lemma QSI_wirt_cmul (c : ℂ) {f : ℂ → ℂ} (hf : QSI_Sm f) (a b : ℕ) :
    wirt a b (fun x => c * f x) = fun x => c * wirt a b f x := by
  unfold wirt
  rw [QSI_iter_cmul QSI_Der_dWbar c hf b, QSI_iter_cmul QSI_Der_dW c (hf.itwb b) a]

private lemma QSI_sum_choose_le (n : ℕ) (g : ℕ × ℕ → ℝ) (B : ℝ)
    (hg : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal n, g ij ≤ B) (hB : 0 ≤ B) :
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, ((n.choose ij.1 : ℕ) : ℝ) * g ij ≤
      (n + 1) * 2 ^ n * B := by
  calc ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, ((n.choose ij.1 : ℕ) : ℝ) * g ij
      ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (2 : ℝ) ^ n * B := by
        refine Finset.sum_le_sum fun ij hij => ?_
        have h1 : ((n.choose ij.1 : ℕ) : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n _
        have h2 := hg ij hij
        have h3 : (0 : ℝ) ≤ ((n.choose ij.1 : ℕ) : ℝ) := by positivity
        by_cases hgn : 0 ≤ g ij
        · exact mul_le_mul h1 h2 hgn (by positivity)
        · nlinarith [mul_nonneg h3 hB]
    _ = (n + 1) * 2 ^ n * B := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
        push_cast; ring

/-- The Leibniz bound for `wirt`. -/
private lemma QSI_wirt_mul_le {f g : ℂ → ℂ} (hf : QSI_Sm f) (hg : QSI_Sm g) (a b : ℕ) (w : ℂ) (B : ℝ)
    (hB0 : 0 ≤ B)
    (hB : ∀ a1 a2 b1 b2, a1 + a2 = a → b1 + b2 = b →
      ‖wirt a1 b1 f w‖ * ‖wirt a2 b2 g w‖ ≤ B) :
    ‖wirt a b (fun x => f x * g x) w‖ ≤ ((a + 1) * 2 ^ a) * (((b + 1) * 2 ^ b) * B) := by
  rw [QSI_wirt_mul hf hg]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ aa ∈ Finset.HasAntidiagonal.antidiagonal a,
      ‖∑ bb ∈ Finset.HasAntidiagonal.antidiagonal b, ((a.choose aa.1 : ℕ) : ℂ) *
        ((b.choose bb.1 : ℕ) : ℂ) * (wirt aa.1 bb.1 f w * wirt aa.2 bb.2 g w)‖ ≤
      ((a.choose aa.1 : ℕ) : ℝ) * (((b + 1) * 2 ^ b) * B) := by
    intro aa haa
    refine (norm_sum_le _ _).trans ?_
    have e : ∀ bb ∈ Finset.HasAntidiagonal.antidiagonal b, ‖((a.choose aa.1 : ℕ) : ℂ) *
        ((b.choose bb.1 : ℕ) : ℂ) * (wirt aa.1 bb.1 f w * wirt aa.2 bb.2 g w)‖ =
        ((a.choose aa.1 : ℕ) : ℝ) * (((b.choose bb.1 : ℕ) : ℝ) *
          (‖wirt aa.1 bb.1 f w‖ * ‖wirt aa.2 bb.2 g w‖)) := by
      intro bb _
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at haa
    exact QSI_sum_choose_le b (fun bb => ‖wirt aa.1 bb.1 f w‖ * ‖wirt aa.2 bb.2 g w‖) B
      (fun bb hbb => by
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hbb
        exact hB _ _ _ _ haa hbb) hB0
  refine (Finset.sum_le_sum this).trans ?_
  exact QSI_sum_choose_le a (fun _ => ((b + 1) * 2 ^ b) * B) _ (fun _ _ => le_rfl)
    (by positivity)

/-- The generic bound on the derivatives of a form along the slice. -/
private lemma QSI_form_gen {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (p q : Idx D N) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : z.im ≠ 0) (V : Set (Idx D N → ℂ)) (hp : Pi.single p 1 ∈ V) (hq : Pi.single q 1 ∈ V)
    (Γ : ℝ) (hΓ : 1 ≤ Γ) (w : ℂ)
    (hG : ∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, Λ, z) (setEntry h p q w)‖ ≤ Γ)
    (x y : Idx D N → ℂ) (hx : x ∈ V) (hy : y ∈ V) (a b : ℕ) :
    ‖wirt a b (fun w' => resFactorEval (x, y, Λ, z) (setEntry h p q w')) w‖ ≤
      ((1 + a + b : ℕ) : ℝ) ^ (a + b) * Γ ^ (1 + a + b) := by
  have := resPoly_wirt_le h hh p q V {(Λ, z)} hp hq
    (by intro pr hpr; rw [Set.mem_singleton_iff.mp hpr]; exact ⟨hΛ, hz⟩)
    [((1 : ℂ), [(x, y, Λ, z)])] 1
    (by
      intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      refine ⟨by simp, fun f hf => ?_⟩
      simp only [List.mem_singleton] at hf
      subst hf
      exact ⟨hx, hy, Set.mem_singleton _⟩)
    Γ hΓ w (by intro pr hpr; rw [Set.mem_singleton_iff.mp hpr]; exact hG) a b
  simpa [QSI_eval_single] using this

/-- The row bound at order `m` with constant `C`. -/
private def QSI_RowP (m : ℕ) (C : ℝ) : Prop :=
  ∀ {D N : ℕ} (h : Idx D N → Idx D N → ℂ), (Matrix.of h).IsHermitian →
    ∀ (p q : Idx D N) (Λ : Matrix (Idx D N) (Idx D N) ℂ), Λ.IsHermitian → ∀ z : ℂ, z.im ≠ 0 →
    ∀ V : Set (Idx D N → ℂ), Pi.single p 1 ∈ V → Pi.single q 1 ∈ V →
    ∀ Γ : ℝ, 1 ≤ Γ → ∀ w : ℂ,
    (∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, Λ, z) (setEntry h p q w)‖ ≤ Γ) →
    ∀ x y : Idx D N → ℂ, x ∈ V → y ∈ V → ∀ a b : ℕ, a + b = m → 1 ≤ m →
      ‖wirt a b (fun w' => resFactorEval (x, y, Λ, z) (setEntry h p q w')) w‖ ≤
        C * Γ ^ m * (‖resFactorEval (x, Pi.single p 1, Λ, z) (setEntry h p q w)‖ +
          ‖resFactorEval (x, Pi.single q 1, Λ, z) (setEntry h p q w)‖)

/-- The column bound at order `m` with constant `C`. -/
private def QSI_ColP (m : ℕ) (C : ℝ) : Prop :=
  ∀ {D N : ℕ} (h : Idx D N → Idx D N → ℂ), (Matrix.of h).IsHermitian →
    ∀ (p q : Idx D N) (Λ : Matrix (Idx D N) (Idx D N) ℂ), Λ.IsHermitian → ∀ z : ℂ, z.im ≠ 0 →
    ∀ V : Set (Idx D N → ℂ), Pi.single p 1 ∈ V → Pi.single q 1 ∈ V →
    ∀ Γ : ℝ, 1 ≤ Γ → ∀ w : ℂ,
    (∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, Λ, z) (setEntry h p q w)‖ ≤ Γ) →
    ∀ x y : Idx D N → ℂ, x ∈ V → y ∈ V → ∀ a b : ℕ, a + b = m → 1 ≤ m →
      ‖wirt a b (fun w' => resFactorEval (x, y, Λ, z) (setEntry h p q w')) w‖ ≤
        C * Γ ^ m * (‖resFactorEval (Pi.single p 1, y, Λ, z) (setEntry h p q w)‖ +
          ‖resFactorEval (Pi.single q 1, y, Λ, z) (setEntry h p q w)‖)

private lemma QSI_count_le (n a' b' : ℕ) (hab : a' + b' + 1 = n) (B : ℝ) (hB0 : 0 ≤ B) :
    ((a' + 1 : ℝ) * 2 ^ a') * (((b' + 1 : ℝ) * 2 ^ b') * B) ≤ ((n : ℝ) + 1) ^ 2 * 2 ^ n * B := by
  have ha : (a' + 1 : ℝ) ≤ n + 1 := by exact_mod_cast (by omega : a' + 1 ≤ n + 1)
  have hb : (b' + 1 : ℝ) ≤ n + 1 := by exact_mod_cast (by omega : b' + 1 ≤ n + 1)
  have h2p : (2 : ℝ) ^ a' * 2 ^ b' ≤ 2 ^ n := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have := mul_le_mul (mul_le_mul ha hb (by positivity) (by positivity)) h2p (by positivity)
    (by positivity)
  calc ((a' + 1 : ℝ) * 2 ^ a') * (((b' + 1 : ℝ) * 2 ^ b') * B) =
        ((a' + 1 : ℝ) * (b' + 1)) * (2 ^ a' * 2 ^ b') * B := by ring
    _ ≤ ((n : ℝ) + 1) * (n + 1) * 2 ^ n * B := mul_le_mul_of_nonneg_right this hB0
    _ = ((n : ℝ) + 1) ^ 2 * 2 ^ n * B := by ring

private lemma QSI_gen_pow_le (n a2 b2 : ℕ) (h : 1 + a2 + b2 ≤ n) :
    ((1 + a2 + b2 : ℕ) : ℝ) ^ (a2 + b2) ≤ (n : ℝ) ^ n := by
  have h1n : ((1 + a2 + b2 : ℕ) : ℝ) ≤ n := by exact_mod_cast h
  calc ((1 + a2 + b2 : ℕ) : ℝ) ^ (a2 + b2) ≤ (n : ℝ) ^ (a2 + b2) :=
        pow_le_pow_left₀ (by positivity) h1n _
    _ ≤ (n : ℝ) ^ n := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ n)) (by omega)

/-- One derivative of a form, peeled off. -/
private lemma QSI_wirt_form_peel {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (p q : Idx D N) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : z.im ≠ 0) (x y : Idx D N → ℂ) (a b : ℕ) (hab : 1 ≤ a + b) (w : ℂ) :
    ∃ s t a' b', ((s = p ∧ t = q) ∨ (s = q ∧ t = p)) ∧ a' + b' + 1 = a + b ∧
      ‖wirt a b (fun w' => resFactorEval (x, y, Λ, z) (setEntry h p q w')) w‖ ≤
        ‖wirt a' b' (fun w' => resFactorEval (x, Pi.single s 1, Λ, z) (setEntry h p q w') *
          resFactorEval (Pi.single t 1, y, Λ, z) (setEntry h p q w')) w‖ := by
  have hc : ‖(-(if p = q then (1 / 2 : ℂ) else 1))‖ ≤ 1 := by
    rw [norm_neg]; split_ifs <;> norm_num
  obtain ⟨d1, d2⟩ := QSI_dW_form h hh p q x y Λ hΛ z hz
  rcases b with _ | b'
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    refine ⟨p, q, a', 0, Or.inl ⟨rfl, rfl⟩, by omega, ?_⟩
    have e : wirt (a' + 1) 0 (fun w' => resFactorEval (x, y, Λ, z) (setEntry h p q w')) =
        wirt a' 0 (dW (fun w' => resFactorEval (x, y, Λ, z) (setEntry h p q w'))) := by
      simp only [wirt, Function.iterate_zero, id, Function.iterate_succ_apply]
    rw [e, d1, QSI_wirt_cmul _ ((QSI_Sm_form h hh p q x _ Λ hΛ z hz).mul
      (QSI_Sm_form h hh p q _ y Λ hΛ z hz)), norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc
  · refine ⟨q, p, a, b', Or.inr ⟨rfl, rfl⟩, by omega, ?_⟩
    have e : wirt a (b' + 1) (fun w' => resFactorEval (x, y, Λ, z) (setEntry h p q w')) =
        wirt a b' (dWbar (fun w' => resFactorEval (x, y, Λ, z) (setEntry h p q w'))) := by
      simp only [wirt, Function.iterate_succ_apply]
    rw [e, d2, QSI_wirt_cmul _ ((QSI_Sm_form h hh p q x _ Λ hΛ z hz).mul
      (QSI_Sm_form h hh p q _ y Λ hΛ z hz)), norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc

private lemma QSI_form_row (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ QSI_RowP n C := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  have IH' : ∀ m, ∃ C : ℝ, 0 ≤ C ∧ (m < n → QSI_RowP m C) := fun m => by
    by_cases hm : m < n
    · obtain ⟨C, hC0, hC⟩ := IH m hm; exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hm⟩
  choose Cf hCf0 hCf using IH'
  set S := ∑ m ∈ Finset.range n, Cf m with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => hCf0 m
  refine ⟨((n : ℝ) + 1) ^ 2 * 2 ^ n * ((S + 1) * (n : ℝ) ^ n), by positivity, ?_⟩
  intro D N h hh p q Λ hΛ z hz V hp hq Γ hΓ w hG x y hx hy a b hab hn
  set row := ‖resFactorEval (x, Pi.single p 1, Λ, z) (setEntry h p q w)‖ +
    ‖resFactorEval (x, Pi.single q 1, Λ, z) (setEntry h p q w)‖ with hrow
  have hrow0 : 0 ≤ row := by positivity
  have hΓ0 : 0 ≤ Γ := by linarith
  set B := (S + 1) * (n : ℝ) ^ n * Γ ^ n * row with hBdef
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨s, t, a', b', hst, hab', hle⟩ := QSI_wirt_form_peel h hh p q Λ hΛ z hz x y a b (by omega) w
  rw [hab] at hab'
  have hsV : Pi.single s 1 ∈ V := by rcases hst with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
  have htV : Pi.single t 1 ∈ V := by rcases hst with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
  have hs : s = p ∨ s = q := by rcases hst with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  have h1 := QSI_wirt_mul_le (QSI_Sm_form h hh p q x _ Λ hΛ z hz)
    (QSI_Sm_form h hh p q _ y Λ hΛ z hz) a' b' w B hB0 (by
      intro a1 a2 b1 b2 ha hb
      have f1 : ‖wirt a1 b1 (fun w' => resFactorEval (x, Pi.single s 1, Λ, z)
          (setEntry h p q w')) w‖ ≤ (S + 1) * Γ ^ (a1 + b1) * row := by
        by_cases hn1 : a1 + b1 = 0
        · have ha1 : a1 = 0 := by omega
          have hb1 : b1 = 0 := by omega
          subst ha1 hb1
          simp only [wirt, Function.iterate_zero, id, add_zero, pow_zero, mul_one]
          have : ‖resFactorEval (x, Pi.single s 1, Λ, z) (setEntry h p q w)‖ ≤ row := by
            rcases hs with hs | hs <;> rw [hs, hrow] <;> linarith [norm_nonneg
              (resFactorEval (x, Pi.single p 1, Λ, z) (setEntry h p q w)), norm_nonneg
              (resFactorEval (x, Pi.single q 1, Λ, z) (setEntry h p q w))]
          nlinarith
        · have hlt : a1 + b1 < n := by omega
          have := hCf (a1 + b1) hlt h hh p q Λ hΛ z hz V hp hq Γ hΓ w hG x _ hx hsV a1 b1 rfl
            (by omega)
          have hle : Cf (a1 + b1) ≤ S + 1 := by
            have := Finset.single_le_sum (f := Cf) (fun m _ => hCf0 m) (Finset.mem_range.2 hlt)
            linarith
          calc _ ≤ Cf (a1 + b1) * Γ ^ (a1 + b1) * row := this
            _ ≤ (S + 1) * Γ ^ (a1 + b1) * row := by gcongr
      have f2 := QSI_form_gen h hh p q Λ hΛ z hz V hp hq Γ hΓ w hG _ y htV hy a2 b2
      have f3 := QSI_gen_pow_le n a2 b2 (by omega)
      have e : Γ ^ (a1 + b1) * Γ ^ (1 + a2 + b2) = Γ ^ n := by
        rw [← pow_add]; congr 1; omega
      calc _ ≤ ((S + 1) * Γ ^ (a1 + b1) * row) *
            (((1 + a2 + b2 : ℕ) : ℝ) ^ (a2 + b2) * Γ ^ (1 + a2 + b2)) :=
            mul_le_mul f1 f2 (norm_nonneg _) (by positivity)
        _ ≤ ((S + 1) * Γ ^ (a1 + b1) * row) * ((n : ℝ) ^ n * Γ ^ (1 + a2 + b2)) := by gcongr
        _ = B := by rw [hBdef, ← e]; ring)
  calc _ ≤ _ := hle
    _ ≤ _ := h1.trans (QSI_count_le n a' b' hab' B hB0)
    _ = _ := by rw [hBdef]; ring

private lemma QSI_form_col (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ QSI_ColP n C := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  have IH' : ∀ m, ∃ C : ℝ, 0 ≤ C ∧ (m < n → QSI_ColP m C) := fun m => by
    by_cases hm : m < n
    · obtain ⟨C, hC0, hC⟩ := IH m hm; exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hm⟩
  choose Cf hCf0 hCf using IH'
  set S := ∑ m ∈ Finset.range n, Cf m with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => hCf0 m
  refine ⟨((n : ℝ) + 1) ^ 2 * 2 ^ n * ((S + 1) * (n : ℝ) ^ n), by positivity, ?_⟩
  intro D N h hh p q Λ hΛ z hz V hp hq Γ hΓ w hG x y hx hy a b hab hn
  set row := ‖resFactorEval (Pi.single p 1, y, Λ, z) (setEntry h p q w)‖ +
    ‖resFactorEval (Pi.single q 1, y, Λ, z) (setEntry h p q w)‖ with hrow
  have hrow0 : 0 ≤ row := by positivity
  have hΓ0 : 0 ≤ Γ := by linarith
  set B := (S + 1) * (n : ℝ) ^ n * Γ ^ n * row with hBdef
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨s, t, a', b', hst, hab', hle⟩ := QSI_wirt_form_peel h hh p q Λ hΛ z hz x y a b (by omega) w
  rw [hab] at hab'
  have hsV : Pi.single s 1 ∈ V := by rcases hst with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
  have htV : Pi.single t 1 ∈ V := by rcases hst with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
  have ht : t = p ∨ t = q := by rcases hst with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]
  have h1 := QSI_wirt_mul_le (QSI_Sm_form h hh p q x _ Λ hΛ z hz)
    (QSI_Sm_form h hh p q _ y Λ hΛ z hz) a' b' w B hB0 (by
      intro a1 a2 b1 b2 ha hb
      have f1 : ‖wirt a2 b2 (fun w' => resFactorEval (Pi.single t 1, y, Λ, z)
          (setEntry h p q w')) w‖ ≤ (S + 1) * Γ ^ (a2 + b2) * row := by
        by_cases hn1 : a2 + b2 = 0
        · have ha1 : a2 = 0 := by omega
          have hb1 : b2 = 0 := by omega
          subst ha1 hb1
          simp only [wirt, Function.iterate_zero, id, add_zero, pow_zero, mul_one]
          have : ‖resFactorEval (Pi.single t 1, y, Λ, z) (setEntry h p q w)‖ ≤ row := by
            rcases ht with ht | ht <;> rw [ht, hrow] <;> linarith [norm_nonneg
              (resFactorEval (Pi.single p 1, y, Λ, z) (setEntry h p q w)), norm_nonneg
              (resFactorEval (Pi.single q 1, y, Λ, z) (setEntry h p q w))]
          nlinarith
        · have hlt : a2 + b2 < n := by omega
          have := hCf (a2 + b2) hlt h hh p q Λ hΛ z hz V hp hq Γ hΓ w hG _ y htV hy a2 b2 rfl
            (by omega)
          have hle : Cf (a2 + b2) ≤ S + 1 := by
            have := Finset.single_le_sum (f := Cf) (fun m _ => hCf0 m) (Finset.mem_range.2 hlt)
            linarith
          calc _ ≤ Cf (a2 + b2) * Γ ^ (a2 + b2) * row := this
            _ ≤ (S + 1) * Γ ^ (a2 + b2) * row := by gcongr
      have f2 := QSI_form_gen h hh p q Λ hΛ z hz V hp hq Γ hΓ w hG x _ hx hsV a1 b1
      have f3 := QSI_gen_pow_le n a1 b1 (by omega)
      have e : Γ ^ (a2 + b2) * Γ ^ (1 + a1 + b1) = Γ ^ n := by
        rw [← pow_add]; congr 1; omega
      calc _ ≤ (((1 + a1 + b1 : ℕ) : ℝ) ^ (a1 + b1) * Γ ^ (1 + a1 + b1)) *
            ((S + 1) * Γ ^ (a2 + b2) * row) :=
            mul_le_mul f2 f1 (norm_nonneg _) (by positivity)
        _ ≤ ((n : ℝ) ^ n * Γ ^ (1 + a1 + b1)) * ((S + 1) * Γ ^ (a2 + b2) * row) := by gcongr
        _ = B := by rw [hBdef, ← e]; ring)
  calc _ ≤ _ := hle
    _ ≤ _ := h1.trans (QSI_count_le n a' b' hab' B hB0)
    _ = _ := by rw [hBdef]; ring
/-- The jet of the product of two forms, the first with a fixed row vector, the second with a
fixed column vector. -/
private lemma QSI_Ajet (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {D N : ℕ} (h : Idx D N → Idx D N → ℂ), (Matrix.of h).IsHermitian →
    ∀ (p q : Idx D N) (Λ : Matrix (Idx D N) (Idx D N) ℂ), Λ.IsHermitian → ∀ z : ℂ, z.im ≠ 0 →
    ∀ V : Set (Idx D N → ℂ), Pi.single p 1 ∈ V → Pi.single q 1 ∈ V →
    ∀ Γ : ℝ, 1 ≤ Γ → ∀ w : ℂ,
    (∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, Λ, z) (setEntry h p q w)‖ ≤ Γ) →
    ∀ x1 y1 x2 y2 : Idx D N → ℂ, x1 ∈ V → y1 ∈ V → x2 ∈ V → y2 ∈ V → ∀ a b : ℕ, a + b = n →
      ‖wirt a b (fun w' => resFactorEval (x1, y1, Λ, z) (setEntry h p q w') *
          resFactorEval (x2, y2, Λ, z) (setEntry h p q w')) w‖ ≤
        C * Γ ^ n * ((‖resFactorEval (x1, Pi.single p 1, Λ, z) (setEntry h p q w)‖ +
          ‖resFactorEval (x1, Pi.single q 1, Λ, z) (setEntry h p q w)‖ +
          ‖resFactorEval (x1, y1, Λ, z) (setEntry h p q w)‖) *
          (‖resFactorEval (Pi.single p 1, y2, Λ, z) (setEntry h p q w)‖ +
          ‖resFactorEval (Pi.single q 1, y2, Λ, z) (setEntry h p q w)‖ +
          ‖resFactorEval (x2, y2, Λ, z) (setEntry h p q w)‖)) := by
  choose Cr hCr0 hCr using QSI_form_row
  choose Cc hCc0 hCc using QSI_form_col
  set Sr := (∑ m ∈ Finset.range (n + 1), Cr m) + 1 with hSr
  set Sc := (∑ m ∈ Finset.range (n + 1), Cc m) + 1 with hSc
  have hSr1 : 1 ≤ Sr := by
    have := Finset.sum_nonneg (s := Finset.range (n + 1)) fun m _ => hCr0 m
    linarith
  have hSc1 : 1 ≤ Sc := by
    have := Finset.sum_nonneg (s := Finset.range (n + 1)) fun m _ => hCc0 m
    linarith
  refine ⟨((n : ℝ) + 1) ^ 2 * 2 ^ n * (Sr * Sc), by positivity, ?_⟩
  intro D N h hh p q Λ hΛ z hz V hp hq Γ hΓ w hG x1 y1 x2 y2 hx1 hy1 hx2 hy2 a b hab
  set R := ‖resFactorEval (x1, Pi.single p 1, Λ, z) (setEntry h p q w)‖ +
    ‖resFactorEval (x1, Pi.single q 1, Λ, z) (setEntry h p q w)‖ +
    ‖resFactorEval (x1, y1, Λ, z) (setEntry h p q w)‖ with hR
  set Cl := ‖resFactorEval (Pi.single p 1, y2, Λ, z) (setEntry h p q w)‖ +
    ‖resFactorEval (Pi.single q 1, y2, Λ, z) (setEntry h p q w)‖ +
    ‖resFactorEval (x2, y2, Λ, z) (setEntry h p q w)‖ with hCl
  have hR0 : 0 ≤ R := by positivity
  have hCl0 : 0 ≤ Cl := by positivity
  have hΓ0 : 0 ≤ Γ := by linarith
  set B := Sr * Sc * Γ ^ n * (R * Cl) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have h1 := QSI_wirt_mul_le (QSI_Sm_form h hh p q x1 y1 Λ hΛ z hz)
    (QSI_Sm_form h hh p q x2 y2 Λ hΛ z hz) a b w B hB0 (by
      intro a1 a2 b1 b2 ha hb
      have f1 : ‖wirt a1 b1 (fun w' => resFactorEval (x1, y1, Λ, z) (setEntry h p q w')) w‖ ≤
          Sr * Γ ^ (a1 + b1) * R := by
        by_cases hn1 : a1 + b1 = 0
        · have ha1 : a1 = 0 := by omega
          have hb1 : b1 = 0 := by omega
          subst ha1 hb1
          simp only [wirt, Function.iterate_zero, id, add_zero, pow_zero, mul_one]
          have : ‖resFactorEval (x1, y1, Λ, z) (setEntry h p q w)‖ ≤ R := by
            rw [hR]; linarith [norm_nonneg (resFactorEval (x1, Pi.single p 1, Λ, z)
              (setEntry h p q w)), norm_nonneg (resFactorEval (x1, Pi.single q 1, Λ, z)
              (setEntry h p q w))]
          nlinarith
        · have := hCr (a1 + b1) h hh p q Λ hΛ z hz V hp hq Γ hΓ w hG x1 y1 hx1 hy1 a1 b1 rfl
            (by omega)
          have hle : Cr (a1 + b1) ≤ Sr := by
            have := Finset.single_le_sum (f := Cr) (fun m _ => hCr0 m)
              (Finset.mem_range.2 (by omega : a1 + b1 < n + 1))
            linarith
          refine this.trans ?_
          have : ‖resFactorEval (x1, Pi.single p 1, Λ, z) (setEntry h p q w)‖ +
              ‖resFactorEval (x1, Pi.single q 1, Λ, z) (setEntry h p q w)‖ ≤ R := by
            rw [hR]; linarith [norm_nonneg (resFactorEval (x1, y1, Λ, z) (setEntry h p q w))]
          have hg : 0 ≤ Γ ^ (a1 + b1) := by positivity
          calc _ ≤ Cr (a1 + b1) * Γ ^ (a1 + b1) * R :=
                mul_le_mul_of_nonneg_left this (mul_nonneg (hCr0 _) hg)
            _ ≤ Sr * Γ ^ (a1 + b1) * R := by gcongr
      have f2 : ‖wirt a2 b2 (fun w' => resFactorEval (x2, y2, Λ, z) (setEntry h p q w')) w‖ ≤
          Sc * Γ ^ (a2 + b2) * Cl := by
        by_cases hn1 : a2 + b2 = 0
        · have ha1 : a2 = 0 := by omega
          have hb1 : b2 = 0 := by omega
          subst ha1 hb1
          simp only [wirt, Function.iterate_zero, id, add_zero, pow_zero, mul_one]
          have : ‖resFactorEval (x2, y2, Λ, z) (setEntry h p q w)‖ ≤ Cl := by
            rw [hCl]; linarith [norm_nonneg (resFactorEval (Pi.single p 1, y2, Λ, z)
              (setEntry h p q w)), norm_nonneg (resFactorEval (Pi.single q 1, y2, Λ, z)
              (setEntry h p q w))]
          nlinarith
        · have := hCc (a2 + b2) h hh p q Λ hΛ z hz V hp hq Γ hΓ w hG x2 y2 hx2 hy2 a2 b2 rfl
            (by omega)
          have hle : Cc (a2 + b2) ≤ Sc := by
            have := Finset.single_le_sum (f := Cc) (fun m _ => hCc0 m)
              (Finset.mem_range.2 (by omega : a2 + b2 < n + 1))
            linarith
          refine this.trans ?_
          have : ‖resFactorEval (Pi.single p 1, y2, Λ, z) (setEntry h p q w)‖ +
              ‖resFactorEval (Pi.single q 1, y2, Λ, z) (setEntry h p q w)‖ ≤ Cl := by
            rw [hCl]; linarith [norm_nonneg (resFactorEval (x2, y2, Λ, z) (setEntry h p q w))]
          have hg : 0 ≤ Γ ^ (a2 + b2) := by positivity
          calc _ ≤ Cc (a2 + b2) * Γ ^ (a2 + b2) * Cl :=
                mul_le_mul_of_nonneg_left this (mul_nonneg (hCc0 _) hg)
            _ ≤ Sc * Γ ^ (a2 + b2) * Cl := by gcongr
      have e : Γ ^ (a1 + b1) * Γ ^ (a2 + b2) = Γ ^ n := by rw [← pow_add]; congr 1; omega
      calc _ ≤ (Sr * Γ ^ (a1 + b1) * R) * (Sc * Γ ^ (a2 + b2) * Cl) :=
            mul_le_mul f1 f2 (norm_nonneg _) (by positivity)
        _ = B := by rw [hBdef, ← e]; ring)
  have h2 : ((a + 1 : ℝ) * 2 ^ a) * (((b + 1 : ℝ) * 2 ^ b) * B) ≤ ((n : ℝ) + 1) ^ 2 * 2 ^ n * B := by
    have ha : (a + 1 : ℝ) ≤ n + 1 := by exact_mod_cast (by omega : a + 1 ≤ n + 1)
    have hb : (b + 1 : ℝ) ≤ n + 1 := by exact_mod_cast (by omega : b + 1 ≤ n + 1)
    have h2p : (2 : ℝ) ^ a * 2 ^ b = 2 ^ n := by rw [← pow_add, hab]
    calc ((a + 1 : ℝ) * 2 ^ a) * (((b + 1 : ℝ) * 2 ^ b) * B) =
          ((a + 1 : ℝ) * (b + 1)) * (2 ^ a * 2 ^ b) * B := by ring
      _ ≤ ((n : ℝ) + 1) * (n + 1) * 2 ^ n * B := by
          rw [h2p]; gcongr
      _ = ((n : ℝ) + 1) ^ 2 * 2 ^ n * B := by ring
  calc _ ≤ _ := h1.trans h2
    _ = _ := by rw [hBdef]; ring


/-! ### part g -/

/-- The scale of the slot with `q` differentiated factors among `m` derivatives. -/
private def QSI_kap2 (m q : ℕ) (T r1 r2 : ℝ) : ℝ :=
  if q = 0 then 0 else if q + 2 ≤ m then T ^ q else if q + 1 = m then
    (if m = 2 then r2 else r1 * T ^ (m - 2)) else if q = m then r1 * T ^ (m - 1) else 0

/-- The classified jet bound of a product of `M` factors. -/
private def QSI_Cl (M m : ℕ) (x T r1 r2 : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (M + 1), x ^ (M - q) * QSI_kap2 m q T r1 r2

/-- The constant of the classified jet bound. -/
private def QSI_Cst (M m : ℕ) : ℝ := (((m : ℝ) + 1) ^ 2 * 2 ^ m) ^ M

section
variable {T r1 r2 : ℝ} (hT : 0 ≤ T) (h1 : 0 ≤ r1) (h2 : 0 ≤ r2) (h1T : r1 ≤ T) (h2T : r2 ≤ T)
include hT h1 h2 h1T h2T

private lemma QSI_kap2_nonneg (m q : ℕ) : 0 ≤ QSI_kap2 m q T r1 r2 := by
  unfold QSI_kap2; split_ifs <;> positivity

private lemma QSI_kap2_le (m q : ℕ) : QSI_kap2 m q T r1 r2 ≤ T ^ q := by
  unfold QSI_kap2
  split_ifs with a b c d e
  · positivity
  · exact le_rfl
  · subst d
    have : q = 1 := by omega
    subst this; simpa using h2T
  · have hq : q = m - 1 := by omega
    rw [hq]
    have e1 : m - 1 = (m - 2) + 1 := by omega
    rw [e1, pow_succ]
    nlinarith [pow_nonneg hT (m - 2)]
  · rw [e]
    have e1 : m = (m - 1) + 1 := by omega
    conv_rhs => rw [e1]
    rw [pow_succ]
    nlinarith [pow_nonneg hT (m - 1)]
  · positivity

private lemma QSI_kap2_land (m1 m2 q : ℕ) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2) :
    QSI_kap2 m1 q T r1 r2 * (if m2 = 1 then r1 else T) ≤ QSI_kap2 (m1 + m2) (q + 1) T r1 r2 := by
  have hb : (if m2 = 1 then r1 else T) ≤ T := by split_ifs <;> linarith
  have hb0 : 0 ≤ (if m2 = 1 then r1 else T) := by split_ifs <;> linarith
  by_cases hq : q = 0
  · subst hq; simp only [QSI_kap2, if_true, zero_mul]; exact QSI_kap2_nonneg hT h1 h2 h1T h2T _ _
  by_cases g1 : q + 2 ≤ m1
  · -- generic slot
    have e1 : QSI_kap2 m1 q T r1 r2 = T ^ q := by simp [QSI_kap2, hq, g1]
    have e2 : QSI_kap2 (m1 + m2) (q + 1) T r1 r2 = T ^ (q + 1) := by
      simp [QSI_kap2, show q + 1 + 2 ≤ m1 + m2 by omega]
    rw [e1, e2, pow_succ]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  by_cases g2 : q + 1 = m1
  · -- the slot with one double derivative
    have e1 : QSI_kap2 m1 q T r1 r2 = (if m1 = 2 then r2 else r1 * T ^ (m1 - 2)) := by
      simp [QSI_kap2, hq, g1, g2]
    have hV : (if m1 = 2 then r2 else r1 * T ^ (m1 - 2)) ≤ T ^ q := by
      split_ifs with hm
      · have : q = 1 := by omega
        subst this; simpa using h2T
      · have e3 : q = (m1 - 2) + 1 := by omega
        rw [e3, pow_succ]; nlinarith [pow_nonneg hT (m1 - 2)]
    have hV0 : 0 ≤ (if m1 = 2 then r2 else r1 * T ^ (m1 - 2)) := by split_ifs <;> positivity
    rw [e1]
    by_cases hm2 : m2 = 1
    · subst hm2
      have e2 : QSI_kap2 (m1 + 1) (q + 1) T r1 r2 = r1 * T ^ (m1 + 1 - 2) := by
        have : m1 + 1 ≠ 2 := by omega
        simp [QSI_kap2, show ¬ (q + 1 + 2 ≤ m1 + 1) by omega, show q + 1 + 1 = m1 + 1 by omega,
          this]
      rw [e2, if_pos rfl, show m1 + 1 - 2 = q by omega]
      exact (mul_le_mul_of_nonneg_right hV h1).trans (le_of_eq (mul_comm _ _))
    · have e2 : QSI_kap2 (m1 + m2) (q + 1) T r1 r2 = T ^ (q + 1) := by
        simp [QSI_kap2, show q + 1 + 2 ≤ m1 + m2 by omega]
      rw [e2, if_neg hm2, pow_succ]
      exact mul_le_mul_of_nonneg_right hV hT
  by_cases g3 : q = m1
  · -- all derivatives single
    subst g3
    have e1 : QSI_kap2 q q T r1 r2 = r1 * T ^ (q - 1) := by
      simp [QSI_kap2, hq, show ¬ (q + 1 = q) by omega]
    rw [e1]
    have hU : r1 * T ^ (q - 1) ≤ T ^ q := by
      have e3 : q = (q - 1) + 1 := by omega
      conv_rhs => rw [e3]
      rw [pow_succ]; nlinarith [pow_nonneg hT (q - 1)]
    rcases Nat.lt_or_ge m2 3 with hm | hm
    · by_cases hm2 : m2 = 1
      · subst hm2
        have e2 : QSI_kap2 (q + 1) (q + 1) T r1 r2 = r1 * T ^ q := by
          simp [QSI_kap2]
        rw [e2, if_pos rfl]
        have : r1 * T ^ (q - 1) * r1 ≤ r1 * T ^ (q - 1) * T :=
          mul_le_mul_of_nonneg_left h1T (by positivity)
        have e3 : r1 * T ^ (q - 1) * T = r1 * T ^ q := by
          rw [mul_assoc, ← pow_succ, show q - 1 + 1 = q by omega]
        linarith
      · have hm2' : m2 = 2 := by omega
        subst hm2'
        have e2 : QSI_kap2 (q + 2) (q + 1) T r1 r2 = r1 * T ^ q := by
          have : q + 2 ≠ 2 := by omega
          simp [QSI_kap2, this, hq]
        rw [e2, if_neg (by norm_num)]
        rw [mul_assoc, ← pow_succ, show q - 1 + 1 = q by omega]
    · have e2 : QSI_kap2 (q + m2) (q + 1) T r1 r2 = T ^ (q + 1) := by
        simp [QSI_kap2, show q + 1 + 2 ≤ q + m2 by omega]
      rw [e2, pow_succ]
      exact mul_le_mul hU hb hb0 (by positivity)
  · -- empty slot
    have e1 : QSI_kap2 m1 q T r1 r2 = 0 := by simp [QSI_kap2, hq, g1, g2, g3]
    rw [e1, zero_mul]
    exact QSI_kap2_nonneg hT h1 h2 h1T h2T _ _

private lemma QSI_Cl_nonneg {x : ℝ} (hx : 0 ≤ x) (M m : ℕ) : 0 ≤ QSI_Cl M m x T r1 r2 :=
  Finset.sum_nonneg fun q _ => mul_nonneg (pow_nonneg hx _) (QSI_kap2_nonneg hT h1 h2 h1T h2T _ _)

private lemma QSI_Cl_land {x : ℝ} (hx : 0 ≤ x) (M m1 m2 : ℕ) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2) :
    QSI_Cl M m1 x T r1 r2 * (if m2 = 1 then r1 else T) ≤ QSI_Cl (M + 1) (m1 + m2) x T r1 r2 := by
  unfold QSI_Cl
  rw [Finset.sum_mul, Finset.sum_range_succ' _ (M + 1)]
  have h0 : 0 ≤ x ^ (M + 1 - 0) * QSI_kap2 (m1 + m2) 0 T r1 r2 :=
    mul_nonneg (pow_nonneg hx _) (QSI_kap2_nonneg hT h1 h2 h1T h2T _ _)
  have : ∑ q ∈ Finset.range (M + 1), x ^ (M - q) * QSI_kap2 m1 q T r1 r2 *
      (if m2 = 1 then r1 else T) ≤
      ∑ q ∈ Finset.range (M + 1), x ^ (M + 1 - (q + 1)) * QSI_kap2 (m1 + m2) (q + 1) T r1 r2 := by
    refine Finset.sum_le_sum fun q _ => ?_
    rw [show M + 1 - (q + 1) = M - q by omega, mul_assoc]
    exact mul_le_mul_of_nonneg_left (QSI_kap2_land hT h1 h2 h1T h2T m1 m2 q hm1 hm2)
      (pow_nonneg hx _)
  linarith

private lemma QSI_Cl_x {x : ℝ} (hx : 0 ≤ x) (M m : ℕ) :
    QSI_Cl M m x T r1 r2 * x ≤ QSI_Cl (M + 1) m x T r1 r2 := by
  unfold QSI_Cl
  rw [Finset.sum_mul, Finset.sum_range_succ _ (M + 1)]
  have h0 : 0 ≤ x ^ (M + 1 - (M + 1)) * QSI_kap2 m (M + 1) T r1 r2 :=
    mul_nonneg (pow_nonneg hx _) (QSI_kap2_nonneg hT h1 h2 h1T h2T _ _)
  have : ∑ q ∈ Finset.range (M + 1), x ^ (M - q) * QSI_kap2 m q T r1 r2 * x ≤
      ∑ q ∈ Finset.range (M + 1), x ^ (M + 1 - q) * QSI_kap2 m q T r1 r2 := by
    refine Finset.sum_le_sum fun q hq => le_of_eq ?_
    rw [Finset.mem_range] at hq
    rw [show M + 1 - q = (M - q) + 1 by omega, pow_succ]
    ring
  linarith

private lemma QSI_Cl_one {x : ℝ} (hx : 0 ≤ x) (M m : ℕ) :
    x ^ M * QSI_kap2 m 1 T r1 r2 ≤ QSI_Cl (M + 1) m x T r1 r2 := by
  unfold QSI_Cl
  have := Finset.single_le_sum (f := fun q => x ^ (M + 1 - q) * QSI_kap2 m q T r1 r2)
    (fun q _ => mul_nonneg (pow_nonneg hx _) (QSI_kap2_nonneg hT h1 h2 h1T h2T _ _))
    (Finset.mem_range.2 (by omega : 1 < M + 1 + 1))
  simpa using this

end

private lemma QSI_Cst_one_le (M m : ℕ) : 1 ≤ QSI_Cst M m := by
  unfold QSI_Cst
  apply one_le_pow₀
  have : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  nlinarith

private lemma QSI_Cst_mono (M : ℕ) {m1 m : ℕ} (h : m1 ≤ m) : QSI_Cst M m1 ≤ QSI_Cst M m := by
  unfold QSI_Cst
  apply pow_le_pow_left₀ (by positivity)
  have : (m1 : ℝ) ≤ m := by exact_mod_cast h
  have h2 : (2 : ℝ) ^ m1 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) h
  have h3 : ((m1 : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity); linarith
  exact mul_le_mul h3 h2 (by positivity) (by positivity)

private lemma QSI_count2 (a b : ℕ) (B : ℝ) (hB0 : 0 ≤ B) :
    ((a + 1 : ℝ) * 2 ^ a) * (((b + 1 : ℝ) * 2 ^ b) * B) ≤
      (((a + b : ℕ) : ℝ) + 1) ^ 2 * 2 ^ (a + b) * B := by
  have ha : (a + 1 : ℝ) ≤ ((a + b : ℕ) : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b)]
  have hb : (b + 1 : ℝ) ≤ ((a + b : ℕ) : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]
  have h2p : (2 : ℝ) ^ a * 2 ^ b = 2 ^ (a + b) := by rw [← pow_add]
  calc ((a + 1 : ℝ) * 2 ^ a) * (((b + 1 : ℝ) * 2 ^ b) * B) =
        ((a + 1 : ℝ) * (b + 1)) * (2 ^ a * 2 ^ b) * B := by ring
    _ ≤ ((((a + b : ℕ) : ℝ) + 1) * (((a + b : ℕ) : ℝ) + 1)) * 2 ^ (a + b) * B := by
        rw [h2p]; gcongr
    _ = _ := by ring

/-- The jet of a product of `M` factors with the jets of `Q` and `Q̄`. -/
private lemma QSI_Yjet (φ : ℕ → ℂ → ℂ) (hφ : ∀ s, QSI_Sm (φ s)) (w : ℂ) (x T r1 r2 Γ : ℝ) (L : ℕ)
    (hx : 0 ≤ x) (hT : 0 ≤ T) (h1 : 0 ≤ r1) (h2 : 0 ≤ r2) (h1T : r1 ≤ T) (h2T : r2 ≤ T)
    (hΓ : 1 ≤ Γ) (h0 : ∀ s, ‖φ s w‖ ≤ x)
    (hg : ∀ s a b, 1 ≤ a + b → a + b ≤ L → ‖wirt a b (φ s) w‖ ≤ Γ ^ (a + b) * T)
    (h1' : ∀ s a b, a + b = 1 → ‖wirt a b (φ s) w‖ ≤ Γ * r1)
    (h2' : ∀ s a b, a + b = 2 → ‖wirt a b (φ s) w‖ ≤ Γ ^ 2 * r2) :
    ∀ M, 1 ≤ M → ∀ a b, a + b ≤ L → ‖wirt a b (fun w' => ∏ s ∈ Finset.range M, φ s w') w‖ ≤
      if a + b = 0 then x ^ M else
        QSI_Cst M (a + b) * Γ ^ (a + b) * QSI_Cl M (a + b) x T r1 r2 := by
  have hΓ0 : 0 ≤ Γ := by linarith
  -- the factor bound in slot form
  have hf1 : ∀ s a b, 1 ≤ a + b → a + b ≤ L →
      ‖wirt a b (φ s) w‖ ≤ Γ ^ (a + b) * QSI_kap2 (a + b) 1 T r1 r2 := by
    intro s a b hab hL
    rcases Nat.lt_or_ge (a + b) 3 with hm | hm
    · by_cases hm1 : a + b = 1
      · have e : QSI_kap2 (a + b) 1 T r1 r2 = r1 := by rw [hm1]; simp [QSI_kap2]
        rw [e, hm1, pow_one]; exact h1' s a b hm1
      · have hm2 : a + b = 2 := by omega
        have e : QSI_kap2 (a + b) 1 T r1 r2 = r2 := by rw [hm2]; simp [QSI_kap2]
        rw [e, hm2]; exact h2' s a b hm2
    · have e : QSI_kap2 (a + b) 1 T r1 r2 = T := by
        simp [QSI_kap2, show 1 + 2 ≤ a + b by omega]
      rw [e]; exact hg s a b hab hL
  have hfb : ∀ s a b, 1 ≤ a + b → a + b ≤ L →
      ‖wirt a b (φ s) w‖ ≤ Γ ^ (a + b) * (if a + b = 1 then r1 else T) := by
    intro s a b hab hL
    split_ifs with hm
    · rw [hm, pow_one]; exact h1' s a b hm
    · exact hg s a b hab hL
  intro M hM
  induction M with
  | zero => omega
  | succ M ih =>
    intro a b hL
    by_cases hM0 : M = 0
    · subst hM0
      simp only [Finset.prod_range_one, zero_add, pow_one]
      split_ifs with hab
      · have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha hb
        simpa [wirt] using h0 0
      · have hcl : QSI_Cl 1 (a + b) x T r1 r2 = QSI_kap2 (a + b) 1 T r1 r2 := by
          simp [QSI_Cl, Finset.sum_range_succ, QSI_kap2]
        rw [hcl]
        have := hf1 0 a b (by omega) hL
        have hc := QSI_Cst_one_le 1 (a + b)
        have hk := QSI_kap2_nonneg hT h1 h2 h1T h2T (a + b) 1
        calc _ ≤ Γ ^ (a + b) * QSI_kap2 (a + b) 1 T r1 r2 := this
          _ ≤ _ := by nlinarith [pow_nonneg hΓ0 (a + b), mul_nonneg (pow_nonneg hΓ0 (a + b)) hk]
    have ihM := ih (by omega)
    have hY : QSI_Sm (fun w' => ∏ s ∈ Finset.range M, φ s w') :=
      contDiff_prod fun s _ => hφ s
    have e : (fun w' => ∏ s ∈ Finset.range (M + 1), φ s w') =
        fun w' => (∏ s ∈ Finset.range M, φ s w') * φ M w' := by
      funext w'; rw [Finset.prod_range_succ]
    rw [e]
    split_ifs with hab
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb
      have := ihM 0 0 (by omega)
      simp only [add_zero, if_true] at this
      simp only [wirt, Function.iterate_zero, id, norm_mul, pow_succ]
      simp only [wirt, Function.iterate_zero, id] at this
      exact mul_le_mul this (h0 M) (norm_nonneg _) (pow_nonneg hx _)
    · set m := a + b with hm
      have hCl0 := QSI_Cl_nonneg hT h1 h2 h1T h2T hx (M + 1) m
      set B := QSI_Cst M m * Γ ^ m * QSI_Cl (M + 1) m x T r1 r2 with hB
      have hB0 : 0 ≤ B := by
        have := QSI_Cst_one_le M m; positivity
      have hL := QSI_wirt_mul_le hY (hφ M) a b w B hB0 (by
        intro a1 a2 b1 b2 ha hb
        have iY := ihM a1 b1 (by omega)
        by_cases hm1 : a1 + b1 = 0
        · rw [if_pos hm1] at iY
          have hm2 : a2 + b2 = m := by omega
          have := hf1 M a2 b2 (by omega) (by omega)
          rw [hm2] at this
          have hk := QSI_Cl_one hT h1 h2 h1T h2T hx M m
          have hc := QSI_Cst_one_le M m
          calc _ ≤ x ^ M * (Γ ^ m * QSI_kap2 m 1 T r1 r2) :=
                mul_le_mul iY this (norm_nonneg _) (pow_nonneg hx _)
            _ = Γ ^ m * (x ^ M * QSI_kap2 m 1 T r1 r2) := by ring
            _ ≤ Γ ^ m * QSI_Cl (M + 1) m x T r1 r2 :=
                mul_le_mul_of_nonneg_left hk (pow_nonneg hΓ0 _)
            _ ≤ B := by rw [hB]; nlinarith [mul_nonneg (pow_nonneg hΓ0 m) hCl0]
        · rw [if_neg hm1] at iY
          have hCst := QSI_Cst_mono M (show a1 + b1 ≤ m by omega)
          have hCl1 := QSI_Cl_nonneg hT h1 h2 h1T h2T hx M (a1 + b1)
          by_cases hm2 : a2 + b2 = 0
          · have ha2 : a2 = 0 := by omega
            have hb2 : b2 = 0 := by omega
            subst ha2 hb2
            have hφ0 : ‖wirt 0 0 (φ M) w‖ ≤ x := by simpa [wirt] using h0 M
            have hland := QSI_Cl_x hT h1 h2 h1T h2T hx M m
            have em : a1 + b1 = m := by omega
            rw [em] at iY hCl1
            have hC1 := QSI_Cst_one_le M m
            calc _ ≤ (QSI_Cst M m * Γ ^ m * QSI_Cl M m x T r1 r2) * x :=
                  mul_le_mul iY hφ0 (norm_nonneg _) (by positivity)
              _ = QSI_Cst M m * Γ ^ m * (QSI_Cl M m x T r1 r2 * x) := by ring
              _ ≤ B := by
                  rw [hB]
                  exact mul_le_mul_of_nonneg_left hland (by positivity)
          · have := hfb M a2 b2 (by omega) (by omega)
            have hland := QSI_Cl_land hT h1 h2 h1T h2T hx M (a1 + b1) (a2 + b2) (by omega)
              (by omega)
            rw [show a1 + b1 + (a2 + b2) = m by omega] at hland
            have hb0 : 0 ≤ (if a2 + b2 = 1 then r1 else T) := by split_ifs <;> assumption
            have epow : Γ ^ (a1 + b1) * Γ ^ (a2 + b2) = Γ ^ m := by rw [← pow_add]; congr 1; omega
            calc _ ≤ (QSI_Cst M (a1 + b1) * Γ ^ (a1 + b1) * QSI_Cl M (a1 + b1) x T r1 r2) *
                  (Γ ^ (a2 + b2) * (if a2 + b2 = 1 then r1 else T)) :=
                  mul_le_mul iY this (norm_nonneg _) (by have := QSI_Cst_one_le M (a1 + b1); positivity)
              _ = QSI_Cst M (a1 + b1) * (Γ ^ (a1 + b1) * Γ ^ (a2 + b2)) *
                  (QSI_Cl M (a1 + b1) x T r1 r2 * (if a2 + b2 = 1 then r1 else T)) := by ring
              _ ≤ QSI_Cst M m * Γ ^ m * QSI_Cl (M + 1) m x T r1 r2 := by
                  rw [epow]
                  exact mul_le_mul (mul_le_mul_of_nonneg_right hCst (pow_nonneg hΓ0 _)) hland
                    (mul_nonneg hCl1 hb0) (by have := QSI_Cst_one_le M m; positivity)
              _ = B := rfl)
      refine hL.trans ?_
      refine (QSI_count2 a b B hB0).trans (le_of_eq ?_)
      rw [hB, ← hm]
      unfold QSI_Cst
      rw [pow_succ]
      ring


/-! ### part h -/

section
variable {ι : Type*} [Fintype ι] (a b : ι → ℝ) (wv : ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
  (hwv : 0 ≤ wv) (haW : ∑ s, a s ^ 2 ≤ wv ^ 2) (hbW : ∑ s, b s ^ 2 ≤ wv ^ 2)
include ha hb hwv haW hbW

private lemma QSI_W_sum_a : ∑ s, a s ≤ Real.sqrt (Fintype.card ι) * wv := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
  rw [Finset.card_univ] at h1
  have h2 : (∑ s, a s) ^ 2 ≤ (Real.sqrt (Fintype.card ι) * wv) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact h1.trans (mul_le_mul_of_nonneg_left haW (by positivity))
  exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2

private lemma QSI_W_sum_b : ∑ s, b s ≤ Real.sqrt (Fintype.card ι) * wv :=
  QSI_W_sum_a b a wv hb ha hwv hbW haW

private lemma QSI_W_sum_ab : ∑ s, a s * b s ≤ wv ^ 2 := by
  have h1 : ∀ s, a s * b s ≤ (a s ^ 2 + b s ^ 2) / 2 := fun s => by
    nlinarith [sq_nonneg (a s - b s)]
  refine (Finset.sum_le_sum fun s _ => h1 s).trans ?_
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  linarith

private lemma QSI_W_sum_aa : ∑ s, a s * a s ≤ wv ^ 2 := by
  simpa [sq] using haW

private lemma QSI_W_sum_bb : ∑ s, b s * b s ≤ wv ^ 2 := by
  simpa [sq] using hbW

/-- `Σ_{pq} a_q b_p ≤ n wv²`. -/
private lemma QSI_W_S0 : ∑ p, ∑ q, a q * b p ≤ Fintype.card ι * wv ^ 2 := by
  have e : ∑ p, ∑ q, a q * b p = (∑ q, a q) * ∑ p, b p := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
  rw [e]
  have h1 := QSI_W_sum_a a b wv ha hb hwv haW hbW
  have h2 := QSI_W_sum_b a b wv ha hb hwv haW hbW
  have h3 : 0 ≤ ∑ q, a q := Finset.sum_nonneg fun q _ => ha q
  calc (∑ q, a q) * ∑ p, b p ≤ (Real.sqrt (Fintype.card ι) * wv) *
        (Real.sqrt (Fintype.card ι) * wv) := mul_le_mul h1 h2 (Finset.sum_nonneg fun p _ => hb p)
          (by positivity)
    _ = Fintype.card ι * wv ^ 2 := by
        rw [show Real.sqrt (Fintype.card ι) * wv * (Real.sqrt (Fintype.card ι) * wv) =
          Real.sqrt (Fintype.card ι) ^ 2 * wv ^ 2 by ring, Real.sq_sqrt (by positivity)]

/-- `Σ_{pq} (a_p + a_q)(b_p + b_q) ≤ 4 n wv²`. -/
private lemma QSI_W_S1 : ∑ p, ∑ q, (a p + a q) * (b p + b q) ≤ 4 * (Fintype.card ι * wv ^ 2) := by
  have h0 := QSI_W_S0 a b wv ha hb hwv haW hbW
  have h0' := QSI_W_S0 b a wv hb ha hwv hbW haW
  have hn : (0 : ℝ) ≤ Fintype.card ι := by positivity
  have e1 : ∑ p, ∑ q : ι, a p * b p = Fintype.card ι * ∑ p, a p * b p := by
    simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]
  have e2 : ∑ p : ι, ∑ q, a q * b q = Fintype.card ι * ∑ q, a q * b q := by
    rw [Finset.sum_comm]; simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]
  have e3 : ∑ p, ∑ q, a p * b q = ∑ p, ∑ q, b q * a p := by
    simp only [mul_comm]
  have hab := QSI_W_sum_ab a b wv ha hb hwv haW hbW
  have : ∑ p, ∑ q, (a p + a q) * (b p + b q) = (∑ p, ∑ q : ι, a p * b p) +
      (∑ p, ∑ q, a p * b q) + (∑ p, ∑ q, a q * b p) + ∑ p : ι, ∑ q, a q * b q := by
    simp only [add_mul, mul_add, Finset.sum_add_distrib]; ring
  rw [this, e1, e2]
  have e4 : ∑ p, ∑ q, a p * b q = ∑ q, ∑ p, b q * a p := by rw [Finset.sum_comm]; simp only [mul_comm]
  rw [e4]
  have := QSI_W_S0 b a wv hb ha hwv hbW haW
  nlinarith [mul_le_mul_of_nonneg_left hab hn]

/-- The sums with three Ward factors. -/
private lemma QSI_W_S3 : ∑ p, ∑ q, a q * b p * (a p + a q + b p + b q) ≤
    4 * (Real.sqrt (Fintype.card ι) * wv ^ 3) := by
  have sa := QSI_W_sum_a a b wv ha hb hwv haW hbW
  have sb := QSI_W_sum_b a b wv ha hb hwv haW hbW
  have sab := QSI_W_sum_ab a b wv ha hb hwv haW hbW
  have saa := QSI_W_sum_aa a b wv ha hb hwv haW hbW
  have sbb := QSI_W_sum_bb a b wv ha hb hwv haW hbW
  have na : 0 ≤ ∑ s, a s := Finset.sum_nonneg fun s _ => ha s
  have nb : 0 ≤ ∑ s, b s := Finset.sum_nonneg fun s _ => hb s
  have nab : 0 ≤ ∑ s, a s * b s := Finset.sum_nonneg fun s _ => mul_nonneg (ha s) (hb s)
  have naa : 0 ≤ ∑ s, a s * a s := Finset.sum_nonneg fun s _ => mul_nonneg (ha s) (ha s)
  have nbb : 0 ≤ ∑ s, b s * b s := Finset.sum_nonneg fun s _ => mul_nonneg (hb s) (hb s)
  have e : ∑ p, ∑ q, a q * b p * (a p + a q + b p + b q) =
      (∑ p, a p * b p) * (∑ q, a q) + (∑ p, b p) * (∑ q, a q * a q) +
        (∑ p, b p * b p) * (∑ q, a q) + (∑ p, b p) * (∑ q, a q * b q) := by
    simp only [Finset.sum_mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [e]
  have hn := Real.sqrt_nonneg (Fintype.card ι)
  have t1 := mul_le_mul sab sa na (by positivity)
  have t2 := mul_le_mul sb saa naa (by positivity)
  have t3 := mul_le_mul sbb sa na (by positivity)
  have t4 := mul_le_mul sb sab nab (by positivity)
  nlinarith

private lemma QSI_W_S4 : ∑ p, ∑ q, a q * b p * (a p * b q + a q * b p) ≤ 2 * wv ^ 4 := by
  have sab := QSI_W_sum_ab a b wv ha hb hwv haW hbW
  have saa := QSI_W_sum_aa a b wv ha hb hwv haW hbW
  have sbb := QSI_W_sum_bb a b wv ha hb hwv haW hbW
  have nab : 0 ≤ ∑ s, a s * b s := Finset.sum_nonneg fun s _ => mul_nonneg (ha s) (hb s)
  have naa : 0 ≤ ∑ s, a s * a s := Finset.sum_nonneg fun s _ => mul_nonneg (ha s) (ha s)
  have e : ∑ p, ∑ q, a q * b p * (a p * b q + a q * b p) =
      (∑ p, a p * b p) * (∑ q, a q * b q) + (∑ p, b p * b p) * (∑ q, a q * a q) := by
    simp only [Finset.sum_mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [e]
  have t1 := mul_le_mul sab sab nab (by positivity)
  have t2 := mul_le_mul sbb saa naa (by positivity)
  nlinarith

private lemma QSI_W_S5 : ∑ p, ∑ q, (a p + a q) * (a p * b q + a q * b p) ≤
    4 * (Real.sqrt (Fintype.card ι) * wv ^ 3) := by
  have sa := QSI_W_sum_a a b wv ha hb hwv haW hbW
  have sb := QSI_W_sum_b a b wv ha hb hwv haW hbW
  have sab := QSI_W_sum_ab a b wv ha hb hwv haW hbW
  have saa := QSI_W_sum_aa a b wv ha hb hwv haW hbW
  have na : 0 ≤ ∑ s, a s := Finset.sum_nonneg fun s _ => ha s
  have nb : 0 ≤ ∑ s, b s := Finset.sum_nonneg fun s _ => hb s
  have nab : 0 ≤ ∑ s, a s * b s := Finset.sum_nonneg fun s _ => mul_nonneg (ha s) (hb s)
  have naa : 0 ≤ ∑ s, a s * a s := Finset.sum_nonneg fun s _ => mul_nonneg (ha s) (ha s)
  have e : ∑ p, ∑ q, (a p + a q) * (a p * b q + a q * b p) =
      (∑ p, a p * a p) * (∑ q, b q) + (∑ p, a p * b p) * (∑ q, a q) +
        (∑ p, a p) * (∑ q, a q * b q) + (∑ p, b p) * (∑ q, a q * a q) := by
    simp only [Finset.sum_mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [e]
  have hn := Real.sqrt_nonneg (Fintype.card ι)
  have t1 := mul_le_mul saa sb nb (by positivity)
  have t2 := mul_le_mul sab sa na (by positivity)
  have t3 := mul_le_mul sa sab nab (by positivity)
  have t4 := mul_le_mul sb saa naa (by positivity)
  nlinarith

end


/-! ### part i -/

/-- The normalized scales of the moment inequality for `Q`: `s = N^{-1/2}`, `ζ`, `Γ`,
`Z = 1 + |z|`, `ϖ = Z² Γ⁴ ζ³ ≤ λ`, `u² = ϖ λ`. -/
structure QSI_Sc (s ζ Γ Z lam u : ℝ) : Prop where
  s0 : 0 < s
  sζ : s ≤ ζ
  ζ1 : ζ ≤ 1
  Γ1 : 1 ≤ Γ
  sΓ : s * Γ ≤ 1
  Z1 : 1 ≤ Z
  wl : Z ^ 2 * Γ ^ 4 * ζ ^ 3 ≤ lam
  u0 : 0 ≤ u
  u2 : u ^ 2 = Z ^ 2 * Γ ^ 4 * ζ ^ 3 * lam

section
variable {s ζ Γ Z lam u : ℝ} (H : QSI_Sc s ζ Γ Z lam u)
include H

private lemma QSI_Sc.ζ0 : 0 < ζ := lt_of_lt_of_le H.s0 H.sζ
private lemma QSI_Sc.Γ0 : 0 < Γ := lt_of_lt_of_le one_pos H.Γ1
private lemma QSI_Sc.Z0 : 0 < Z := lt_of_lt_of_le one_pos H.Z1

private lemma QSI_Sc.wu : Z ^ 2 * Γ ^ 4 * ζ ^ 3 ≤ u := by
  have h0 : 0 ≤ Z ^ 2 * Γ ^ 4 * ζ ^ 3 := by
    have := H.ζ0; have := H.Γ0; have := H.Z0; positivity
  have : (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ 2 ≤ u ^ 2 := by
    rw [H.u2, sq]; exact mul_le_mul_of_nonneg_left H.wl h0
  exact abs_le_of_sq_le_sq' this H.u0 |>.2

private lemma QSI_Sc.lam0 : 0 ≤ lam := by
  have : 0 ≤ Z ^ 2 * Γ ^ 4 * ζ ^ 3 := by have := H.ζ0; have := H.Γ0; have := H.Z0; positivity
  linarith [H.wl]

/-- `ϖ^j ≤ u^j`. -/
private lemma QSI_Sc.wpow (j : ℕ) : (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j ≤ u ^ j := by
  have h0 : 0 ≤ Z ^ 2 * Γ ^ 4 * ζ ^ 3 := by
    have := H.ζ0; have := H.Γ0; have := H.Z0; positivity
  exact pow_le_pow_left₀ h0 H.wu j

/-- `λ ϖ^{j+1} ≤ u^{j+2}`. -/
private lemma QSI_Sc.lwpow (j : ℕ) : lam * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ (j + 1) ≤ u ^ (j + 2) := by
  have h1 : lam * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ (j + 1) = u ^ 2 * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j := by
    rw [H.u2, pow_succ]; ring
  rw [h1, pow_add u j 2, mul_comm (u ^ j)]
  exact mul_le_mul_of_nonneg_left (H.wpow j) (by positivity)

/-- `s^m ≤ ζ^m`. -/
private lemma QSI_Sc.spow (m : ℕ) : s ^ m ≤ ζ ^ m := pow_le_pow_left₀ H.s0.le H.sζ m

/-- `(s Γ)^m ≤ 1`. -/
private lemma QSI_Sc.sΓpow (m : ℕ) : (s * Γ) ^ m ≤ 1 :=
  pow_le_one₀ (mul_nonneg H.s0.le H.Γ0.le) H.sΓ

/-- `ζ^a ≤ ζ^b` for `b ≤ a`. -/
private lemma QSI_Sc.ζanti {a b : ℕ} (h : b ≤ a) : ζ ^ a ≤ ζ ^ b :=
  pow_le_pow_of_le_one H.ζ0.le H.ζ1 h

/-- `Γ^a ≤ Γ^b` for `a ≤ b`. -/
private lemma QSI_Sc.Γmono {a b : ℕ} (h : a ≤ b) : Γ ^ a ≤ Γ ^ b := pow_le_pow_right₀ H.Γ1 h

/-- `Z^a ≤ Z^b` for `a ≤ b`. -/
private lemma QSI_Sc.Zmono {a b : ℕ} (h : a ≤ b) : Z ^ a ≤ Z ^ b := pow_le_pow_right₀ H.Z1 h

/-- The generic slots: `s^{k-1} Γ^k ζ² (Z Γ ζ²)^q ≤ u^{q+1}` for `q + 2 ≤ k`. -/
private lemma QSI_cmp_gen (k q : ℕ) (hq : q + 2 ≤ k) :
    s ^ (k - 1) * Γ ^ k * ζ ^ 2 * (Z * Γ * ζ ^ 2) ^ q ≤ u ^ (q + 1) := by
  have hζ := H.ζ0; have hΓ := H.Γ0; have hZ := H.Z0; have hs := H.s0
  set d := k - q - 2 with hd
  have e : s ^ (k - 1) * Γ ^ k * ζ ^ 2 * (Z * Γ * ζ ^ 2) ^ q =
      (s * Γ) ^ d * (s ^ (q + 1) * (Z ^ q * Γ ^ (2 * q + 2) * ζ ^ (2 * q + 2))) := by
    rw [show k - 1 = d + (q + 1) by omega, show k = d + (q + 2) by omega]
    ring
  rw [e]
  have h1 := H.sΓpow d
  have h2 : s ^ (q + 1) * (Z ^ q * Γ ^ (2 * q + 2) * ζ ^ (2 * q + 2)) ≤
      (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ (q + 1) := by
    calc s ^ (q + 1) * (Z ^ q * Γ ^ (2 * q + 2) * ζ ^ (2 * q + 2)) ≤
          ζ ^ (q + 1) * (Z ^ (2 * (q + 1)) * Γ ^ (4 * (q + 1)) * ζ ^ (2 * q + 2)) := by
          apply mul_le_mul (H.spow _) _ (by positivity) (by positivity)
          gcongr <;> first | exact H.Z1 | exact H.Γ1 | omega
      _ = (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ (q + 1) := by ring
  calc (s * Γ) ^ d * (s ^ (q + 1) * (Z ^ q * Γ ^ (2 * q + 2) * ζ ^ (2 * q + 2))) ≤
        1 * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ (q + 1) :=
        mul_le_mul h1 h2 (by positivity) zero_le_one
    _ ≤ u ^ (q + 1) := by rw [one_mul]; exact H.wpow _

/-- The slot `(B)`: `s^{k-1} Γ^{k-1} (Z Γ ζ²)^{k-1} (λ ζ³ + ζ⁶) ≤ 2 u^{k+1}`. -/
private lemma QSI_cmp_B (k : ℕ) (hk : 1 ≤ k) :
    s ^ (k - 1) * Γ ^ (k - 1) * (Z * Γ * ζ ^ 2) ^ (k - 1) * (lam * ζ ^ 3 + ζ ^ 6) ≤
      2 * u ^ (k + 1) := by
  have hζ := H.ζ0; have hΓ := H.Γ0; have hZ := H.Z0; have hs := H.s0; have hl := H.lam0
  set j := k - 1 with hj
  have base : s ^ j * Γ ^ j * (Z * Γ * ζ ^ 2) ^ j ≤ (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j := by
    calc s ^ j * Γ ^ j * (Z * Γ * ζ ^ 2) ^ j ≤ ζ ^ j * Γ ^ j * (Z * Γ * ζ ^ 2) ^ j := by
          gcongr; exact H.sζ
      _ = Z ^ j * Γ ^ (2 * j) * ζ ^ (3 * j) := by ring
      _ ≤ Z ^ (2 * j) * Γ ^ (4 * j) * ζ ^ (3 * j) := by
          gcongr <;> first | exact H.Z1 | exact H.Γ1 | omega
      _ = (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j := by ring
  have w3 : ζ ^ 3 ≤ Z ^ 2 * Γ ^ 4 * ζ ^ 3 := by
    have : 1 ≤ Z ^ 2 * Γ ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ H.Z1)
      (one_le_pow₀ H.Γ1)
    nlinarith [pow_pos hζ 3]
  have t1 : lam * ζ ^ 3 * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j ≤ u ^ (k + 1) := by
    have := H.lwpow j
    rw [show j + 2 = k + 1 by omega] at this
    calc lam * ζ ^ 3 * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j ≤
          lam * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j := by gcongr
      _ = lam * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ (j + 1) := by ring
      _ ≤ _ := this
  have t2 : ζ ^ 6 * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j ≤ u ^ (k + 1) := by
    calc ζ ^ 6 * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j = ζ ^ 3 * ζ ^ 3 * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j := by
          ring
      _ ≤ (Z ^ 2 * Γ ^ 4 * ζ ^ 3) * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j := by
          gcongr
      _ = (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ (k + 1) := by rw [show k + 1 = j + 2 by omega]; ring
      _ ≤ _ := H.wpow _
  have hb0 : 0 ≤ lam * ζ ^ 3 + ζ ^ 6 := by positivity
  calc s ^ j * Γ ^ j * (Z * Γ * ζ ^ 2) ^ j * (lam * ζ ^ 3 + ζ ^ 6) ≤
        (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j * (lam * ζ ^ 3 + ζ ^ 6) :=
        mul_le_mul_of_nonneg_right base hb0
    _ = lam * ζ ^ 3 * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j + ζ ^ 6 * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ j := by
        ring
    _ ≤ 2 * u ^ (k + 1) := by linarith

private lemma QSI_Sc.w1 : 0 ≤ Z ^ 2 * Γ ^ 4 * ζ ^ 3 := by
  have := H.ζ0; have := H.Γ0; have := H.Z0; positivity

/-- `λ ϖ ≤ u²` and `ϖ² ≤ u²`. -/
private lemma QSI_Sc.u2l : lam * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ≤ u ^ 2 := by rw [H.u2]; ring_nf; rfl

private lemma QSI_Sc.u2w : (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ 2 ≤ u ^ 2 := H.wpow 2

/-- The slot `(B')`: `s^{k-1} Γ^{k-1} (Z Γ ζ²)^{k-2} (λ ζ³ + ζ⁶) ≤ 2 u^k`, `k ≥ 2`. -/
private lemma QSI_cmp_B' (k : ℕ) (hk : 2 ≤ k) :
    s ^ (k - 1) * Γ ^ (k - 1) * (Z * Γ * ζ ^ 2) ^ (k - 2) * (lam * ζ ^ 3 + ζ ^ 6) ≤
      2 * u ^ k := by
  have hζ := H.ζ0; have hΓ := H.Γ0; have hZ := H.Z0; have hs := H.s0; have hl := H.lam0
  set j := k - 2 with hj
  set w := Z ^ 2 * Γ ^ 4 * ζ ^ 3 with hw
  have hw0 : 0 ≤ w := H.w1
  have base : s ^ (k - 1) * Γ ^ (k - 1) * (Z * Γ * ζ ^ 2) ^ j ≤ Γ * ζ * w ^ j := by
    calc s ^ (k - 1) * Γ ^ (k - 1) * (Z * Γ * ζ ^ 2) ^ j ≤
          ζ ^ (k - 1) * Γ ^ (k - 1) * (Z * Γ * ζ ^ 2) ^ j := by gcongr; exact H.sζ
      _ = Γ * ζ * (Z ^ j * Γ ^ (2 * j) * ζ ^ (3 * j)) := by
          rw [show k - 1 = j + 1 by omega]; ring
      _ ≤ Γ * ζ * (Z ^ (2 * j) * Γ ^ (4 * j) * ζ ^ (3 * j)) := by
          gcongr <;> first | exact H.Z1 | exact H.Γ1 | omega
      _ = Γ * ζ * w ^ j := by rw [hw]; ring
  have t1 : Γ * ζ * lam * ζ ^ 3 ≤ lam * w := by
    have : Γ * ζ ^ 4 ≤ w := by
      rw [hw]
      have h1 : Γ ≤ Γ ^ 4 := by
        calc Γ = Γ ^ 1 := (pow_one Γ).symm
          _ ≤ Γ ^ 4 := H.Γmono (by norm_num)
      have h2 : ζ ^ 4 ≤ ζ ^ 3 := H.ζanti (by norm_num)
      have h3 : 1 ≤ Z ^ 2 := one_le_pow₀ H.Z1
      calc Γ * ζ ^ 4 ≤ Γ ^ 4 * ζ ^ 3 := mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 1 * (Γ ^ 4 * ζ ^ 3) := by ring
        _ ≤ Z ^ 2 * (Γ ^ 4 * ζ ^ 3) := by gcongr
        _ = Z ^ 2 * Γ ^ 4 * ζ ^ 3 := by ring
    nlinarith
  have t2 : Γ * ζ * ζ ^ 6 ≤ w ^ 2 := by
    rw [hw]
    have h1 : Γ ≤ Γ ^ 8 := by
      calc Γ = Γ ^ 1 := (pow_one Γ).symm
        _ ≤ Γ ^ 8 := H.Γmono (by norm_num)
    have h2 : ζ ^ 7 ≤ ζ ^ 6 := H.ζanti (by norm_num)
    have h3 : 1 ≤ Z ^ 4 := one_le_pow₀ H.Z1
    calc Γ * ζ * ζ ^ 6 = Γ * ζ ^ 7 := by ring
      _ ≤ Γ ^ 8 * ζ ^ 6 := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 1 * (Γ ^ 8 * ζ ^ 6) := by ring
      _ ≤ Z ^ 4 * (Γ ^ 8 * ζ ^ 6) := by gcongr
      _ = (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ 2 := by ring
  have u1 : lam * w * w ^ j ≤ u ^ k := by
    have := H.lwpow j
    rw [show j + 2 = k by omega, pow_succ] at this
    linarith [show lam * w * w ^ j = lam * (w ^ j * w) by ring]
  have u2 : w ^ 2 * w ^ j ≤ u ^ k := by
    have := H.wpow k
    rw [show k = j + 2 by omega] at this ⊢
    calc w ^ 2 * w ^ j = w ^ (j + 2) := by ring
      _ ≤ _ := this
  have hb0 : 0 ≤ lam * ζ ^ 3 + ζ ^ 6 := by positivity
  calc s ^ (k - 1) * Γ ^ (k - 1) * (Z * Γ * ζ ^ 2) ^ j * (lam * ζ ^ 3 + ζ ^ 6) ≤
        Γ * ζ * w ^ j * (lam * ζ ^ 3 + ζ ^ 6) := mul_le_mul_of_nonneg_right base hb0
    _ = (Γ * ζ * lam * ζ ^ 3) * w ^ j + (Γ * ζ * ζ ^ 6) * w ^ j := by ring
    _ ≤ lam * w * w ^ j + w ^ 2 * w ^ j := by
        gcongr
    _ ≤ 2 * u ^ k := by linarith

/-- The slot `(C)`: `s^{k-1} Γ^{k-1} (Z Γ ζ²)^{k-2} (Γ λ ζ² + Γ ζ⁵ + ζ⁶) ≤ 3 u^k`, `k ≥ 2`. -/
private lemma QSI_cmp_C (k : ℕ) (hk : 2 ≤ k) :
    s ^ (k - 1) * Γ ^ (k - 1) * (Z * Γ * ζ ^ 2) ^ (k - 2) *
      (Γ * lam * ζ ^ 2 + Γ * ζ ^ 5 + ζ ^ 6) ≤ 3 * u ^ k := by
  have hζ := H.ζ0; have hΓ := H.Γ0; have hZ := H.Z0; have hs := H.s0; have hl := H.lam0
  set j := k - 2 with hj
  set w := Z ^ 2 * Γ ^ 4 * ζ ^ 3 with hw
  have hw0 : 0 ≤ w := H.w1
  have base : s ^ (k - 1) * Γ ^ (k - 1) * (Z * Γ * ζ ^ 2) ^ j ≤ Γ * ζ * w ^ j := by
    calc s ^ (k - 1) * Γ ^ (k - 1) * (Z * Γ * ζ ^ 2) ^ j ≤
          ζ ^ (k - 1) * Γ ^ (k - 1) * (Z * Γ * ζ ^ 2) ^ j := by gcongr; exact H.sζ
      _ = Γ * ζ * (Z ^ j * Γ ^ (2 * j) * ζ ^ (3 * j)) := by
          rw [show k - 1 = j + 1 by omega]; ring
      _ ≤ Γ * ζ * (Z ^ (2 * j) * Γ ^ (4 * j) * ζ ^ (3 * j)) := by
          gcongr <;> first | exact H.Z1 | exact H.Γ1 | omega
      _ = Γ * ζ * w ^ j := by rw [hw]; ring
  have hZ2 : 1 ≤ Z ^ 2 := one_le_pow₀ H.Z1
  have hZ4 : 1 ≤ Z ^ 4 := one_le_pow₀ H.Z1
  have t1 : Γ * ζ * (Γ * lam * ζ ^ 2) ≤ lam * w := by
    have : Γ ^ 2 * ζ ^ 3 ≤ w := by
      rw [hw]
      have h1 : Γ ^ 2 ≤ Γ ^ 4 := H.Γmono (by norm_num)
      calc Γ ^ 2 * ζ ^ 3 ≤ Γ ^ 4 * ζ ^ 3 := by gcongr
        _ = 1 * (Γ ^ 4 * ζ ^ 3) := by ring
        _ ≤ Z ^ 2 * (Γ ^ 4 * ζ ^ 3) := by gcongr
        _ = _ := by ring
    have e : Γ * ζ * (Γ * lam * ζ ^ 2) = lam * (Γ ^ 2 * ζ ^ 3) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left this hl
  have t2 : Γ * ζ * (Γ * ζ ^ 5) ≤ w ^ 2 := by
    rw [hw]
    have h1 : Γ ^ 2 ≤ Γ ^ 8 := H.Γmono (by norm_num)
    calc Γ * ζ * (Γ * ζ ^ 5) = Γ ^ 2 * ζ ^ 6 := by ring
      _ ≤ Γ ^ 8 * ζ ^ 6 := by gcongr
      _ = 1 * (Γ ^ 8 * ζ ^ 6) := by ring
      _ ≤ Z ^ 4 * (Γ ^ 8 * ζ ^ 6) := by gcongr
      _ = _ := by ring
  have t3 : Γ * ζ * ζ ^ 6 ≤ w ^ 2 := by
    rw [hw]
    have h1 : Γ ≤ Γ ^ 8 := by
      calc Γ = Γ ^ 1 := (pow_one Γ).symm
        _ ≤ Γ ^ 8 := H.Γmono (by norm_num)
    have h2 : ζ ^ 7 ≤ ζ ^ 6 := H.ζanti (by norm_num)
    calc Γ * ζ * ζ ^ 6 = Γ * ζ ^ 7 := by ring
      _ ≤ Γ ^ 8 * ζ ^ 6 := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 1 * (Γ ^ 8 * ζ ^ 6) := by ring
      _ ≤ Z ^ 4 * (Γ ^ 8 * ζ ^ 6) := by gcongr
      _ = _ := by ring
  have u1 : lam * w * w ^ j ≤ u ^ k := by
    have := H.lwpow j
    rw [show j + 2 = k by omega, pow_succ] at this
    linarith [show lam * w * w ^ j = lam * (w ^ j * w) by ring]
  have u2 : w ^ 2 * w ^ j ≤ u ^ k := by
    have := H.wpow k
    rw [show k = j + 2 by omega] at this ⊢
    calc w ^ 2 * w ^ j = w ^ (j + 2) := by ring
      _ ≤ _ := this
  have hb0 : 0 ≤ Γ * lam * ζ ^ 2 + Γ * ζ ^ 5 + ζ ^ 6 := by positivity
  calc s ^ (k - 1) * Γ ^ (k - 1) * (Z * Γ * ζ ^ 2) ^ j * (Γ * lam * ζ ^ 2 + Γ * ζ ^ 5 + ζ ^ 6) ≤
        Γ * ζ * w ^ j * (Γ * lam * ζ ^ 2 + Γ * ζ ^ 5 + ζ ^ 6) :=
        mul_le_mul_of_nonneg_right base hb0
    _ = (Γ * ζ * (Γ * lam * ζ ^ 2)) * w ^ j + (Γ * ζ * (Γ * ζ ^ 5)) * w ^ j +
        (Γ * ζ * ζ ^ 6) * w ^ j := by ring
    _ ≤ lam * w * w ^ j + w ^ 2 * w ^ j + w ^ 2 * w ^ j := by gcongr
    _ ≤ 3 * u ^ k := by linarith

/-- The slot `(D)`: `s (Γ λ ζ³ + Z Γ² ζ⁵ + Γ² ζ⁵ + Γ ζ⁶) ≤ 4 u²`. -/
private lemma QSI_cmp_D :
    s * (Γ * lam * ζ ^ 3 + Z * Γ ^ 2 * ζ ^ 5 + Γ ^ 2 * ζ ^ 5 + Γ * ζ ^ 6) ≤ 4 * u ^ 2 := by
  have hζ := H.ζ0; have hΓ := H.Γ0; have hZ := H.Z0; have hs := H.s0; have hl := H.lam0
  have hu1 := H.u2l
  have hu2 := H.u2w
  have hZ2 : Z ≤ Z ^ 4 := by
    calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ Z ^ 4 := H.Zmono (by norm_num)
  have hZ4 : 1 ≤ Z ^ 4 := one_le_pow₀ H.Z1
  have hZ2' : 1 ≤ Z ^ 2 := one_le_pow₀ H.Z1
  have g2 : Γ ^ 2 ≤ Γ ^ 8 := H.Γmono (by norm_num)
  have g1 : Γ ≤ Γ ^ 4 := by
    calc Γ = Γ ^ 1 := (pow_one Γ).symm
      _ ≤ Γ ^ 4 := H.Γmono (by norm_num)
  have g18 : Γ ≤ Γ ^ 8 := le_trans g1 (H.Γmono (by norm_num))
  have z43 : ζ ^ 4 ≤ ζ ^ 3 := H.ζanti (by norm_num)
  have z76 : ζ ^ 7 ≤ ζ ^ 6 := H.ζanti (by norm_num)
  have sz := H.sζ
  have a1 : s * (Γ * lam * ζ ^ 3) ≤ lam * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) := by
    calc s * (Γ * lam * ζ ^ 3) ≤ ζ * (Γ * lam * ζ ^ 3) := by gcongr
      _ = lam * (Γ * ζ ^ 4) := by ring
      _ ≤ lam * (Γ ^ 4 * ζ ^ 3) := by gcongr
      _ = lam * (1 * (Γ ^ 4 * ζ ^ 3)) := by ring
      _ ≤ lam * (Z ^ 2 * (Γ ^ 4 * ζ ^ 3)) := by gcongr
      _ = _ := by ring
  have a2 : s * (Z * Γ ^ 2 * ζ ^ 5) ≤ (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ 2 := by
    calc s * (Z * Γ ^ 2 * ζ ^ 5) ≤ ζ * (Z * Γ ^ 2 * ζ ^ 5) := by gcongr
      _ = Z * Γ ^ 2 * ζ ^ 6 := by ring
      _ ≤ Z ^ 4 * Γ ^ 8 * ζ ^ 6 := by gcongr
      _ = _ := by ring
  have a3 : s * (Γ ^ 2 * ζ ^ 5) ≤ (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ 2 := by
    calc s * (Γ ^ 2 * ζ ^ 5) ≤ ζ * (Γ ^ 2 * ζ ^ 5) := by gcongr
      _ = 1 * (Γ ^ 2 * ζ ^ 6) := by ring
      _ ≤ Z ^ 4 * (Γ ^ 8 * ζ ^ 6) := by gcongr
      _ = _ := by ring
  have a4 : s * (Γ * ζ ^ 6) ≤ (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ 2 := by
    calc s * (Γ * ζ ^ 6) ≤ ζ * (Γ * ζ ^ 6) := by gcongr
      _ = 1 * (Γ * ζ ^ 7) := by ring
      _ ≤ Z ^ 4 * (Γ ^ 8 * ζ ^ 6) := by gcongr
      _ = _ := by ring
  nlinarith

/-- The order-one rest: `λ ζ³ + ζ⁶ ≤ 2 u²`. -/
private lemma QSI_cmp_one : lam * ζ ^ 3 + ζ ^ 6 ≤ 2 * u ^ 2 := by
  have hζ := H.ζ0; have hΓ := H.Γ0; have hl := H.lam0
  have hu1 := H.u2l
  have hu2 := H.u2w
  have hZ2 : 1 ≤ Z ^ 2 := one_le_pow₀ H.Z1
  have hZ4 : 1 ≤ Z ^ 4 := one_le_pow₀ H.Z1
  have g4 : 1 ≤ Γ ^ 4 := one_le_pow₀ H.Γ1
  have g8 : 1 ≤ Γ ^ 8 := one_le_pow₀ H.Γ1
  have a1 : lam * ζ ^ 3 ≤ lam * (Z ^ 2 * Γ ^ 4 * ζ ^ 3) := by
    apply mul_le_mul_of_nonneg_left _ hl
    calc ζ ^ 3 = 1 * 1 * ζ ^ 3 := by ring
      _ ≤ Z ^ 2 * Γ ^ 4 * ζ ^ 3 := by gcongr
  have a2 : ζ ^ 6 ≤ (Z ^ 2 * Γ ^ 4 * ζ ^ 3) ^ 2 := by
    calc ζ ^ 6 = 1 * 1 * ζ ^ 6 := by ring
      _ ≤ Z ^ 4 * Γ ^ 8 * ζ ^ 6 := by gcongr
      _ = _ := by ring
  linarith

end


/-! ### part j -/

/-- The refined bound on the first derivatives of `Q_{kl}` along the slice in the entry `(j, i)`. -/
def QSI_r1b {ι : Type*} (n N lam ζ : ℝ) (a b : ι → ℝ) (i j : ι) : ℝ :=
  lam * (a j + a i + b j + b i) + n⁻¹ * (a j * b i + a i * b j + 2 * (N * ζ ^ 4))

/-- The refined bound on the second derivatives of `Q_{kl}` along the slice in the entry `(j, i)`. -/
def QSI_r2b {ι : Type*} (n N lam Γ T ζ : ℝ) (a b : ι → ℝ) (i j : ι) : ℝ :=
  (Γ * lam + Γ * T) * (a j + a i + b j + b i) +
    n⁻¹ * (2 * Γ * ((a j + a i) * (b j + b i)) + 8 * (Γ * (N * ζ ^ 4)))

/-- The bound on the derivatives of order `r` of `(G B)_{ki} G_{jl}`. -/
private def QSI_Abd {ι : Type*} (CA : ℕ → ℝ) (A0 : ι → ι → ℝ) (Γ : ℝ) (a b : ι → ℝ) (r : ℕ) (i j : ι) :
    ℝ :=
  if r = 0 then A0 i j else CA r * Γ ^ r * ((a j + a i) * (2 * (b j + b i)))

/-- The data of the Ward sums at a point of the good event. -/
structure QSI_WD {ι : Type*} [Fintype ι] (n N ζ Γ : ℝ) (a b : ι → ℝ) (A0 : ι → ι → ℝ) : Prop where
  card : (Fintype.card ι : ℝ) = n
  N1 : 1 ≤ N
  D1 : N ≤ n
  a0 : ∀ s, 0 ≤ a s
  b0 : ∀ s, 0 ≤ b s
  aW : ∑ s, a s ^ 2 ≤ (2 * Real.sqrt N * ζ) ^ 2
  bW : ∑ s, b s ^ 2 ≤ (2 * Real.sqrt N * ζ) ^ 2
  aΓ : ∀ s, a s ≤ 2 * Γ
  bΓ : ∀ s, b s ≤ Γ
  A00 : ∀ i j, 0 ≤ A0 i j
  A0ab : ∀ i j, A0 i j ≤ a i * b j

section
variable {ι : Type*} [Fintype ι] {n N ζ Γ : ℝ} {a b : ι → ℝ} {A0 : ι → ι → ℝ}
  (W : QSI_WD n N ζ Γ a b A0) (hζ : 0 ≤ ζ)
include W hζ

private lemma QSI_WD.wv0 : 0 ≤ 2 * Real.sqrt N * ζ := by positivity

private lemma QSI_WD.sqn : Real.sqrt (Fintype.card ι) = Real.sqrt n := by rw [W.card]

private lemma QSI_WD.N0 : 0 < N := lt_of_lt_of_le one_pos W.N1

private lemma QSI_WD.wv2 : (2 * Real.sqrt N * ζ) ^ 2 = 4 * N * ζ ^ 2 := by
  rw [mul_pow, mul_pow, Real.sq_sqrt (W.N0 hζ).le]; ring

/-- `Σ_{ij} (a_j + a_i)(b_j + b_i) ≤ 16 n N ζ²`. -/
private lemma QSI_WD.S1 : ∑ i, ∑ j, (a j + a i) * (b j + b i) ≤ 16 * (n * N * ζ ^ 2) := by
  have := QSI_W_S1 a b _ W.a0 W.b0 (W.wv0 hζ) W.aW W.bW
  rw [W.card, W.wv2 hζ, Finset.sum_comm] at this
  linarith

/-- `Σ_{ij} a_i b_j ≤ 4 n N ζ²`. -/
private lemma QSI_WD.S0 : ∑ i, ∑ j, a i * b j ≤ 4 * (n * N * ζ ^ 2) := by
  have := QSI_W_S0 a b _ W.a0 W.b0 (W.wv0 hζ) W.aW W.bW
  rw [W.card, W.wv2 hζ, Finset.sum_comm] at this
  linarith

/-- `Σ_{ij} a_i b_j (a_j + a_i + b_j + b_i) ≤ 32 √n N^{3/2} ζ³`. -/
private lemma QSI_WD.S3 : ∑ i, ∑ j, a i * b j * (a j + a i + b j + b i) ≤
    32 * (Real.sqrt n * Real.sqrt N ^ 3 * ζ ^ 3) := by
  have := QSI_W_S3 a b _ W.a0 W.b0 (W.wv0 hζ) W.aW W.bW
  rw [W.sqn hζ, Finset.sum_comm] at this
  have e : (2 * Real.sqrt N * ζ) ^ 3 = 8 * Real.sqrt N ^ 3 * ζ ^ 3 := by ring
  rw [e] at this
  linarith

/-- `Σ_{ij} a_i b_j (a_j b_i + a_i b_j) ≤ 32 N² ζ⁴`. -/
private lemma QSI_WD.S4 : ∑ i, ∑ j, a i * b j * (a j * b i + a i * b j) ≤ 32 * (N ^ 2 * ζ ^ 4) := by
  have := QSI_W_S4 a b _ W.a0 W.b0 (W.wv0 hζ) W.aW W.bW
  rw [Finset.sum_comm] at this
  have e : (2 * Real.sqrt N * ζ) ^ 4 = 16 * N ^ 2 * ζ ^ 4 := by
    rw [show (2 * Real.sqrt N * ζ) ^ 4 = ((2 * Real.sqrt N * ζ) ^ 2) ^ 2 by ring, W.wv2 hζ]; ring
  rw [e] at this
  linarith

/-- `Σ_{ij} (a_j + a_i)(a_j b_i + a_i b_j) ≤ 32 √n N^{3/2} ζ³`. -/
private lemma QSI_WD.S5 : ∑ i, ∑ j, (a j + a i) * (a j * b i + a i * b j) ≤
    32 * (Real.sqrt n * Real.sqrt N ^ 3 * ζ ^ 3) := by
  have := QSI_W_S5 a b _ W.a0 W.b0 (W.wv0 hζ) W.aW W.bW
  rw [W.sqn hζ, Finset.sum_comm] at this
  have e : (2 * Real.sqrt N * ζ) ^ 3 = 8 * Real.sqrt N ^ 3 * ζ ^ 3 := by ring
  rw [e] at this
  linarith

/-- `Σ_{ij} a_i b_j (a_j + a_i) ≤ 32 √n N^{3/2} ζ³`. -/
private lemma QSI_WD.S3a : ∑ i, ∑ j, a i * b j * (a j + a i) ≤
    32 * (Real.sqrt n * Real.sqrt N ^ 3 * ζ ^ 3) := by
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_) (W.S3 hζ)
  have := W.a0 i; have := W.b0 j; have := W.b0 i; have := W.a0 j
  have h0 : 0 ≤ a i * b j := by positivity
  nlinarith

end



section
variable {ι : Type*} [Fintype ι] {n N D ζ Γ s Z lam u T cq : ℝ} {a b : ι → ℝ}
  {A0 r1 r2 : ι → ι → ℝ} (W : QSI_WD n N ζ Γ a b A0) (H : QSI_Sc s ζ Γ Z lam u)
  (hsN : s ^ 2 * N = 1) (hn : n = D * N) (hD : 1 ≤ D) (hT : T = cq * (Z * Γ * ζ ^ 2))
  (hcq : 0 ≤ cq)
  (hr1 : ∀ i j, 0 ≤ r1 i j ∧ r1 i j ≤ T ∧ Γ * r1 i j ≤ QSI_r1b n N lam ζ a b i j)
  (hr2 : ∀ i j, 0 ≤ r2 i j ∧ r2 i j ≤ T ∧ Γ ^ 2 * r2 i j ≤ QSI_r2b n N lam Γ T ζ a b i j)
include W H hsN hn hD hT hcq

private lemma QSI_K.n0 : 0 < n := by
  have := W.N0 H.ζ0.le; rw [hn]; nlinarith

private lemma QSI_K.T0 : 0 ≤ T := by
  rw [hT]; have := H.ζ0; have := H.Γ0; have := H.Z0; positivity

private lemma QSI_K.sq : Real.sqrt n * Real.sqrt N ^ 3 = Real.sqrt D * N ^ 2 := by
  have hN := (W.N0 H.ζ0.le).le
  rw [hn, Real.sqrt_mul (by linarith) N]
  have : Real.sqrt N ^ 4 = N ^ 2 := by
    rw [show Real.sqrt N ^ 4 = (Real.sqrt N ^ 2) ^ 2 by ring, Real.sq_sqrt hN]
  rw [show Real.sqrt D * Real.sqrt N * Real.sqrt N ^ 3 = Real.sqrt D * Real.sqrt N ^ 4 by ring, this]

private lemma QSI_K.Nζ : 1 ≤ N * ζ ^ 2 := by
  have h1 : s ^ 2 ≤ ζ ^ 2 := pow_le_pow_left₀ H.s0.le H.sζ 2
  have hN := W.N0 H.ζ0.le
  nlinarith

private lemma QSI_K.sD : Real.sqrt D ≤ D := by
  have h1 : (0 : ℝ) ≤ D := by linarith
  rw [Real.sqrt_le_left h1]
  nlinarith

/-- The Ward sum against `ρ₁` with the undifferentiated `(GB)_{ki} G_{jl}`. -/
private lemma QSI_K.SB : ∑ i, ∑ j, a i * b j * QSI_r1b n N lam ζ a b i j ≤
    N ^ 2 * ((32 * D + 40) * (lam * ζ ^ 3 + ζ ^ 6)) := by
  have hζ := H.ζ0.le
  have hl := H.lam0
  have hn0 := QSI_K.n0 W H hsN hn hD hT hcq
  have hN := W.N0 hζ
  have e : ∀ i j, a i * b j * QSI_r1b n N lam ζ a b i j =
      lam * (a i * b j * (a j + a i + b j + b i)) + n⁻¹ * (a i * b j * (a j * b i + a i * b j)) +
        n⁻¹ * (2 * (N * ζ ^ 4)) * (a i * b j) := by
    intro i j; unfold QSI_r1b; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  have s3 := W.S3 hζ
  have s4 := W.S4 hζ
  have s0 := W.S0 hζ
  rw [QSI_K.sq W H hsN hn hD hT hcq] at s3
  have hNζ := QSI_K.Nζ W H hsN hn hD hT hcq
  have hsD := QSI_K.sD W H hsN hn hD hT hcq
  have t1 : lam * ∑ i, ∑ j, a i * b j * (a j + a i + b j + b i) ≤
      lam * (32 * (Real.sqrt D * N ^ 2 * ζ ^ 3)) := mul_le_mul_of_nonneg_left s3 hl
  have hNζ4 : N * ζ ^ 4 ≤ N ^ 2 * ζ ^ 6 := by
    have := mul_le_mul_of_nonneg_left hNζ (show 0 ≤ N * ζ ^ 4 by positivity)
    nlinarith
  have t2 : n⁻¹ * ∑ i, ∑ j, a i * b j * (a j * b i + a i * b j) ≤ 32 * (N ^ 2 * ζ ^ 6) := by
    have h1 : n⁻¹ * ∑ i, ∑ j, a i * b j * (a j * b i + a i * b j) ≤ n⁻¹ * (32 * (N ^ 2 * ζ ^ 4)) :=
      mul_le_mul_of_nonneg_left s4 (inv_nonneg.2 hn0.le)
    have h2 : n⁻¹ * (32 * (N ^ 2 * ζ ^ 4)) = 32 * (N * ζ ^ 4) / D := by rw [hn]; field_simp
    have h3 : 32 * (N * ζ ^ 4) / D ≤ 32 * (N * ζ ^ 4) := by
      apply div_le_self (by positivity) hD
    linarith
  have s0' : ∑ i, a i * ∑ j, b j ≤ 4 * (n * N * ζ ^ 2) := by
    simpa only [← Finset.mul_sum] using s0
  have t3 : n⁻¹ * (2 * (N * ζ ^ 4)) * ∑ i, a i * ∑ j, b j ≤ 8 * (N ^ 2 * ζ ^ 6) := by
    have h1 := mul_le_mul_of_nonneg_left s0' (show 0 ≤ n⁻¹ * (2 * (N * ζ ^ 4)) by positivity)
    have h2 : n⁻¹ * (2 * (N * ζ ^ 4)) * (4 * (n * N * ζ ^ 2)) = 8 * (N ^ 2 * ζ ^ 6) := by
      field_simp; ring
    linarith
  have t4 : lam * (32 * (Real.sqrt D * N ^ 2 * ζ ^ 3)) ≤ N ^ 2 * (32 * D * (lam * ζ ^ 3)) := by
    have : 0 ≤ lam * N ^ 2 * ζ ^ 3 := by positivity
    nlinarith
  have p1 : 0 ≤ N ^ 2 * (lam * ζ ^ 3) := by positivity
  have p2 : 0 ≤ N ^ 2 * (D * ζ ^ 6) := by have : 0 ≤ D := by linarith
                                          positivity
  have e2 : N ^ 2 * ((32 * D + 40) * (lam * ζ ^ 3 + ζ ^ 6)) = N ^ 2 * (32 * D * (lam * ζ ^ 3)) +
      40 * (N ^ 2 * (lam * ζ ^ 3)) + 32 * (N ^ 2 * (D * ζ ^ 6)) + 40 * (N ^ 2 * ζ ^ 6) := by ring
  rw [e2]
  linarith

/-- The Ward sum against `ρ₁` with the first derivative of `(GB)_{ki} G_{jl}`. -/
private lemma QSI_K.SC : ∑ i, ∑ j, (a j + a i) * (b j + b i) * QSI_r1b n N lam ζ a b i j ≤
    N ^ 2 * (96 * D * (Γ * lam * ζ ^ 2 + Γ * ζ ^ 5 + ζ ^ 6)) := by
  have hζ := H.ζ0.le
  have hl := H.lam0
  have hΓ := H.Γ0.le
  have hn0 := QSI_K.n0 W H hsN hn hD hT hcq
  have hN := W.N0 hζ
  have hNζ := QSI_K.Nζ W H hsN hn hD hT hcq
  have hsD := QSI_K.sD W H hsN hn hD hT hcq
  have e : ∀ i j, (a j + a i) * (b j + b i) * QSI_r1b n N lam ζ a b i j =
      lam * ((a j + a i) * (b j + b i) * (a j + a i + b j + b i)) +
        n⁻¹ * ((a j + a i) * (b j + b i) * (a j * b i + a i * b j)) +
        n⁻¹ * (2 * (N * ζ ^ 4)) * ((a j + a i) * (b j + b i)) := by
    intro i j; unfold QSI_r1b; ring
  have p1 : ∀ i j, (a j + a i) * (b j + b i) * (a j + a i + b j + b i) ≤
      6 * Γ * ((a j + a i) * (b j + b i)) := by
    intro i j
    have := W.aΓ i; have := W.aΓ j; have := W.bΓ i; have := W.bΓ j
    have h0 : 0 ≤ (a j + a i) * (b j + b i) := by
      have := W.a0 i; have := W.a0 j; have := W.b0 i; have := W.b0 j; positivity
    nlinarith
  have p2 : ∀ i j, (a j + a i) * (b j + b i) * (a j * b i + a i * b j) ≤
      2 * Γ * ((a j + a i) * (a j * b i + a i * b j)) := by
    intro i j
    have := W.bΓ i; have := W.bΓ j
    have h0 : 0 ≤ (a j + a i) * (a j * b i + a i * b j) := by
      have := W.a0 i; have := W.a0 j; have := W.b0 i; have := W.b0 j; positivity
    nlinarith
  have s1 := W.S1 hζ
  have s5 := W.S5 hζ
  rw [QSI_K.sq W H hsN hn hD hT hcq] at s5
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e i j]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have t1 : lam * ∑ i, ∑ j, (a j + a i) * (b j + b i) * (a j + a i + b j + b i) ≤
      lam * (6 * Γ * (16 * (n * N * ζ ^ 2))) := by
    apply mul_le_mul_of_nonneg_left _ hl
    calc ∑ i, ∑ j, (a j + a i) * (b j + b i) * (a j + a i + b j + b i) ≤
          ∑ i, ∑ j, 6 * Γ * ((a j + a i) * (b j + b i)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => p1 i j
      _ = 6 * Γ * ∑ i, ∑ j, (a j + a i) * (b j + b i) := by simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left s1 (by positivity)
  have t2 : n⁻¹ * ∑ i, ∑ j, (a j + a i) * (b j + b i) * (a j * b i + a i * b j) ≤
      64 * (N ^ 2 * (Γ * ζ ^ 5)) := by
    have u1 : ∑ i, ∑ j, (a j + a i) * (b j + b i) * (a j * b i + a i * b j) ≤
        2 * Γ * (32 * (Real.sqrt D * N ^ 2 * ζ ^ 3)) := by
      calc ∑ i, ∑ j, (a j + a i) * (b j + b i) * (a j * b i + a i * b j) ≤
            ∑ i, ∑ j, 2 * Γ * ((a j + a i) * (a j * b i + a i * b j)) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => p2 i j
        _ = 2 * Γ * ∑ i, ∑ j, (a j + a i) * (a j * b i + a i * b j) := by
            simp only [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left s5 (by positivity)
    have u2 := mul_le_mul_of_nonneg_left u1 (inv_nonneg.2 hn0.le)
    have u3 : n⁻¹ * (2 * Γ * (32 * (Real.sqrt D * N ^ 2 * ζ ^ 3))) =
        64 * (Γ * N * ζ ^ 3) * (Real.sqrt D / D) := by
      rw [hn]; field_simp; ring
    have u4 : Real.sqrt D / D ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hsD
    have u5 : Γ * N * ζ ^ 3 ≤ N ^ 2 * (Γ * ζ ^ 5) := by
      have := mul_le_mul_of_nonneg_left hNζ (show 0 ≤ Γ * N * ζ ^ 3 by positivity)
      nlinarith
    have u7 : 64 * (Γ * N * ζ ^ 3) * (Real.sqrt D / D) ≤ 64 * (Γ * N * ζ ^ 3) :=
      mul_le_of_le_one_right (by positivity) u4
    linarith
  have t3 : n⁻¹ * (2 * (N * ζ ^ 4)) * ∑ i, ∑ j, (a j + a i) * (b j + b i) ≤
      32 * (N ^ 2 * ζ ^ 6) := by
    have := mul_le_mul_of_nonneg_left s1 (show 0 ≤ n⁻¹ * (2 * (N * ζ ^ 4)) by positivity)
    have e2 : n⁻¹ * (2 * (N * ζ ^ 4)) * (16 * (n * N * ζ ^ 2)) = 32 * (N ^ 2 * ζ ^ 6) := by
      field_simp; ring
    linarith
  have e3 : lam * (6 * Γ * (16 * (n * N * ζ ^ 2))) = 96 * D * (N ^ 2 * (Γ * lam * ζ ^ 2)) := by
    rw [hn]; ring
  have q1 : 0 ≤ N ^ 2 * (Γ * ζ ^ 5) := by positivity
  have q2 : 0 ≤ N ^ 2 * ζ ^ 6 := by positivity
  have e4 : N ^ 2 * (96 * D * (Γ * lam * ζ ^ 2 + Γ * ζ ^ 5 + ζ ^ 6)) =
      96 * D * (N ^ 2 * (Γ * lam * ζ ^ 2)) + 96 * D * (N ^ 2 * (Γ * ζ ^ 5)) +
        96 * D * (N ^ 2 * ζ ^ 6) := by ring
  rw [e4]
  have q3 : 64 * (N ^ 2 * (Γ * ζ ^ 5)) ≤ 96 * D * (N ^ 2 * (Γ * ζ ^ 5)) := by nlinarith
  have q4 : 32 * (N ^ 2 * ζ ^ 6) ≤ 96 * D * (N ^ 2 * ζ ^ 6) := by nlinarith
  linarith

/-- The Ward sum against `ρ₂` with the undifferentiated `(GB)_{ki} G_{jl}`. -/
private lemma QSI_K.SD : ∑ i, ∑ j, a i * b j * QSI_r2b n N lam Γ T ζ a b i j ≤
    N ^ 2 * ((32 * D + 160) * ((Γ * lam + Γ * T) * ζ ^ 3 + Γ ^ 2 * ζ ^ 5 + Γ * ζ ^ 6)) := by
  have hζ := H.ζ0.le
  have hl := H.lam0
  have hΓ := H.Γ0.le
  have hT0 := QSI_K.T0 W H hsN hn hD hT hcq
  have hn0 := QSI_K.n0 W H hsN hn hD hT hcq
  have hN := W.N0 hζ
  have hNζ := QSI_K.Nζ W H hsN hn hD hT hcq
  have hsD := QSI_K.sD W H hsN hn hD hT hcq
  have e : ∀ i j, a i * b j * QSI_r2b n N lam Γ T ζ a b i j =
      (Γ * lam + Γ * T) * (a i * b j * (a j + a i + b j + b i)) +
        n⁻¹ * (2 * Γ) * (a i * b j * ((a j + a i) * (b j + b i))) +
        n⁻¹ * (8 * (Γ * (N * ζ ^ 4))) * (a i * b j) := by
    intro i j; unfold QSI_r2b; ring
  have p1 : ∀ i j, a i * b j * ((a j + a i) * (b j + b i)) ≤ 2 * Γ * (a i * b j * (a j + a i)) := by
    intro i j
    have := W.bΓ i; have := W.bΓ j
    have h0 : 0 ≤ a i * b j * (a j + a i) := by
      have := W.a0 i; have := W.a0 j; have := W.b0 i; have := W.b0 j; positivity
    nlinarith
  have s3 := W.S3 hζ
  have s3a := W.S3a hζ
  have s0 := W.S0 hζ
  rw [QSI_K.sq W H hsN hn hD hT hcq] at s3 s3a
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e i j]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have s0' : ∑ i, a i * ∑ j, b j ≤ 4 * (n * N * ζ ^ 2) := by
    simpa only [← Finset.mul_sum] using s0
  have t1 := mul_le_mul_of_nonneg_left s3 (show 0 ≤ Γ * lam + Γ * T by positivity)
  have t2 : n⁻¹ * (2 * Γ) * ∑ i, ∑ j, a i * b j * ((a j + a i) * (b j + b i)) ≤
      128 * (N ^ 2 * (Γ ^ 2 * ζ ^ 5)) := by
    have u1 : ∑ i, ∑ j, a i * b j * ((a j + a i) * (b j + b i)) ≤
        2 * Γ * (32 * (Real.sqrt D * N ^ 2 * ζ ^ 3)) := by
      calc _ ≤ ∑ i, ∑ j, 2 * Γ * (a i * b j * (a j + a i)) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => p1 i j
        _ = 2 * Γ * ∑ i, ∑ j, a i * b j * (a j + a i) := by simp only [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left s3a (by positivity)
    have u2 := mul_le_mul_of_nonneg_left u1 (show 0 ≤ n⁻¹ * (2 * Γ) by positivity)
    have u3 : n⁻¹ * (2 * Γ) * (2 * Γ * (32 * (Real.sqrt D * N ^ 2 * ζ ^ 3))) =
        128 * (Γ ^ 2 * N * ζ ^ 3) * (Real.sqrt D / D) := by
      rw [hn]; field_simp; ring
    have u4 : Real.sqrt D / D ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hsD
    have u5 : Γ ^ 2 * N * ζ ^ 3 ≤ N ^ 2 * (Γ ^ 2 * ζ ^ 5) := by
      have := mul_le_mul_of_nonneg_left hNζ (show 0 ≤ Γ ^ 2 * N * ζ ^ 3 by positivity)
      nlinarith
    have u7 : 128 * (Γ ^ 2 * N * ζ ^ 3) * (Real.sqrt D / D) ≤ 128 * (Γ ^ 2 * N * ζ ^ 3) :=
      mul_le_of_le_one_right (by positivity) u4
    linarith
  have t3 : n⁻¹ * (8 * (Γ * (N * ζ ^ 4))) * ∑ i, a i * ∑ j, b j ≤ 32 * (N ^ 2 * (Γ * ζ ^ 6)) := by
    have := mul_le_mul_of_nonneg_left s0' (show 0 ≤ n⁻¹ * (8 * (Γ * (N * ζ ^ 4))) by positivity)
    have e2 : n⁻¹ * (8 * (Γ * (N * ζ ^ 4))) * (4 * (n * N * ζ ^ 2)) = 32 * (N ^ 2 * (Γ * ζ ^ 6)) := by
      field_simp; ring
    linarith
  have t4 : (Γ * lam + Γ * T) * (32 * (Real.sqrt D * N ^ 2 * ζ ^ 3)) ≤
      32 * D * (N ^ 2 * ((Γ * lam + Γ * T) * ζ ^ 3)) := by
    have : 0 ≤ (Γ * lam + Γ * T) * N ^ 2 * ζ ^ 3 := by positivity
    nlinarith
  have e4 : N ^ 2 * ((32 * D + 160) * ((Γ * lam + Γ * T) * ζ ^ 3 + Γ ^ 2 * ζ ^ 5 + Γ * ζ ^ 6)) =
      32 * D * (N ^ 2 * ((Γ * lam + Γ * T) * ζ ^ 3)) + 160 * (N ^ 2 * ((Γ * lam + Γ * T) * ζ ^ 3)) +
      (32 * D + 160) * (N ^ 2 * (Γ ^ 2 * ζ ^ 5)) + (32 * D + 160) * (N ^ 2 * (Γ * ζ ^ 6)) := by ring
  rw [e4]
  have q0 : 0 ≤ N ^ 2 * ((Γ * lam + Γ * T) * ζ ^ 3) := by positivity
  have q1 : 0 ≤ N ^ 2 * (Γ ^ 2 * ζ ^ 5) := by positivity
  have q2 : 0 ≤ N ^ 2 * (Γ * ζ ^ 6) := by positivity
  have q3 : 128 * (N ^ 2 * (Γ ^ 2 * ζ ^ 5)) ≤ (32 * D + 160) * (N ^ 2 * (Γ ^ 2 * ζ ^ 5)) := by
    nlinarith
  have q4 : 32 * (N ^ 2 * (Γ * ζ ^ 6)) ≤ (32 * D + 160) * (N ^ 2 * (Γ * ζ ^ 6)) := by nlinarith
  linarith

end


section
variable {ι : Type*} [Fintype ι] {n N D ζ Γ s Z lam u T cq : ℝ} {a b : ι → ℝ}
  {A0 r1 r2 : ι → ι → ℝ} (W : QSI_WD n N ζ Γ a b A0) (H : QSI_Sc s ζ Γ Z lam u)
  (hsN : s ^ 2 * N = 1) (hn : n = D * N) (hD : 1 ≤ D) (hT : T = cq * (Z * Γ * ζ ^ 2))
  (hcq : 0 ≤ cq)
include W H hsN hn hD hT hcq

private lemma QSI_K.sumAbd (CA : ℕ → ℝ) (hCA : ∀ r, 0 ≤ CA r) (r : ℕ) :
    ∑ i, ∑ j, QSI_Abd CA A0 Γ a b r i j ≤ 32 * (CA r + 1) * Γ ^ r * (n * N * ζ ^ 2) := by
  have hζ := H.ζ0.le
  have hΓ := H.Γ0.le
  have hn0 := QSI_K.n0 W H hsN hn hD hT hcq
  have hN := W.N0 hζ
  have hc := hCA r
  have hb : 0 ≤ n * N * ζ ^ 2 := by positivity
  by_cases hr : r = 0
  · subst hr
    simp only [QSI_Abd, if_true, pow_zero, mul_one]
    have := W.S0 hζ
    calc ∑ i, ∑ j, A0 i j ≤ ∑ i, ∑ j, a i * b j :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => W.A0ab i j
      _ ≤ _ := by nlinarith
  · simp only [QSI_Abd, if_neg hr]
    have e : ∀ i j, CA r * Γ ^ r * ((a j + a i) * (2 * (b j + b i))) =
        2 * CA r * Γ ^ r * ((a j + a i) * (b j + b i)) := fun i j => by ring
    simp only [e, ← Finset.mul_sum]
    have := W.S1 hζ
    have h2 : 0 ≤ 2 * CA r * Γ ^ r := by positivity
    calc 2 * CA r * Γ ^ r * ∑ i, ∑ j, (a j + a i) * (b j + b i) ≤
          2 * CA r * Γ ^ r * (16 * (n * N * ζ ^ 2)) := mul_le_mul_of_nonneg_left this h2
      _ ≤ _ := by nlinarith [pow_nonneg hΓ r, mul_nonneg (pow_nonneg hΓ r) hb]

private lemma QSI_K.pref (kk : ℕ) (hk : 1 ≤ kk) :
    n⁻¹ * s ^ (kk + 1) * (n * N) = s ^ (kk - 1) := by
  have hn0 := QSI_K.n0 W H hsN hn hD hT hcq
  rw [show kk + 1 = (kk - 1) + 2 by omega, pow_add]
  field_simp
  linear_combination (s ^ (kk - 1)) * hsN

private lemma QSI_K.pref2 (kk : ℕ) (hk : 1 ≤ kk) :
    n⁻¹ * s ^ (kk + 1) * N ^ 2 = s ^ (kk - 1) / D := by
  have hn0 := QSI_K.n0 W H hsN hn hD hT hcq
  have hN := W.N0 H.ζ0.le
  have hD0 : 0 < D := by linarith
  rw [hn, show kk + 1 = (kk - 1) + 2 by omega, pow_add]
  field_simp
  linear_combination (s ^ (kk - 1)) * hsN

/-- The slot without derivatives on the `Q`-factors. -/
private lemma QSI_K.slot0 (CA : ℕ → ℝ) (hCA : ∀ r, 0 ≤ CA r) (kk : ℕ) (hkk : 2 ≤ kk) :
    n⁻¹ * s ^ (kk + 1) * ∑ i, ∑ j, QSI_Abd CA A0 Γ a b kk i j ≤ 32 * (CA kk + 1) * u := by
  have hn0 := QSI_K.n0 W H hsN hn hD hT hcq
  have h1 := QSI_K.sumAbd W H hsN hn hD hT hcq CA hCA kk
  have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ n⁻¹ * s ^ (kk + 1) by
    have := H.s0; positivity)
  have h3 := QSI_cmp_gen H kk 0 (by omega)
  have e : n⁻¹ * s ^ (kk + 1) * (32 * (CA kk + 1) * Γ ^ kk * (n * N * ζ ^ 2)) =
      32 * (CA kk + 1) * (s ^ (kk - 1) * Γ ^ kk * ζ ^ 2 * (Z * Γ * ζ ^ 2) ^ 0) := by
    rw [← QSI_K.pref W H hsN hn hD hT hcq kk (by omega)]; ring
  rw [e] at h2
  have := hCA kk
  calc _ ≤ _ := h2
    _ ≤ 32 * (CA kk + 1) * u ^ (0 + 1) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

omit W H hsN hn hD hT hcq in
private lemma QSI_kap2_U (m : ℕ) (hm : 1 ≤ m) (T r1 r2 : ℝ) :
    QSI_kap2 m m T r1 r2 = r1 * T ^ (m - 1) := by
  simp [QSI_kap2, show m ≠ 0 by omega]

omit W H hsN hn hD hT hcq in
private lemma QSI_kap2_V (m : ℕ) (hm : 2 ≤ m) (T r1 r2 : ℝ) :
    QSI_kap2 m (m - 1) T r1 r2 = (if m = 2 then r2 else r1 * T ^ (m - 2)) := by
  simp [QSI_kap2, show m - 1 ≠ 0 by omega, show ¬ (m - 1 + 2 ≤ m) by omega,
    show m - 1 + 1 = m by omega]

private lemma QSI_K.reduce (kk m : ℕ) (hk : 1 ≤ kk) (F g : ι → ι → ℝ) (c X : ℝ) (hc : 0 ≤ c)
    (hF : ∀ i j, Γ ^ m * F i j ≤ c * g i j) (hg : ∑ i, ∑ j, g i j ≤ N ^ 2 * X) :
    n⁻¹ * s ^ (kk + 1) * Γ ^ m * ∑ i, ∑ j, F i j ≤ s ^ (kk - 1) / D * (c * X) := by
  have hn0 := QSI_K.n0 W H hsN hn hD hT hcq
  have hp : 0 ≤ n⁻¹ * s ^ (kk + 1) := by have := H.s0; positivity
  calc n⁻¹ * s ^ (kk + 1) * Γ ^ m * ∑ i, ∑ j, F i j =
        n⁻¹ * s ^ (kk + 1) * ∑ i, ∑ j, Γ ^ m * F i j := by
        rw [mul_assoc, Finset.mul_sum]; simp only [Finset.mul_sum]
    _ ≤ n⁻¹ * s ^ (kk + 1) * ∑ i, ∑ j, c * g i j :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          hF i j) hp
    _ = n⁻¹ * s ^ (kk + 1) * (c * ∑ i, ∑ j, g i j) := by simp only [Finset.mul_sum]
    _ ≤ n⁻¹ * s ^ (kk + 1) * (c * (N ^ 2 * X)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hc) hp
    _ = (n⁻¹ * s ^ (kk + 1) * N ^ 2) * (c * X) := by ring
    _ = _ := by rw [QSI_K.pref2 W H hsN hn hD hT hcq kk hk]

private lemma QSI_K.Abd0 (CA : ℕ → ℝ) (hCA : ∀ r, 0 ≤ CA r) (r : ℕ) (i j : ι) :
    0 ≤ QSI_Abd CA A0 Γ a b r i j := by
  unfold QSI_Abd
  split_ifs
  · exact W.A00 i j
  · have := W.a0 i; have := W.a0 j; have := W.b0 i; have := W.b0 j; have := hCA r
    have := H.Γ0; positivity

private lemma QSI_K.cqpow (q kk : ℕ) (h : q ≤ kk) : cq ^ q ≤ (cq + 1) ^ kk :=
  (pow_le_pow_left₀ hcq (by linarith) q).trans (pow_le_pow_right₀ (by linarith) h)

set_option maxHeartbeats 1000000 in
/-- The slots with derivatives on the `Q`-factors. -/
private lemma QSI_K.slot (CA : ℕ → ℝ) (hCA : ∀ r, 0 ≤ CA r)
    (hr1 : ∀ i j, 0 ≤ r1 i j ∧ r1 i j ≤ T ∧ Γ * r1 i j ≤ QSI_r1b n N lam ζ a b i j)
    (hr2 : ∀ i j, 0 ≤ r2 i j ∧ r2 i j ≤ T ∧ Γ ^ 2 * r2 i j ≤ QSI_r2b n N lam Γ T ζ a b i j)
    (kk r m q : ℕ) (hkk : 2 ≤ kk) (hrm : r + m = kk) (hm : 1 ≤ m) :
    n⁻¹ * s ^ (kk + 1) * Γ ^ m *
      ∑ i, ∑ j, QSI_Abd CA A0 Γ a b r i j * QSI_kap2 m q T (r1 i j) (r2 i j) ≤
      1000 * (D + 1) * (CA r + CA 1 + 1) * (cq + 1) ^ kk * u ^ (q + 1) := by
  have hζ := H.ζ0.le
  have hΓ := H.Γ0.le
  have hl := H.lam0
  have hT0 := QSI_K.T0 W H hsN hn hD hT hcq
  have hn0 := QSI_K.n0 W H hsN hn hD hT hcq
  have hN := W.N0 hζ
  have hu := H.u0
  have hD0 : 0 < D := by linarith
  have hCr := hCA r
  have hC1 := hCA 1
  have hr10 : ∀ i j, 0 ≤ r1 i j := fun i j => (hr1 i j).1
  have hr20 : ∀ i j, 0 ≤ r2 i j := fun i j => (hr2 i j).1
  have hk0 : ∀ i j, 0 ≤ QSI_kap2 m q T (r1 i j) (r2 i j) := fun i j =>
    QSI_kap2_nonneg hT0 (hr10 i j) (hr20 i j) (hr1 i j).2.1 (hr2 i j).2.1 m q
  have hA0 := QSI_K.Abd0 W H hsN hn hD hT hcq CA hCA r
  have hRHS : 0 ≤ 1000 * (D + 1) * (CA r + CA 1 + 1) * (cq + 1) ^ kk * u ^ (q + 1) := by
    positivity
  have hp : 0 ≤ n⁻¹ * s ^ (kk + 1) * Γ ^ m := by have := H.s0; positivity
  by_cases hq0 : q ≤ m
  swap
  · -- empty slot
    have e : ∀ i j, QSI_kap2 m q T (r1 i j) (r2 i j) = 0 := fun i j => by
      simp [QSI_kap2, show q ≠ 0 by omega, show ¬ (q + 2 ≤ m) by omega,
        show q + 1 ≠ m by omega, show q ≠ m by omega]
    simp only [e, mul_zero, Finset.sum_const_zero]
    exact hRHS
  by_cases hg : q + 2 ≤ kk
  · -- generic slot
    have h1 : ∑ i, ∑ j, QSI_Abd CA A0 Γ a b r i j * QSI_kap2 m q T (r1 i j) (r2 i j) ≤
        T ^ q * (32 * (CA r + 1) * Γ ^ r * (n * N * ζ ^ 2)) := by
      calc _ ≤ ∑ i, ∑ j, QSI_Abd CA A0 Γ a b r i j * T ^ q :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (QSI_kap2_le hT0 (hr10 i j) (hr20 i j) (hr1 i j).2.1
                (hr2 i j).2.1 m q) (hA0 i j)
        _ = T ^ q * ∑ i, ∑ j, QSI_Abd CA A0 Γ a b r i j := by
            simp only [Finset.mul_sum, mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left (QSI_K.sumAbd W H hsN hn hD hT hcq CA hCA r)
            (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 hp
    have e : n⁻¹ * s ^ (kk + 1) * Γ ^ m * (T ^ q * (32 * (CA r + 1) * Γ ^ r * (n * N * ζ ^ 2))) =
        32 * (CA r + 1) * cq ^ q * (s ^ (kk - 1) * Γ ^ kk * ζ ^ 2 * (Z * Γ * ζ ^ 2) ^ q) := by
      rw [← QSI_K.pref W H hsN hn hD hT hcq kk (by omega), hT, ← hrm]; ring
    rw [e] at h2
    have h3 := QSI_cmp_gen H kk q hg
    have h4 := QSI_K.cqpow W H hsN hn hD hT hcq q kk (by omega)
    calc _ ≤ _ := h2
      _ ≤ 32 * (CA r + 1) * cq ^ q * u ^ (q + 1) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 1000 * (D + 1) * (CA r + CA 1 + 1) * (cq + 1) ^ kk * u ^ (q + 1) := by
          have : 32 * (CA r + 1) ≤ 1000 * (D + 1) * (CA r + CA 1 + 1) := by nlinarith
          have hu1 := pow_nonneg hu (q + 1)
          calc 32 * (CA r + 1) * cq ^ q * u ^ (q + 1) ≤
                1000 * (D + 1) * (CA r + CA 1 + 1) * (cq + 1) ^ kk * u ^ (q + 1) := by
                gcongr
            _ = _ := rfl
  have hD72 : (32 * D + 40) / D ≤ 72 := by
    rw [div_le_iff₀ hD0]; linarith
  have hD192 : (32 * D + 160) / D ≤ 192 := by
    rw [div_le_iff₀ hD0]; linarith
  have hsk : ∀ k, 0 ≤ s ^ k := fun k => pow_nonneg H.s0.le k
  have hgen : ∀ i j, 0 ≤ a i * b j := fun i j => mul_nonneg (W.a0 i) (W.b0 j)
  have hr1b : ∀ i j, 0 ≤ QSI_r1b n N lam ζ a b i j := fun i j =>
    le_trans (mul_nonneg hΓ (hr10 i j)) (hr1 i j).2.2
  have hr2b : ∀ i j, 0 ≤ QSI_r2b n N lam Γ T ζ a b i j := fun i j =>
    le_trans (mul_nonneg (pow_nonneg hΓ 2) (hr20 i j)) (hr2 i j).2.2
  have hSB := QSI_K.SB W H hsN hn hD hT hcq
  have hSC := QSI_K.SC W H hsN hn hD hT hcq
  have hSD := QSI_K.SD W H hsN hn hD hT hcq
  have hfin : ∀ (X c' : ℝ) (j : ℕ), j ≤ kk → 0 ≤ c' → c' ≤ 900 →
      X ≤ c' * (CA r + CA 1 + 1) * (cq + 1) ^ j * u ^ (q + 1) →
      X ≤ 1000 * (D + 1) * (CA r + CA 1 + 1) * (cq + 1) ^ kk * u ^ (q + 1) := by
    intro X c' j hj hc0 hc' hXc
    have h4 : (cq + 1) ^ j ≤ (cq + 1) ^ kk := pow_le_pow_right₀ (by linarith) hj
    have hu1 := pow_nonneg hu (q + 1)
    calc X ≤ c' * (CA r + CA 1 + 1) * (cq + 1) ^ j * u ^ (q + 1) := hXc
      _ ≤ 1000 * (D + 1) * (CA r + CA 1 + 1) * (cq + 1) ^ kk * u ^ (q + 1) := by
          have : c' ≤ 1000 * (D + 1) := by nlinarith
          gcongr
  have hcq1 : ∀ j, cq ^ j ≤ (cq + 1) ^ j := fun j => pow_le_pow_left₀ hcq (by linarith) j
  have hCA1 : 1 ≤ CA r + CA 1 + 1 := by linarith
  have hLHS0 : 0 ≤ n⁻¹ * s ^ (kk + 1) * Γ ^ m *
      ∑ i, ∑ j, QSI_Abd CA A0 Γ a b r i j * QSI_kap2 m q T (r1 i j) (r2 i j) :=
    mul_nonneg hp (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hA0 i j) (hk0 i j))
  by_cases hqk : q = kk
  · -- (B): all derivatives single, none on `(GB)_{ki} G_{jl}`
    have hr0 : r = 0 := by omega
    have hmk : m = kk := by omega
    subst hr0 hmk hqk
    simp only [QSI_kap2_U q (by omega), QSI_Abd, if_true]
    have h1 := QSI_K.reduce W H hsN hn hD hT hcq q q (by omega)
      (fun i j => A0 i j * (r1 i j * T ^ (q - 1))) (fun i j => a i * b j * QSI_r1b n N lam ζ a b i j)
      (Γ ^ (q - 1) * T ^ (q - 1)) _ (by positivity) (fun i j => by
        have e : Γ ^ q * (A0 i j * (r1 i j * T ^ (q - 1))) =
            Γ ^ (q - 1) * T ^ (q - 1) * (A0 i j * (Γ * r1 i j)) := by
          rw [show Γ ^ q = Γ ^ (q - 1) * Γ by rw [← pow_succ]; congr 1; omega]
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (W.A0ab i j) (hr1 i j).2.2
          (mul_nonneg hΓ (hr10 i j)) (hgen i j)) (by positivity)) hSB
    refine hfin _ (2 * 72) (q - 1) (by omega) (by norm_num) (by norm_num) (h1.trans ?_)
    have h2 := QSI_cmp_B H q (by omega)
    have e : s ^ (q - 1) / D * (Γ ^ (q - 1) * T ^ (q - 1) * ((32 * D + 40) *
        (lam * ζ ^ 3 + ζ ^ 6))) = (32 * D + 40) / D * cq ^ (q - 1) *
        (s ^ (q - 1) * Γ ^ (q - 1) * (Z * Γ * ζ ^ 2) ^ (q - 1) * (lam * ζ ^ 3 + ζ ^ 6)) := by
      rw [hT]; field_simp; ring
    rw [e]
    have hc0 : 0 ≤ (32 * D + 40) / D * cq ^ (q - 1) := by positivity
    have hu1 := pow_nonneg hu (q + 1)
    calc _ ≤ (32 * D + 40) / D * cq ^ (q - 1) * (2 * u ^ (q + 1)) :=
          mul_le_mul_of_nonneg_left h2 hc0
      _ ≤ 72 * (cq + 1) ^ (q - 1) * (2 * u ^ (q + 1)) := by gcongr; linarith
      _ = 2 * 72 * 1 * (cq + 1) ^ (q - 1) * u ^ (q + 1) := by ring
      _ ≤ 2 * 72 * (CA 0 + CA 1 + 1) * (cq + 1) ^ (q - 1) * u ^ (q + 1) := by gcongr
  have hqk1 : q + 1 = kk := by omega
  by_cases hr0 : r = 0
  · have hmk : m = kk := by omega
    subst hr0 hmk
    rw [← hqk1] at *
    have eV : ∀ i j, QSI_kap2 (q + 1) q T (r1 i j) (r2 i j) =
        (if q + 1 = 2 then r2 i j else r1 i j * T ^ (q + 1 - 2)) := fun i j => by
      have := QSI_kap2_V (q + 1) (by omega) T (r1 i j) (r2 i j)
      rwa [show q + 1 - 1 = q by omega] at this
    simp only [eV, QSI_Abd, if_true]
    by_cases hq1 : q = 1
    · -- (D): one double derivative, nothing else
      subst hq1
      simp only [if_true]
      have h1 := QSI_K.reduce W H hsN hn hD hT hcq 2 2 (by omega)
        (fun i j => A0 i j * r2 i j) (fun i j => a i * b j * QSI_r2b n N lam Γ T ζ a b i j) 1 _
        zero_le_one (fun i j => by
          rw [one_mul]
          calc Γ ^ 2 * (A0 i j * r2 i j) = A0 i j * (Γ ^ 2 * r2 i j) := by ring
            _ ≤ _ := mul_le_mul (W.A0ab i j) (hr2 i j).2.2
                (mul_nonneg (pow_nonneg hΓ 2) (hr20 i j)) (hgen i j)) hSD
      refine hfin _ (4 * 192) 1 (by omega) (by norm_num) (by norm_num) (h1.trans ?_)
      have h2 := QSI_cmp_D H
      have hTe : (Γ * lam + Γ * T) * ζ ^ 3 + Γ ^ 2 * ζ ^ 5 + Γ * ζ ^ 6 ≤
          (cq + 1) * (Γ * lam * ζ ^ 3 + Z * Γ ^ 2 * ζ ^ 5 + Γ ^ 2 * ζ ^ 5 + Γ * ζ ^ 6) := by
        rw [hT]
        have := H.Z0
        have a1 : 0 ≤ Γ * lam * ζ ^ 3 := by positivity
        have a2 : 0 ≤ Z * Γ ^ 2 * ζ ^ 5 := by positivity
        have a3 : 0 ≤ Γ ^ 2 * ζ ^ 5 := by positivity
        have a4 : 0 ≤ Γ * ζ ^ 6 := by positivity
        nlinarith
      have hs1 : (2 : ℕ) - 1 = 1 := rfl
      rw [hs1, pow_one]
      have hX0 : 0 ≤ Γ * lam * ζ ^ 3 + Z * Γ ^ 2 * ζ ^ 5 + Γ ^ 2 * ζ ^ 5 + Γ * ζ ^ 6 := by
        have := H.Z0; positivity
      calc s / D * (1 * ((32 * D + 160) * ((Γ * lam + Γ * T) * ζ ^ 3 + Γ ^ 2 * ζ ^ 5 +
            Γ * ζ ^ 6))) = (32 * D + 160) / D * (s * ((Γ * lam + Γ * T) * ζ ^ 3 + Γ ^ 2 * ζ ^ 5 +
            Γ * ζ ^ 6)) := by field_simp
        _ ≤ (32 * D + 160) / D * (s * ((cq + 1) * (Γ * lam * ζ ^ 3 + Z * Γ ^ 2 * ζ ^ 5 +
            Γ ^ 2 * ζ ^ 5 + Γ * ζ ^ 6))) := by
            gcongr; exact H.s0.le
        _ = (32 * D + 160) / D * (cq + 1) * (s * (Γ * lam * ζ ^ 3 + Z * Γ ^ 2 * ζ ^ 5 +
            Γ ^ 2 * ζ ^ 5 + Γ * ζ ^ 6)) := by ring
        _ ≤ (32 * D + 160) / D * (cq + 1) * (4 * u ^ 2) := by
            gcongr
        _ ≤ 192 * (cq + 1) * (4 * u ^ 2) := by gcongr
        _ = 4 * 192 * 1 * (cq + 1) ^ 1 * u ^ (1 + 1) := by ring
        _ ≤ 4 * 192 * (CA 0 + CA 1 + 1) * (cq + 1) ^ 1 * u ^ (1 + 1) := by
            have := pow_nonneg hu (1 + 1); gcongr
    · -- (B'): one double derivative and at least one single derivative
      simp only [show q + 1 ≠ 2 by omega, if_false]
      have h1 := QSI_K.reduce W H hsN hn hD hT hcq (q + 1) (q + 1) (by omega)
        (fun i j => A0 i j * (r1 i j * T ^ (q + 1 - 2)))
        (fun i j => a i * b j * QSI_r1b n N lam ζ a b i j)
        (Γ ^ q * T ^ (q + 1 - 2)) _ (by positivity) (fun i j => by
          have e : Γ ^ (q + 1) * (A0 i j * (r1 i j * T ^ (q + 1 - 2))) =
              Γ ^ q * T ^ (q + 1 - 2) * (A0 i j * (Γ * r1 i j)) := by
            rw [pow_succ]; ring
          rw [e]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (W.A0ab i j) (hr1 i j).2.2
            (mul_nonneg hΓ (hr10 i j)) (hgen i j)) (by positivity)) hSB
      refine hfin _ (2 * 72) (q + 1 - 2) (by omega) (by norm_num) (by norm_num)
        (h1.trans ?_)
      have h2 := QSI_cmp_B' H (q + 1) (by omega)
      rw [show q + 1 - 1 = q by omega] at h2 ⊢
      have e : s ^ q / D * (Γ ^ q * T ^ (q + 1 - 2) * ((32 * D + 40) *
          (lam * ζ ^ 3 + ζ ^ 6))) = (32 * D + 40) / D * cq ^ (q + 1 - 2) *
          (s ^ q * Γ ^ q * (Z * Γ * ζ ^ 2) ^ (q + 1 - 2) * (lam * ζ ^ 3 + ζ ^ 6)) := by
        rw [hT]; field_simp; ring
      rw [e]
      have hc0 : 0 ≤ (32 * D + 40) / D * cq ^ (q + 1 - 2) := by positivity
      have hu1 := pow_nonneg hu (q + 1)
      calc _ ≤ (32 * D + 40) / D * cq ^ (q + 1 - 2) * (2 * u ^ (q + 1)) :=
            mul_le_mul_of_nonneg_left h2 hc0
        _ ≤ 72 * (cq + 1) ^ (q + 1 - 2) * (2 * u ^ (q + 1)) := by gcongr; linarith
        _ = 2 * 72 * 1 * (cq + 1) ^ (q + 1 - 2) * u ^ (q + 1) := by ring
        _ ≤ 2 * 72 * (CA 0 + CA 1 + 1) * (cq + 1) ^ (q + 1 - 2) * u ^ (q + 1) := by gcongr
  · -- (C): one derivative on `(GB)_{ki} G_{jl}`, all others single
    have hr1' : r = 1 := by omega
    have hmq : m = q := by omega
    subst hr1'
    have hmq' : q = m := hmq.symm
    subst hmq'
    subst hqk1
    have eU : ∀ i j, QSI_kap2 q q T (r1 i j) (r2 i j) = r1 i j * T ^ (q - 1) := fun i j =>
      QSI_kap2_U q (by omega) _ _ _
    simp only [eU, QSI_Abd, if_neg one_ne_zero, pow_one]
    have h1 := QSI_K.reduce W H hsN hn hD hT hcq (q + 1) q (by omega)
      (fun i j => CA 1 * Γ * ((a j + a i) * (2 * (b j + b i))) * (r1 i j * T ^ (q - 1)))
      (fun i j => (a j + a i) * (b j + b i) * QSI_r1b n N lam ζ a b i j)
      (2 * CA 1 * Γ ^ q * T ^ (q - 1)) _ (by positivity) (fun i j => by
        have hab : 0 ≤ (a j + a i) * (b j + b i) := by
          have := W.a0 i; have := W.a0 j; have := W.b0 i; have := W.b0 j; positivity
        have e : Γ ^ q * (CA 1 * Γ * ((a j + a i) * (2 * (b j + b i))) * (r1 i j * T ^ (q - 1))) =
            2 * CA 1 * Γ ^ q * T ^ (q - 1) * ((a j + a i) * (b j + b i) * (Γ * r1 i j)) := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hr1 i j).2.2 hab)
          (by positivity)) hSC
    refine hfin _ (3 * 192) (q - 1) (by omega) (by norm_num) (by norm_num) (h1.trans ?_)
    have h2 := QSI_cmp_C H (q + 1) (by omega)
    rw [show q + 1 - 1 = q by omega, show q + 1 - 2 = q - 1 by omega] at h2
    rw [show q + 1 - 1 = q by omega]
    have e : s ^ q / D * (2 * CA 1 * Γ ^ q * T ^ (q - 1) * (96 * D * (Γ * lam * ζ ^ 2 +
        Γ * ζ ^ 5 + ζ ^ 6))) = 192 * CA 1 * cq ^ (q - 1) *
        (s ^ q * Γ ^ q * (Z * Γ * ζ ^ 2) ^ (q - 1) * (Γ * lam * ζ ^ 2 + Γ * ζ ^ 5 + ζ ^ 6)) := by
      rw [hT]; field_simp; ring
    rw [e]
    have hu1 := pow_nonneg hu (q + 1)
    calc _ ≤ 192 * CA 1 * cq ^ (q - 1) * (3 * u ^ (q + 1)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 192 * CA 1 * (cq + 1) ^ (q - 1) * (3 * u ^ (q + 1)) := by gcongr; linarith
      _ = 3 * 192 * CA 1 * (cq + 1) ^ (q - 1) * u ^ (q + 1) := by ring
      _ ≤ 3 * 192 * (CA 1 + CA 1 + 1) * (cq + 1) ^ (q - 1) * u ^ (q + 1) := by
          have : CA 1 ≤ CA 1 + CA 1 + 1 := by linarith
          gcongr

end


/-- `Q_{kl}` along the slice in the entry `(j, i)`. -/
private def QSI_X {D N : ℕ} (θ : ℝ) (h : Idx D N → Idx D N → ℂ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (k l i j : Idx D N) : ℂ → ℂ :=
  fun w => qMat D N θ (Matrix.of (setEntry h j i w)) Λ B z k l

/-- The factors `Q, …, Q, Q̄, …, Q̄` of `Q^{p-1} Q̄^p`. -/
private def QSI_phi (p : ℕ) (X : ℂ → ℂ) : ℕ → ℂ → ℂ :=
  fun s w => if s < p - 1 then X w else starRingEnd ℂ (X w)

/-- `Q^{p-1} Q̄^p` as a product of `2p - 1` factors. -/
private def QSI_Y (p : ℕ) (X : ℂ → ℂ) : ℂ → ℂ :=
  fun w => ∏ s ∈ Finset.range (2 * p - 1), QSI_phi p X s w

/-- `(G B)_{ki} G_{jl}` along the slice in the entry `(j, i)`. -/
private def QSI_A {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (k l i j : Idx D N) : ℂ → ℂ :=
  fun w => resFactorEval (Pi.single k 1, B *ᵥ Pi.single i 1, Λ, z) (setEntry h j i w) *
    resFactorEval (Pi.single j 1, Pi.single l 1, Λ, z) (setEntry h j i w)

/-- The jet bound of `Q^{p-1} Q̄^p`. -/
private def QSI_Ybd (M m : ℕ) (x T r1 r2 Γ : ℝ) : ℝ :=
  if m = 0 then x ^ M else QSI_Cst M m * Γ ^ m * QSI_Cl M m x T r1 r2

private lemma QSI_Y_eq (p : ℕ) (hp : 1 ≤ p) (X : ℂ → ℂ) (w : ℂ) :
    QSI_Y p X w = X w ^ (p - 1) * starRingEnd ℂ (X w) ^ p := by
  unfold QSI_Y QSI_phi
  have e : 2 * p - 1 = (p - 1) + p := by omega
  rw [e, Finset.prod_range_add]
  congr 1
  · rw [Finset.prod_congr rfl fun s hs => if_pos (Finset.mem_range.1 hs), Finset.prod_const,
      Finset.card_range]
  · rw [Finset.prod_congr rfl fun s _ => if_neg (by omega), Finset.prod_const, Finset.card_range]

private lemma QSI_Ybd_nonneg (M m : ℕ) {x T r1 r2 Γ : ℝ} (hx : 0 ≤ x) (hT : 0 ≤ T) (h1 : 0 ≤ r1)
    (h2 : 0 ≤ r2) (h1T : r1 ≤ T) (h2T : r2 ≤ T) (hΓ : 0 ≤ Γ) : 0 ≤ QSI_Ybd M m x T r1 r2 Γ := by
  unfold QSI_Ybd
  split_ifs
  · positivity
  · have := QSI_Cst_one_le M m
    have := QSI_Cl_nonneg hT h1 h2 h1T h2T hx M m
    positivity

/-- The jet of `A · Π φ_s` from the jets of `A` and of the factors. -/
private lemma QSI_Fjet_abs (A : ℂ → ℂ) (hA : QSI_Sm A) (φ : ℕ → ℂ → ℂ) (hφ : ∀ s, QSI_Sm (φ s)) (w : ℂ)
    (x T r1 r2 Γ : ℝ) (L : ℕ) (hx : 0 ≤ x) (hT : 0 ≤ T) (h1 : 0 ≤ r1) (h2 : 0 ≤ r2)
    (h1T : r1 ≤ T) (h2T : r2 ≤ T) (hΓ : 1 ≤ Γ) (h0 : ∀ s, ‖φ s w‖ ≤ x)
    (hg : ∀ s a b, 1 ≤ a + b → a + b ≤ L → ‖wirt a b (φ s) w‖ ≤ Γ ^ (a + b) * T)
    (h1' : ∀ s a b, a + b = 1 → ‖wirt a b (φ s) w‖ ≤ Γ * r1)
    (h2' : ∀ s a b, a + b = 2 → ‖wirt a b (φ s) w‖ ≤ Γ ^ 2 * r2)
    (Ab : ℕ → ℝ) (hAb0 : ∀ r, 0 ≤ Ab r) (hAb : ∀ a b, a + b ≤ L → ‖wirt a b A w‖ ≤ Ab (a + b))
    (M : ℕ) (hM : 1 ≤ M) (a b : ℕ) (hab : a + b ≤ L) :
    ‖wirt a b (fun w' => A w' * ∏ s ∈ Finset.range M, φ s w') w‖ ≤
      (((a + b : ℕ) : ℝ) + 1) ^ 2 * 2 ^ (a + b) *
        ∑ r ∈ Finset.range (a + b + 1), Ab r * QSI_Ybd M (a + b - r) x T r1 r2 Γ := by
  have hY := QSI_Yjet φ hφ w x T r1 r2 Γ L hx hT h1 h2 h1T h2T hΓ h0 hg h1' h2' M hM
  have hYs : QSI_Sm (fun w' => ∏ s ∈ Finset.range M, φ s w') := contDiff_prod fun s _ => hφ s
  have hYb0 : ∀ m, 0 ≤ QSI_Ybd M m x T r1 r2 Γ := fun m =>
    QSI_Ybd_nonneg M m hx hT h1 h2 h1T h2T (by linarith)
  set B := ∑ r ∈ Finset.range (a + b + 1), Ab r * QSI_Ybd M (a + b - r) x T r1 r2 Γ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun r _ => mul_nonneg (hAb0 r) (hYb0 _)
  have hL := QSI_wirt_mul_le hA hYs a b w B hB0 (by
    intro a1 a2 b1 b2 ha hb
    have y := hY a2 b2 (by omega)
    have hy : (if a2 + b2 = 0 then x ^ M else
        QSI_Cst M (a2 + b2) * Γ ^ (a2 + b2) * QSI_Cl M (a2 + b2) x T r1 r2) =
        QSI_Ybd M (a + b - (a1 + b1)) x T r1 r2 Γ := by
      rw [show a + b - (a1 + b1) = a2 + b2 by omega]; rfl
    rw [hy] at y
    have hr : a1 + b1 ∈ Finset.range (a + b + 1) := Finset.mem_range.2 (by omega)
    calc ‖wirt a1 b1 A w‖ * ‖wirt a2 b2 (fun w' => ∏ s ∈ Finset.range M, φ s w') w‖ ≤
          Ab (a1 + b1) * QSI_Ybd M (a + b - (a1 + b1)) x T r1 r2 Γ :=
          mul_le_mul (hAb a1 b1 (by omega)) y (norm_nonneg _) (hAb0 _)
      _ ≤ B := Finset.single_le_sum (f := fun r => Ab r * QSI_Ybd M (a + b - r) x T r1 r2 Γ)
          (fun r _ => mul_nonneg (hAb0 r) (hYb0 _)) hr)
  refine hL.trans (le_trans (QSI_count2 a b B hB0) (le_of_eq ?_))
  rfl

private lemma QSI_sum_shift (p : ℕ) (hp : 1 ≤ p) (x u : ℝ) :
    ∑ q ∈ Finset.range (2 * p - 1 + 1), x ^ (2 * p - 1 - q) * u ^ (q + 1) =
      ∑ n ∈ Finset.Icc 1 (2 * p), u ^ n * x ^ (2 * p - n) := by
  rw [show Finset.Icc 1 (2 * p) = Finset.Ico 1 (2 * p + 1) by
      ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range, show 2 * p + 1 - 1 = 2 * p - 1 + 1 by omega]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_range] at hq
  rw [mul_comm, show 2 * p - (1 + q) = 2 * p - 1 - q by omega, add_comm 1 q]

private lemma QSI_swap3 {ι : Type*} [Fintype ι] (R : Finset ℕ) (f : ℕ → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ q ∈ R, f q i j = ∑ q ∈ R, ∑ i, ∑ j, f q i j :=
  calc ∑ i, ∑ j, ∑ q ∈ R, f q i j = ∑ i, ∑ q ∈ R, ∑ j, f q i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ q ∈ R, ∑ i, ∑ j, f q i j := Finset.sum_comm

section
variable {ι : Type*} [Fintype ι] {n N D ζ Γ s Z lam u T cq : ℝ} {a b : ι → ℝ}
  {A0 r1 r2 : ι → ι → ℝ} (W : QSI_WD n N ζ Γ a b A0) (H : QSI_Sc s ζ Γ Z lam u)
  (hsN : s ^ 2 * N = 1) (hn : n = D * N) (hD : 1 ≤ D) (hT : T = cq * (Z * Γ * ζ ^ 2))
  (hcq : 0 ≤ cq)
include W H hsN hn hD hT hcq

/-- The total over the entries of the bound of order `kk`. -/
private lemma QSI_K.total (CA : ℕ → ℝ) (hCA : ∀ r, 0 ≤ CA r)
    (hr1 : ∀ i j, 0 ≤ r1 i j ∧ r1 i j ≤ T ∧ Γ * r1 i j ≤ QSI_r1b n N lam ζ a b i j)
    (hr2 : ∀ i j, 0 ≤ r2 i j ∧ r2 i j ≤ T ∧ Γ ^ 2 * r2 i j ≤ QSI_r2b n N lam Γ T ζ a b i j)
    (x : ℝ) (hx : 0 ≤ x) (M : ℕ) (kk : ℕ) (hkk : 2 ≤ kk) :
    n⁻¹ * s ^ (kk + 1) * ∑ i, ∑ j, ∑ r ∈ Finset.range (kk + 1),
        QSI_Abd CA A0 Γ a b r i j * QSI_Ybd M (kk - r) x T (r1 i j) (r2 i j) Γ ≤
      (∑ r ∈ Finset.range (kk + 1), (QSI_Cst M (kk - r) * (1000 * (D + 1) *
        (CA r + CA 1 + 1) * (cq + 1) ^ kk) + 32 * (CA kk + 1))) *
        ∑ q ∈ Finset.range (M + 1), x ^ (M - q) * u ^ (q + 1) := by
  have hn0 := QSI_K.n0 W H hsN hn hD hT hcq
  have hu := H.u0
  have hpre : 0 ≤ n⁻¹ * s ^ (kk + 1) := by have := H.s0; positivity
  set Sq := ∑ q ∈ Finset.range (M + 1), x ^ (M - q) * u ^ (q + 1) with hSq
  have hSq0 : 0 ≤ Sq := Finset.sum_nonneg fun q _ => by positivity
  rw [QSI_swap3 (Finset.range (kk + 1)) (fun r i j =>
    QSI_Abd CA A0 Γ a b r i j * QSI_Ybd M (kk - r) x T (r1 i j) (r2 i j) Γ)]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun r hr => ?_
  rw [Finset.mem_range] at hr
  have hCst := QSI_Cst_one_le M (kk - r)
  rw [add_mul]
  by_cases hrk : r = kk
  · subst hrk
    simp only [Nat.sub_self, QSI_Ybd, if_true]
    have h1 := QSI_K.slot0 W H hsN hn hD hT hcq CA hCA r hkk
    have h2 : ∑ i, ∑ j, QSI_Abd CA A0 Γ a b r i j * x ^ M =
        x ^ M * ∑ i, ∑ j, QSI_Abd CA A0 Γ a b r i j := by
      simp only [Finset.mul_sum, mul_comm]
    rw [h2]
    have h3 : x ^ M * u ≤ Sq := by
      have := Finset.single_le_sum (f := fun q => x ^ (M - q) * u ^ (q + 1))
        (fun q _ => by positivity) (Finset.mem_range.2 (Nat.succ_pos M))
      simpa using this
    have h4 : n⁻¹ * s ^ (r + 1) * (x ^ M * ∑ i, ∑ j, QSI_Abd CA A0 Γ a b r i j) ≤
        32 * (CA r + 1) * Sq := by
      calc _ = x ^ M * (n⁻¹ * s ^ (r + 1) * ∑ i, ∑ j, QSI_Abd CA A0 Γ a b r i j) := by ring
        _ ≤ x ^ M * (32 * (CA r + 1) * u) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 32 * (CA r + 1) * (x ^ M * u) := by ring
        _ ≤ 32 * (CA r + 1) * Sq := by have := hCA r; gcongr
    have h5 : 0 ≤ QSI_Cst M 0 * (1000 * (D + 1) * (CA r + CA 1 + 1) * (cq + 1) ^ r) * Sq := by
      have := hCA r; have := hCA 1; have : (0 : ℝ) ≤ D + 1 := by linarith
      have := QSI_Cst_one_le M 0
      have : (0 : ℝ) ≤ (cq + 1) ^ r := by positivity
      positivity
    linarith
  · have hm : 1 ≤ kk - r := by omega
    have e : ∀ i j, QSI_Abd CA A0 Γ a b r i j * QSI_Ybd M (kk - r) x T (r1 i j) (r2 i j) Γ =
        ∑ q ∈ Finset.range (M + 1), QSI_Cst M (kk - r) * (x ^ (M - q) *
          (Γ ^ (kk - r) * (QSI_Abd CA A0 Γ a b r i j * QSI_kap2 (kk - r) q T (r1 i j) (r2 i j)))) := by
      intro i j
      simp only [QSI_Ybd, if_neg (show kk - r ≠ 0 by omega), QSI_Cl, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    simp only [e]
    rw [QSI_swap3 (Finset.range (M + 1)) (fun q i j => QSI_Cst M (kk - r) * (x ^ (M - q) *
      (Γ ^ (kk - r) * (QSI_Abd CA A0 Γ a b r i j * QSI_kap2 (kk - r) q T (r1 i j) (r2 i j)))))]
    have hs := fun q => QSI_K.slot W H hsN hn hD hT hcq CA hCA hr1 hr2 kk r (kk - r) q hkk
      (by omega) hm
    set K1 := 1000 * (D + 1) * (CA r + CA 1 + 1) * (cq + 1) ^ kk with hK1
    have h1 : n⁻¹ * s ^ (kk + 1) * ∑ q ∈ Finset.range (M + 1), ∑ i, ∑ j,
        QSI_Cst M (kk - r) * (x ^ (M - q) * (Γ ^ (kk - r) *
          (QSI_Abd CA A0 Γ a b r i j * QSI_kap2 (kk - r) q T (r1 i j) (r2 i j)))) ≤
        QSI_Cst M (kk - r) * (K1 * Sq) := by
      rw [Finset.mul_sum, hSq, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun q _ => ?_
      have e2 : n⁻¹ * s ^ (kk + 1) * ∑ i, ∑ j, QSI_Cst M (kk - r) * (x ^ (M - q) *
          (Γ ^ (kk - r) * (QSI_Abd CA A0 Γ a b r i j * QSI_kap2 (kk - r) q T (r1 i j) (r2 i j)))) =
          QSI_Cst M (kk - r) * x ^ (M - q) * (n⁻¹ * s ^ (kk + 1) * Γ ^ (kk - r) *
            ∑ i, ∑ j, QSI_Abd CA A0 Γ a b r i j * QSI_kap2 (kk - r) q T (r1 i j) (r2 i j)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e2]
      calc _ ≤ QSI_Cst M (kk - r) * x ^ (M - q) * (K1 * u ^ (q + 1)) :=
            mul_le_mul_of_nonneg_left (hs q) (by positivity)
        _ = QSI_Cst M (kk - r) * (K1 * (x ^ (M - q) * u ^ (q + 1))) := by ring
    have h5 : 0 ≤ 32 * (CA kk + 1) * Sq := by have := hCA kk; positivity
    linarith

end


private lemma QSI_avgVecs_e {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (p : Idx D N) :
    (Pi.single p 1 : Idx D N → ℂ) ∈ avgVecs D N Λ B := by
  unfold avgVecs; simp

private lemma QSI_avgVecs_Be {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (p : Idx D N) :
    (B *ᵥ Pi.single p 1 : Idx D N → ℂ) ∈ avgVecs D N Λ B := by
  unfold avgVecs; simp

private lemma QSI_min_le {Γ T ρ v : ℝ} (hΓ : 0 < Γ) (h1 : v ≤ Γ * T) (h2 : v ≤ ρ) :
    v ≤ Γ * min T (ρ / Γ) := by
  rcases min_cases T (ρ / Γ) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · exact h1
  · rw [mul_div_cancel₀ _ hΓ.ne']; exact h2

/-- The point bound for one entry `(i, j)` of the expansion: the jet of `(GB)_{ki} G_{jl}
Q^{p-1} Q̄^p` along the slice in the entry `(j, i)`, at a point of the good event. -/
private lemma QSI_pt_ij {D N : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (hB : opNorm B ≤ 1) (z : ℂ) (hz : 0 < z.im) (Γ Υ lam : ℝ) (hΓ : 1 ≤ Γ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (hg : h ∈ avgGood D N θ Λ B z Γ Υ lam) (k l i j : Idx D N) (p L : ℕ) (hp : 1 ≤ p)
    (T : ℝ) (hT0 : 0 ≤ T)
    (hX : ∀ a b, 1 ≤ a + b → a + b ≤ L → ∀ y l', ‖wirt a b
      (fun w => qMat D N θ (Matrix.of (setEntry h j i w)) Λ B z y l') (h j i)‖ ≤ Γ ^ (a + b) * T)
    (CA : ℕ → ℝ) (hCA0 : ∀ r, 0 ≤ CA r)
    (hA : ∀ a b, 1 ≤ a + b → a + b ≤ L →
      ‖wirt a b (QSI_A h Λ B z k l i j) (h j i)‖ ≤ CA (a + b) * Γ ^ (a + b) *
        ((QSI_wa (res (Matrix.of h + Λ) z) B k j + QSI_wa (res (Matrix.of h + Λ) z) B k i) *
          (2 * (‖res (Matrix.of h + Λ) z j l‖ + ‖res (Matrix.of h + Λ) z i l‖))))
    (r1 r2 : ℝ) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (hr1T : r1 ≤ T) (hr2T : r2 ≤ T)
    (h1 : ∀ a b, a + b = 1 → ‖wirt a b (QSI_X θ h Λ B z k l i j) (h j i)‖ ≤ Γ * r1)
    (h2 : ∀ a b, a + b = 2 → ‖wirt a b (QSI_X θ h Λ B z k l i j) (h j i)‖ ≤ Γ ^ 2 * r2)
    (a b : ℕ) (hab : a + b ≤ L) :
    ‖wirt a b (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w) (h j i)‖ ≤
      (((a + b : ℕ) : ℝ) + 1) ^ 2 * 2 ^ (a + b) * ∑ r ∈ Finset.range (a + b + 1),
        QSI_Abd CA (fun i' j' => ‖(res (Matrix.of h + Λ) z * B) k i'‖ *
            ‖res (Matrix.of h + Λ) z j' l‖) Γ (QSI_wa (res (Matrix.of h + Λ) z) B k)
          (fun s' => ‖res (Matrix.of h + Λ) z s' l‖) r i j *
        QSI_Ybd (2 * p - 1) (a + b - r) ‖qMat D N θ (Matrix.of h) Λ B z k l‖ T r1 r2 Γ := by
  set G := res (Matrix.of h + Λ) z with hG
  set X := QSI_X θ h Λ B z k l i j with hXdef
  have hXs : QSI_Sm X := (QSI_MSm_Q θ h hh j i Λ B hΛ z hz) k l
  have hφs : ∀ s, QSI_Sm (QSI_phi p X s) := fun s => by
    unfold QSI_phi
    by_cases hs : s < p - 1
    · simp only [hs, if_true]; exact hXs
    · simp only [hs, if_false]; exact hXs.conj
  have hAs : QSI_Sm (QSI_A h Λ B z k l i j) :=
    (QSI_Sm_form h hh j i _ _ Λ hΛ z hz.ne').mul (QSI_Sm_form h hh j i _ _ Λ hΛ z hz.ne')
  have hself := QSI_setEntry_self h hh j i
  have hX0 : X (h j i) = qMat D N θ (Matrix.of h) Λ B z k l := by
    simp only [hXdef, QSI_X, hself]
  -- the jets of the factors `Q` and `Q̄`
  have hwX : ∀ a b, ‖wirt a b (QSI_phi p X 0) (h j i)‖ = ‖wirt a b X (h j i)‖ ∨
      ‖wirt a b (QSI_phi p X 0) (h j i)‖ = ‖wirt b a X (h j i)‖ := fun a b => by
    unfold QSI_phi
    by_cases hs : 0 < p - 1
    · left; simp only [hs, if_true]
    · right; simp only [hs, if_false]; rw [QSI_wirt_conj hXs a b, Complex.norm_conj]
  have hwφ : ∀ s a b, ‖wirt a b (QSI_phi p X s) (h j i)‖ = ‖wirt a b X (h j i)‖ ∨
      ‖wirt a b (QSI_phi p X s) (h j i)‖ = ‖wirt b a X (h j i)‖ := fun s a b => by
    unfold QSI_phi
    by_cases hs : s < p - 1
    · left; simp only [hs, if_true]
    · right; simp only [hs, if_false]; rw [QSI_wirt_conj hXs a b, Complex.norm_conj]
  have hYeq : (fun w => QSI_A h Λ B z k l i j w * QSI_Y p X w) =
      fun w => QSI_A h Λ B z k l i j w * ∏ s ∈ Finset.range (2 * p - 1), QSI_phi p X s w := rfl
  rw [hYeq]
  refine QSI_Fjet_abs (QSI_A h Λ B z k l i j) hAs (QSI_phi p X) hφs (h j i)
    ‖qMat D N θ (Matrix.of h) Λ B z k l‖ T r1 r2 Γ L (norm_nonneg _) hT0 hr1 hr2 hr1T hr2T hΓ
    ?_ ?_ ?_ ?_ _ ?_ ?_ (2 * p - 1) (by omega) a b hab
  · intro s
    have := hwφ s 0 0
    simp only [wirt, Function.iterate_zero, id] at this
    rcases this with e | e <;> rw [e, hX0]
  · intro s a' b' h1' h2'
    rcases hwφ s a' b' with e | e <;> rw [e]
    · exact hX a' b' h1' h2' k l
    · rw [add_comm a' b']; exact hX b' a' (by omega) (by omega) k l
  · intro s a' b' h1'
    rcases hwφ s a' b' with e | e <;> rw [e]
    · exact h1 a' b' h1'
    · exact h1 b' a' (by omega)
  · intro s a' b' h2'
    rcases hwφ s a' b' with e | e <;> rw [e]
    · exact h2 a' b' h2'
    · exact h2 b' a' (by omega)
  · intro r
    unfold QSI_Abd
    split_ifs
    · positivity
    · have := hCA0 r
      have := QSI_wa_nonneg G B k j; have := QSI_wa_nonneg G B k i
      have : 0 ≤ Γ := by linarith
      positivity
  · intro a' b' hab'
    by_cases h0 : a' + b' = 0
    · have ha : a' = 0 := by omega
      have hb : b' = 0 := by omega
      subst ha hb
      simp only [QSI_Abd, add_zero, if_true, wirt, Function.iterate_zero, id, QSI_A, hself,
        norm_mul, QSI_f_eM, QSI_f_ee]
      exact le_rfl
    · simp only [QSI_Abd, if_neg h0]
      exact hA a' b' (by omega) hab'

/-- The deterministic bound at a point of the good event on the terms of order `2 ≤ kk ≤ L` of the
expansion of `E |Q_{kl}|^{2p}`, summed over the entries. -/
private lemma QSI_point (D p L : ℕ) (hp : 1 ≤ p) (hL : 2 ≤ L) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (Γ Υ lam s ζ u : ℝ)
      (h : Idx D N → Idx D N → ℂ) (k l : Idx D N),
      0 ≤ θ → θ ≤ 1 → Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → opNorm B ≤ 1 → 0 < z.im → 1 ≤ Γ →
      z.im ≤ Υ → (Matrix.of h).IsHermitian → h ∈ avgGood D N θ Λ B z Γ Υ lam →
      QSI_Sc s ζ Γ (1 + ‖z‖) lam u → s ^ 2 * N = 1 → Υ / z.im = N * ζ ^ 2 →
      ∀ kk, 2 ≤ kk → kk ≤ L →
        ((D : ℝ) * N)⁻¹ * s ^ (kk + 1) * ∑ i, ∑ j, ∑ a ∈ Finset.range (kk + 1),
          ‖wirt a (kk - a) (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w)
            (h j i)‖ ≤
        K * ∑ n ∈ Finset.Icc 1 (2 * p), u ^ n * ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - n)
    := by
  choose cw hcw0 hcw using fun ab : ℕ × ℕ => qMat_wirt_le D ab.1 ab.2
  set cq := ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1), cw (a, b) with hcqdef
  have hcq0 : 0 ≤ cq := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hcw0 _
  have hcwle : ∀ a b, a ≤ L → b ≤ L → cw (a, b) ≤ cq := fun a b ha hb => by
    have h1 := Finset.single_le_sum (f := fun b => cw (a, b)) (fun b _ => hcw0 _)
      (Finset.mem_range.2 (by omega : b < L + 1))
    have h2 := Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range (L + 1), cw (a, b))
      (fun a _ => Finset.sum_nonneg fun b _ => hcw0 _) (Finset.mem_range.2 (by omega : a < L + 1))
    exact h1.trans h2
  choose CAf hCA0 hCAf using QSI_Ajet
  set M := 2 * p - 1 with hM
  set Kt : ℕ → ℝ := fun kk => ∑ r ∈ Finset.range (kk + 1), (QSI_Cst M (kk - r) *
    (1000 * (D + 1) * (CAf r + CAf 1 + 1) * (cq + 1) ^ kk) + 32 * (CAf kk + 1)) with hKt
  have hKt0 : ∀ kk, 0 ≤ Kt kk := fun kk => Finset.sum_nonneg fun r _ => by
    have := QSI_Cst_one_le M (kk - r); have := hCA0 r; have := hCA0 1; have := hCA0 kk
    positivity
  set Kk : ℕ → ℝ := fun kk => ((kk : ℝ) + 1) * (((kk : ℝ) + 1) ^ 2 * 2 ^ kk) * Kt kk with hKk
  have hKk0 : ∀ kk, 0 ≤ Kk kk := fun kk => by have := hKt0 kk; positivity
  refine ⟨∑ kk ∈ Finset.range (L + 1), Kk kk, Finset.sum_nonneg fun kk _ => hKk0 kk, ?_⟩
  intro N θ Λ B z Γ Υ lam s ζ u h k l hθ0 hθ1 hΛ hΛn hB hz hΓ hΥ hh hg H hsN hWd kk hkk hkL
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast k.1.pos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast k.2.pos
  have hΓ0 : 0 < Γ := by linarith
  have hζ := H.ζ0
  set G := res (Matrix.of h + Λ) z with hG
  set Q0 := qMat D N θ (Matrix.of h) Λ B z with hQ0
  set x := ‖Q0 k l‖ with hx
  set Z := 1 + ‖z‖ with hZ
  set T := cq * (Z * Γ * ζ ^ 2) with hT
  have hT0 : 0 ≤ T := by have := H.Z0; positivity
  have hP := QSI_Pt_of_good θ Λ B hΛ hB z hz h hh Γ Υ lam hg
  rw [hWd] at hP
  set wa := QSI_wa G B k with hwa
  set wb : Idx D N → ℝ := fun s' => ‖G s' l‖ with hwb
  set A0 : Idx D N → Idx D N → ℝ := fun i' j' => ‖(G * B) k i'‖ * ‖G j' l‖ with hA0
  set n : ℝ := (D : ℝ) * N with hn
  have hNζ4 : (N : ℝ)⁻¹ * (N * ζ ^ 2) * (N * ζ ^ 2) = N * ζ ^ 4 := by
    field_simp
  -- the Ward data
  have W : QSI_WD n N ζ Γ wa wb A0 := by
    refine ⟨by simp [Fintype.card_prod, hn], hN1, by nlinarith, fun s' => QSI_wa_nonneg G B k s',
      fun s' => norm_nonneg _, ?_, ?_, fun s' => ?_, fun s' => hP.g s' l,
      fun i' j' => by positivity, fun i' j' => ?_⟩
    · have e : (2 * Real.sqrt N * ζ) ^ 2 = 4 * (N * ζ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]; ring
      rw [e]
      have h1 : ∀ s', wa s' ^ 2 ≤ 2 * ‖G k s'‖ ^ 2 + 2 * ‖(G * B) k s'‖ ^ 2 := fun s' => by
        simp only [hwa, QSI_wa]; nlinarith [sq_nonneg (‖G k s'‖ - ‖(G * B) k s'‖)]
      calc ∑ s', wa s' ^ 2 ≤ ∑ s', (2 * ‖G k s'‖ ^ 2 + 2 * ‖(G * B) k s'‖ ^ 2) :=
            Finset.sum_le_sum fun s' _ => h1 s'
        _ = 2 * (∑ s', ‖G k s'‖ ^ 2) + 2 * ∑ s', ‖(G * B) k s'‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 2 * (N * ζ ^ 2) + 2 * (N * ζ ^ 2) := by
            gcongr
            · exact hP.row k
            · exact hP.rowB k
        _ = 4 * (N * ζ ^ 2) := by ring
    · have e : (2 * Real.sqrt N * ζ) ^ 2 = 4 * (N * ζ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]; ring
      rw [e]
      have := hP.col l
      have h0 : 0 ≤ N * ζ ^ 2 := by positivity
      simp only [hwb]
      linarith
    · simp only [hwa, QSI_wa]
      linarith [hP.g k s', hP.gb k s']
    · simp only [hA0, hwa, hwb, QSI_wa]
      have := norm_nonneg (G k i')
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hl0 := H.lam0
  have hn0 : 0 < n := by rw [hn]; positivity
  -- the refined scales
  set r1 : Idx D N → Idx D N → ℝ := fun i j => min T (QSI_r1b n N lam ζ wa wb i j / Γ) with hr1def
  set r2 : Idx D N → Idx D N → ℝ := fun i j => min T (QSI_r2b n N lam Γ T ζ wa wb i j / Γ ^ 2)
    with hr2def
  have hr1b0 : ∀ i j, 0 ≤ QSI_r1b n N lam ζ wa wb i j := fun i j => by
    unfold QSI_r1b
    have := W.a0 i; have := W.a0 j; have := W.b0 i; have := W.b0 j
    positivity
  have hr2b0 : ∀ i j, 0 ≤ QSI_r2b n N lam Γ T ζ wa wb i j := fun i j => by
    unfold QSI_r2b
    have := W.a0 i; have := W.a0 j; have := W.b0 i; have := W.b0 j
    positivity
  have hr1 : ∀ i j, 0 ≤ r1 i j ∧ r1 i j ≤ T ∧ Γ * r1 i j ≤ QSI_r1b n N lam ζ wa wb i j :=
    fun i j => ⟨le_min hT0 (div_nonneg (hr1b0 i j) hΓ0.le), min_le_left _ _, by
      calc Γ * r1 i j ≤ Γ * (QSI_r1b n N lam ζ wa wb i j / Γ) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hΓ0.le
        _ = _ := by field_simp⟩
  have hr2 : ∀ i j, 0 ≤ r2 i j ∧ r2 i j ≤ T ∧ Γ ^ 2 * r2 i j ≤ QSI_r2b n N lam Γ T ζ wa wb i j :=
    fun i j => ⟨le_min hT0 (div_nonneg (hr2b0 i j) (by positivity)), min_le_left _ _, by
      calc Γ ^ 2 * r2 i j ≤ Γ ^ 2 * (QSI_r2b n N lam Γ T ζ wa wb i j / Γ ^ 2) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
        _ = _ := by field_simp⟩
  -- the generic bounds on the derivatives of `Q`
  have hself := fun i j => QSI_setEntry_self h hh j i
  have hgood : ∀ i j, setEntry h j i (h j i) ∈ goodSet Λ z (avgVecs D N Λ B) Γ Υ := fun i j => by
    rw [hself i j]; exact hg.1
  have hζ2 : Υ / ((N : ℝ) * z.im) = ζ ^ 2 := by
    rw [show Υ / ((N : ℝ) * z.im) = Υ / z.im / N by rw [div_div, mul_comm], hWd]
    field_simp
  have hX : ∀ i j a b, 1 ≤ a + b → a + b ≤ L → ∀ y l', ‖wirt a b
      (fun w => qMat D N θ (Matrix.of (setEntry h j i w)) Λ B z y l') (h j i)‖ ≤
        Γ ^ (a + b) * T := by
    intro i j a b h1 h2 y l'
    have := hcw (a, b) N θ hθ0 hθ1 Λ hΛ hΛn B hB z hz h hh j i (h j i) y l' Γ Υ hΓ hΥ
      (hgood i j)
    rw [hζ2] at this
    refine this.trans ?_
    have hc := hcwle a b (by omega) (by omega)
    have e : Γ ^ (a + b) * T = cq * (1 + ‖z‖) * Γ ^ (a + b + 1) * ζ ^ 2 := by
      rw [hT, hZ, pow_succ]; ring
    rw [e]
    have := H.Z0
    gcongr
  -- the jets of `(GB)_{ki} G_{jl}`
  have hA : ∀ i j a b, 1 ≤ a + b → a + b ≤ L →
      ‖wirt a b (QSI_A h Λ B z k l i j) (h j i)‖ ≤ CAf (a + b) * Γ ^ (a + b) *
        ((QSI_wa G B k j + QSI_wa G B k i) * (2 * (‖G j l‖ + ‖G i l‖))) := by
    intro i j a b h1 h2
    have hV : ∀ x ∈ (avgVecs D N Λ B : Set (Idx D N → ℂ)), ∀ y ∈ (avgVecs D N Λ B : Set _),
        ‖resFactorEval (x, y, Λ, z) (setEntry h j i (h j i))‖ ≤ Γ := fun x hx y hy => by
      rw [hself i j]; exact (hg.1 x hx y hy).1
    have := hCAf (a + b) h hh j i Λ hΛ z hz.ne' (avgVecs D N Λ B : Set _)
      (QSI_avgVecs_e Λ B j) (QSI_avgVecs_e Λ B i) Γ hΓ (h j i) hV (Pi.single k 1)
      (B *ᵥ Pi.single i 1) (Pi.single j 1) (Pi.single l 1) (QSI_avgVecs_e Λ B k)
      (QSI_avgVecs_Be Λ B i) (QSI_avgVecs_e Λ B j) (QSI_avgVecs_e Λ B l) a b rfl
    refine this.trans ?_
    simp only [hself i j, QSI_f_ee, QSI_f_eM]
    have hR : ‖G k j‖ + ‖G k i‖ + ‖(G * B) k i‖ ≤ QSI_wa G B k j + QSI_wa G B k i := by
      unfold QSI_wa; linarith [norm_nonneg ((G * B) k j)]
    have hC : ‖G j l‖ + ‖G i l‖ + ‖G j l‖ ≤ 2 * (‖G j l‖ + ‖G i l‖) := by
      linarith [norm_nonneg (G i l)]
    have := hCA0 (a + b)
    have := QSI_wa_nonneg G B k j; have := QSI_wa_nonneg G B k i
    gcongr
  -- the refined bounds
  have h1 : ∀ i j a b, a + b = 1 → ‖wirt a b (QSI_X θ h Λ B z k l i j) (h j i)‖ ≤ Γ * r1 i j := by
    intro i j a b hab
    apply QSI_min_le hΓ0
    · have := hX i j a b (by omega) (by omega) k l
      rw [hab, pow_one] at this; exact this
    · have := QSI_rho1 θ hθ0 hθ1 h hh j i Λ B hΛ z hz hP a b hab k l
      rw [hNζ4] at this
      refine this.trans (le_of_eq ?_)
      simp only [QSI_r1b, hn, hwa, hwb, hG]
  have h2 : ∀ i j a b, a + b = 2 → ‖wirt a b (QSI_X θ h Λ B z k l i j) (h j i)‖ ≤
      Γ ^ 2 * r2 i j := by
    intro i j a b hab
    apply QSI_min_le (by positivity)
    · have := hX i j a b (by omega) (by omega) k l
      rw [hab] at this; exact this
    · have := QSI_rho2 θ hθ0 hθ1 h hh j i Λ B hΛ z hz hP (Γ * T) (fun a' b' hab' y l' => by
        have := hX i j a' b' (by omega) (by omega) y l'
        rw [hab', pow_one] at this; exact this) a b hab k l
      rw [hNζ4] at this
      refine this.trans (le_of_eq ?_)
      simp only [QSI_r2b, hn, hwa, hwb, hG]
  -- the bound for each entry
  have hij : ∀ i j a, a ∈ Finset.range (kk + 1) →
      ‖wirt a (kk - a) (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w)
        (h j i)‖ ≤ ((kk : ℝ) + 1) ^ 2 * 2 ^ kk * ∑ r ∈ Finset.range (kk + 1),
          QSI_Abd CAf A0 Γ wa wb r i j * QSI_Ybd M (kk - r) x T (r1 i j) (r2 i j) Γ := by
    intro i j a ha
    rw [Finset.mem_range] at ha
    have := QSI_pt_ij θ hθ0 hθ1 Λ B hΛ hB z hz Γ Υ lam hΓ h hh hg k l i j p L hp T hT0
      (hX i j) CAf hCA0 (hA i j) (r1 i j) (r2 i j) (hr1 i j).1 (hr2 i j).1 (hr1 i j).2.1
      (hr2 i j).2.1 (h1 i j) (h2 i j) a (kk - a) (by omega)
    rwa [show a + (kk - a) = kk by omega] at this
  have htot := QSI_K.total W H hsN hn hD1 hT hcq0 CAf hCA0 hr1 hr2 x (norm_nonneg _) M kk hkk
  rw [QSI_sum_shift p hp x u] at htot
  set Sq := ∑ n ∈ Finset.Icc 1 (2 * p), u ^ n * x ^ (2 * p - n) with hSq
  have hSq0 : 0 ≤ Sq := Finset.sum_nonneg fun n _ => by have := H.u0; positivity
  have hpre : 0 ≤ n⁻¹ * s ^ (kk + 1) := by have := H.s0; positivity
  calc ((D : ℝ) * N)⁻¹ * s ^ (kk + 1) * ∑ i, ∑ j, ∑ a ∈ Finset.range (kk + 1),
        ‖wirt a (kk - a) (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w)
          (h j i)‖ ≤ n⁻¹ * s ^ (kk + 1) * ∑ i, ∑ j, ∑ a ∈ Finset.range (kk + 1),
          ((kk : ℝ) + 1) ^ 2 * 2 ^ kk * ∑ r ∈ Finset.range (kk + 1),
            QSI_Abd CAf A0 Γ wa wb r i j * QSI_Ybd M (kk - r) x T (r1 i j) (r2 i j) Γ := by
        rw [← hn]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum
          fun j _ => Finset.sum_le_sum fun a ha => hij i j a ha) hpre
    _ = ((kk : ℝ) + 1) * (((kk : ℝ) + 1) ^ 2 * 2 ^ kk) * (n⁻¹ * s ^ (kk + 1) *
          ∑ i, ∑ j, ∑ r ∈ Finset.range (kk + 1),
            QSI_Abd CAf A0 Γ wa wb r i j * QSI_Ybd M (kk - r) x T (r1 i j) (r2 i j) Γ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        push_cast; ring
    _ ≤ ((kk : ℝ) + 1) * (((kk : ℝ) + 1) ^ 2 * 2 ^ kk) * (Kt kk * Sq) :=
        mul_le_mul_of_nonneg_left htot (by positivity)
    _ = Kk kk * Sq := by simp only [hKk]; ring
    _ ≤ (∑ kk ∈ Finset.range (L + 1), Kk kk) * Sq := by
        apply mul_le_mul_of_nonneg_right _ hSq0
        exact Finset.single_le_sum (f := Kk) (fun kk _ => hKk0 kk)
          (Finset.mem_range.2 (by omega))

private lemma QSI_Cl_one' (M : ℕ) (hM : 1 ≤ M) (x T r1 r2 : ℝ) :
    QSI_Cl M 1 x T r1 r2 = x ^ (M - 1) * r1 := by
  unfold QSI_Cl
  rw [Finset.sum_eq_single 1]
  · simp [QSI_kap2]
  · intro q _ hq
    have : QSI_kap2 1 q T r1 r2 = 0 := by
      unfold QSI_kap2
      by_cases h0 : q = 0
      · simp [h0]
      · simp [h0, show ¬ (q + 2 ≤ 1) by omega, show q + 1 ≠ 1 by omega, hq]
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- The deterministic bound at a point of the good event on the rest of the terms of order one
after the cancellation of (2.30) [eq:HGline] for `Q`, summed over the entries. -/
private lemma QSI_point1 (D p : ℕ) (hp : 1 ≤ p) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (Γ Υ lam s ζ u : ℝ)
      (h : Idx D N → Idx D N → ℂ) (k l : Idx D N),
      0 ≤ θ → θ ≤ 1 → Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → opNorm B ≤ 1 → 0 < z.im → 1 ≤ Γ →
      z.im ≤ Υ → (Matrix.of h).IsHermitian → h ∈ avgGood D N θ Λ B z Γ Υ lam →
      QSI_Sc s ζ Γ (1 + ‖z‖) lam u → s ^ 2 * N = 1 → Υ / z.im = N * ζ ^ 2 →
        ((D : ℝ) * N)⁻¹ * (N : ℝ)⁻¹ * ∑ i, ∑ j, ‖QSI_A h Λ B z k l i j (h j i)‖ *
          (‖wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ +
            ‖wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖) ≤
        K * u ^ 2 * ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - 2) := by
  choose cw hcw0 hcw using fun ab : ℕ × ℕ => qMat_wirt_le D ab.1 ab.2
  set cq := ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, cw (a, b) with hcqdef
  have hcq0 : 0 ≤ cq := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hcw0 _
  have hcwle : ∀ a b, a ≤ 2 → b ≤ 2 → cw (a, b) ≤ cq := fun a b ha hb => by
    have h1 := Finset.single_le_sum (f := fun b => cw (a, b)) (fun b _ => hcw0 _)
      (Finset.mem_range.2 (by omega : b < 3))
    have h2 := Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range 3, cw (a, b))
      (fun a _ => Finset.sum_nonneg fun b _ => hcw0 _) (Finset.mem_range.2 (by omega : a < 3))
    exact h1.trans h2
  set M := 2 * p - 1 with hM
  refine ⟨2 * QSI_Cst M 1 * (72 * 2), by have := QSI_Cst_one_le M 1; positivity, ?_⟩
  intro N θ Λ B z Γ Υ lam s ζ u h k l hθ0 hθ1 hΛ hΛn hB hz hΓ hΥ hh hg H hsN hWd
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast k.1.pos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast k.2.pos
  have hΓ0 : 0 < Γ := by linarith
  have hζ := H.ζ0
  set G := res (Matrix.of h + Λ) z with hG
  set Q0 := qMat D N θ (Matrix.of h) Λ B z with hQ0
  set x := ‖Q0 k l‖ with hx
  set Z := 1 + ‖z‖ with hZ
  set T := cq * (Z * Γ * ζ ^ 2) with hT
  have hT0 : 0 ≤ T := by have := H.Z0; positivity
  have hP := QSI_Pt_of_good θ Λ B hΛ hB z hz h hh Γ Υ lam hg
  rw [hWd] at hP
  set wa := QSI_wa G B k with hwa
  set wb : Idx D N → ℝ := fun s' => ‖G s' l‖ with hwb
  set A0 : Idx D N → Idx D N → ℝ := fun i' j' => ‖(G * B) k i'‖ * ‖G j' l‖ with hA0
  set n : ℝ := (D : ℝ) * N with hn
  have hNζ4 : (N : ℝ)⁻¹ * (N * ζ ^ 2) * (N * ζ ^ 2) = N * ζ ^ 4 := by
    field_simp
  have W : QSI_WD n N ζ Γ wa wb A0 := by
    refine ⟨by simp [Fintype.card_prod, hn], hN1, by nlinarith, fun s' => QSI_wa_nonneg G B k s',
      fun s' => norm_nonneg _, ?_, ?_, fun s' => ?_, fun s' => hP.g s' l,
      fun i' j' => by positivity, fun i' j' => ?_⟩
    · have e : (2 * Real.sqrt N * ζ) ^ 2 = 4 * (N * ζ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]; ring
      rw [e]
      have h1 : ∀ s', wa s' ^ 2 ≤ 2 * ‖G k s'‖ ^ 2 + 2 * ‖(G * B) k s'‖ ^ 2 := fun s' => by
        simp only [hwa, QSI_wa]; nlinarith [sq_nonneg (‖G k s'‖ - ‖(G * B) k s'‖)]
      calc ∑ s', wa s' ^ 2 ≤ ∑ s', (2 * ‖G k s'‖ ^ 2 + 2 * ‖(G * B) k s'‖ ^ 2) :=
            Finset.sum_le_sum fun s' _ => h1 s'
        _ = 2 * (∑ s', ‖G k s'‖ ^ 2) + 2 * ∑ s', ‖(G * B) k s'‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 2 * (N * ζ ^ 2) + 2 * (N * ζ ^ 2) := by
            gcongr
            · exact hP.row k
            · exact hP.rowB k
        _ = 4 * (N * ζ ^ 2) := by ring
    · have e : (2 * Real.sqrt N * ζ) ^ 2 = 4 * (N * ζ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]; ring
      rw [e]
      have := hP.col l
      have h0 : 0 ≤ N * ζ ^ 2 := by positivity
      simp only [hwb]
      linarith
    · simp only [hwa, QSI_wa]
      linarith [hP.g k s', hP.gb k s']
    · simp only [hA0, hwa, hwb, QSI_wa]
      have := norm_nonneg (G k i')
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hl0 := H.lam0
  have hn0 : 0 < n := by rw [hn]; positivity
  set r1 : Idx D N → Idx D N → ℝ := fun i j => min T (QSI_r1b n N lam ζ wa wb i j / Γ) with hr1def
  have hr1b0 : ∀ i j, 0 ≤ QSI_r1b n N lam ζ wa wb i j := fun i j => by
    unfold QSI_r1b
    have := W.a0 i; have := W.a0 j; have := W.b0 i; have := W.b0 j
    positivity
  have hr1 : ∀ i j, 0 ≤ r1 i j ∧ r1 i j ≤ T ∧ Γ * r1 i j ≤ QSI_r1b n N lam ζ wa wb i j :=
    fun i j => ⟨le_min hT0 (div_nonneg (hr1b0 i j) hΓ0.le), min_le_left _ _, by
      calc Γ * r1 i j ≤ Γ * (QSI_r1b n N lam ζ wa wb i j / Γ) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hΓ0.le
        _ = _ := by field_simp⟩
  have hself := fun i j => QSI_setEntry_self h hh j i
  have hgood : ∀ i j, setEntry h j i (h j i) ∈ goodSet Λ z (avgVecs D N Λ B) Γ Υ := fun i j => by
    rw [hself i j]; exact hg.1
  have hζ2 : Υ / ((N : ℝ) * z.im) = ζ ^ 2 := by
    rw [show Υ / ((N : ℝ) * z.im) = Υ / z.im / N by rw [div_div, mul_comm], hWd]
    field_simp
  have hX : ∀ i j a b, 1 ≤ a + b → a + b ≤ 2 → ∀ y l', ‖wirt a b
      (fun w => qMat D N θ (Matrix.of (setEntry h j i w)) Λ B z y l') (h j i)‖ ≤
        Γ ^ (a + b) * T := by
    intro i j a b h1 h2 y l'
    have := hcw (a, b) N θ hθ0 hθ1 Λ hΛ hΛn B hB z hz h hh j i (h j i) y l' Γ Υ hΓ hΥ
      (hgood i j)
    rw [hζ2] at this
    refine this.trans ?_
    have hc := hcwle a b (by omega) (by omega)
    have e : Γ ^ (a + b) * T = cq * (1 + ‖z‖) * Γ ^ (a + b + 1) * ζ ^ 2 := by
      rw [hT, hZ, pow_succ]; ring
    rw [e]
    have := H.Z0
    gcongr
  have h1 : ∀ i j a b, a + b = 1 → ‖wirt a b (QSI_X θ h Λ B z k l i j) (h j i)‖ ≤ Γ * r1 i j := by
    intro i j a b hab
    apply QSI_min_le hΓ0
    · have := hX i j a b (by omega) (by omega) k l
      rw [hab, pow_one] at this; exact this
    · have := QSI_rho1 θ hθ0 hθ1 h hh j i Λ B hΛ z hz hP a b hab k l
      rw [hNζ4] at this
      refine this.trans (le_of_eq ?_)
      simp only [QSI_r1b, hn, hwa, hwb, hG]
  -- the jet of `Q^{p-1} Q̄^p` at order one
  have hY : ∀ i j a b, a + b = 1 → ‖wirt a b (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ ≤
      QSI_Cst M 1 * Γ * (x ^ (M - 1) * r1 i j) := by
    intro i j a b hab
    set X := QSI_X θ h Λ B z k l i j with hXdef
    have hXs : QSI_Sm X := (QSI_MSm_Q θ h hh j i Λ B hΛ z hz) k l
    have hφs : ∀ s, QSI_Sm (QSI_phi p X s) := fun s => by
      unfold QSI_phi
      by_cases hs : s < p - 1
      · simp only [hs, if_true]; exact hXs
      · simp only [hs, if_false]; exact hXs.conj
    have hX0 : X (h j i) = Q0 k l := by simp only [hXdef, QSI_X, hself i j, hQ0]
    have hwφ : ∀ s a b, ‖wirt a b (QSI_phi p X s) (h j i)‖ = ‖wirt a b X (h j i)‖ ∨
        ‖wirt a b (QSI_phi p X s) (h j i)‖ = ‖wirt b a X (h j i)‖ := fun s a b => by
      unfold QSI_phi
      by_cases hs : s < p - 1
      · left; simp only [hs, if_true]
      · right; simp only [hs, if_false]; rw [QSI_wirt_conj hXs a b, Complex.norm_conj]
    have := QSI_Yjet (QSI_phi p X) hφs (h j i) x T (r1 i j) T Γ 2 (norm_nonneg _) hT0
      (hr1 i j).1 hT0 (hr1 i j).2.1 le_rfl hΓ
      (fun s => by
        have := hwφ s 0 0
        simp only [wirt, Function.iterate_zero, id] at this
        rcases this with e | e <;> rw [e, hX0])
      (fun s a' b' h1' h2' => by
        rcases hwφ s a' b' with e | e <;> rw [e]
        · exact hX i j a' b' h1' h2' k l
        · rw [add_comm a' b']; exact hX i j b' a' (by omega) (by omega) k l)
      (fun s a' b' h1' => by
        rcases hwφ s a' b' with e | e <;> rw [e]
        · exact h1 i j a' b' h1'
        · exact h1 i j b' a' (by omega))
      (fun s a' b' h2' => by
        rcases hwφ s a' b' with e | e <;> rw [e]
        · have := hX i j a' b' (by omega) (by omega) k l; rwa [h2'] at this
        · have := hX i j b' a' (by omega) (by omega) k l; rwa [show b' + a' = 2 by omega] at this)
      M (by omega) a b (by omega)
    rw [if_neg (by omega), hab, QSI_Cl_one' M (by omega), pow_one] at this
    exact this
  have hA : ∀ i j, ‖QSI_A h Λ B z k l i j (h j i)‖ = A0 i j := fun i j => by
    simp only [QSI_A, hself i j, norm_mul, QSI_f_eM, QSI_f_ee, hA0, hG]
  -- assemble
  have hSB := QSI_K.SB W H hsN hn hD1 hT hcq0
  have hC0 := QSI_Cst_one_le M 1
  have hxM : 0 ≤ x ^ (M - 1) := pow_nonneg (norm_nonneg _) _
  have hpt : ∀ i j, ‖QSI_A h Λ B z k l i j (h j i)‖ *
      (‖wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ +
        ‖wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖) ≤
      2 * QSI_Cst M 1 * x ^ (M - 1) * (wa i * wb j * QSI_r1b n N lam ζ wa wb i j) := by
    intro i j
    rw [hA i j]
    have y1 := hY i j 1 0 rfl
    have y2 := hY i j 0 1 rfl
    have hA00 := W.A00 i j
    have e1 : A0 i j * (QSI_Cst M 1 * Γ * (x ^ (M - 1) * r1 i j)) =
        QSI_Cst M 1 * x ^ (M - 1) * (A0 i j * (Γ * r1 i j)) := by ring
    have e2 : A0 i j * (Γ * r1 i j) ≤ wa i * wb j * QSI_r1b n N lam ζ wa wb i j :=
      mul_le_mul (W.A0ab i j) (hr1 i j).2.2 (mul_nonneg hΓ0.le (hr1 i j).1)
        (mul_nonneg (W.a0 i) (W.b0 j))
    calc A0 i j * (‖wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ +
          ‖wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖) ≤
          A0 i j * (QSI_Cst M 1 * Γ * (x ^ (M - 1) * r1 i j) +
            QSI_Cst M 1 * Γ * (x ^ (M - 1) * r1 i j)) := by gcongr
      _ = 2 * (QSI_Cst M 1 * x ^ (M - 1) * (A0 i j * (Γ * r1 i j))) := by ring
      _ ≤ 2 * (QSI_Cst M 1 * x ^ (M - 1) * (wa i * wb j * QSI_r1b n N lam ζ wa wb i j)) := by
          gcongr
      _ = _ := by ring
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpt i j
  have hcmp := QSI_cmp_one H
  have hpre : 0 ≤ ((D : ℝ) * N)⁻¹ * (N : ℝ)⁻¹ := by positivity
  calc _ ≤ ((D : ℝ) * N)⁻¹ * (N : ℝ)⁻¹ * ∑ i, ∑ j,
        2 * QSI_Cst M 1 * x ^ (M - 1) * (wa i * wb j * QSI_r1b n N lam ζ wa wb i j) :=
        mul_le_mul_of_nonneg_left hsum hpre
    _ = 2 * QSI_Cst M 1 * x ^ (M - 1) * (((D : ℝ) * N)⁻¹ * (N : ℝ)⁻¹ *
        ∑ i, ∑ j, wa i * wb j * QSI_r1b n N lam ζ wa wb i j) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 2 * QSI_Cst M 1 * x ^ (M - 1) * (((D : ℝ) * N)⁻¹ * (N : ℝ)⁻¹ *
        (N ^ 2 * ((32 * D + 40) * (lam * ζ ^ 3 + ζ ^ 6)))) := by gcongr
    _ = 2 * QSI_Cst M 1 * x ^ (M - 1) * ((32 * D + 40) / D * (lam * ζ ^ 3 + ζ ^ 6)) := by
        field_simp
    _ ≤ 2 * QSI_Cst M 1 * x ^ (M - 1) * (72 * (2 * u ^ 2)) := by
        have h72 : (32 * (D : ℝ) + 40) / D ≤ 72 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        have h0 : 0 ≤ lam * ζ ^ 3 + ζ ^ 6 := by positivity
        have h3 : (32 * (D : ℝ) + 40) / D * (lam * ζ ^ 3 + ζ ^ 6) ≤ 72 * (2 * u ^ 2) :=
          calc (32 * (D : ℝ) + 40) / D * (lam * ζ ^ 3 + ζ ^ 6) ≤ 72 * (lam * ζ ^ 3 + ζ ^ 6) := by
                gcongr
            _ ≤ 72 * (2 * u ^ 2) := by gcongr
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 * QSI_Cst M 1 * (72 * 2) * u ^ 2 * x ^ (2 * p - 2) := by
        rw [show M - 1 = 2 * p - 2 by omega]; ring


private lemma QSI_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
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

/-- Powers of a resolvent polynomial. -/
private def QSI_ppow {D N : ℕ} (P : ResPoly D N) : ℕ → ResPoly D N
  | 0 => [((1 : ℂ), [])]
  | n + 1 => resPolyMul (QSI_ppow P n) P

/-- The weight `Σ_t |c_t|` of a resolvent polynomial. -/
private def QSI_wt {D N : ℕ} (P : ResPoly D N) : ℝ := (P.map fun t => ‖t.1‖).sum

private lemma QSI_wt_nonneg {D N : ℕ} (P : ResPoly D N) : 0 ≤ QSI_wt P := by
  unfold QSI_wt
  induction P with
  | nil => simp
  | cons t P ih => simp only [List.map_cons, List.sum_cons]; positivity

private lemma QSI_eval_ppow {D N : ℕ} (P : ResPoly D N) (h : Idx D N → Idx D N → ℂ) (n : ℕ) :
    resPolyEval (QSI_ppow P n) h = resPolyEval P h ^ n := by
  induction n with
  | zero => simp [QSI_ppow, resPolyEval, resMonoEval]
  | succ n ih => rw [QSI_ppow, resPolyEval_mul, ih, pow_succ]

private lemma QSI_wt_map {D N : ℕ} (c : ℂ) (m : ResMono D N) (Q : ResPoly D N) :
    ((Q.map fun t => (c * t.1, m ++ t.2)).map fun t => ‖t.1‖).sum =
      ‖c‖ * (Q.map fun t => ‖t.1‖).sum := by
  induction Q with
  | nil => simp
  | cons t Q ih =>
    simp only [List.map_cons, List.sum_cons, norm_mul] at ih ⊢
    rw [ih]; ring

private lemma QSI_wt_mul {D N : ℕ} (P Q : ResPoly D N) :
    QSI_wt (resPolyMul P Q) = QSI_wt P * QSI_wt Q := by
  unfold QSI_wt resPolyMul
  induction P with
  | nil => simp
  | cons s P ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, ih, QSI_wt_map]
    ring

private lemma QSI_wt_star {D N : ℕ} (P : ResPoly D N) : QSI_wt (resPolyStar P) = QSI_wt P := by
  unfold QSI_wt resPolyStar
  simp only [List.map_map]
  congr 1
  exact List.map_congr_left fun t _ => by simp

private lemma QSI_wt_ppow {D N : ℕ} (P : ResPoly D N) (n : ℕ) :
    QSI_wt (QSI_ppow P n) = QSI_wt P ^ n := by
  induction n with
  | zero => simp [QSI_ppow, QSI_wt]
  | succ n ih => rw [QSI_ppow, QSI_wt_mul, ih, pow_succ]

/-- The vectors of a resolvent polynomial lie in `V`, the pairs are `(Λ, z)` or `(Λ, z̄)`, and
every term has at most `m` factors. -/
private def QSI_Good {D N : ℕ} (V : Set (Idx D N → ℂ)) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (m : ℕ) (P : ResPoly D N) : Prop :=
  ∀ t ∈ P, t.2.length ≤ m ∧ ∀ f ∈ t.2, f.1 ∈ V ∧ f.2.1 ∈ V ∧
    (f.2.2 = (Λ, z) ∨ f.2.2 = (Λ, starRingEnd ℂ z))

section
variable {D N : ℕ} {V : Set (Idx D N → ℂ)} {Λ : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}

private lemma QSI_Good.mul {m1 m2 : ℕ} {P Q : ResPoly D N} (hP : QSI_Good V Λ z m1 P)
    (hQ : QSI_Good V Λ z m2 Q) : QSI_Good V Λ z (m1 + m2) (resPolyMul P Q) := by
  intro t ht
  simp only [resPolyMul, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨s, hs, u, hu, rfl⟩ := ht
  refine ⟨by simp only [List.length_append]; have := (hP s hs).1; have := (hQ u hu).1; omega,
    fun f hf => ?_⟩
  rcases List.mem_append.1 hf with hf | hf
  · exact (hP s hs).2 f hf
  · exact (hQ u hu).2 f hf

private lemma QSI_Good.star {m : ℕ} {P : ResPoly D N} (hP : QSI_Good V Λ z m P) :
    QSI_Good V Λ z m (resPolyStar P) := by
  intro t ht
  simp only [resPolyStar, List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  refine ⟨by simpa using (hP s hs).1, fun f hf => ?_⟩
  simp only [List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  obtain ⟨h1, h2, h3⟩ := (hP s hs).2 g hg
  refine ⟨h2, h1, ?_⟩
  rcases h3 with h3 | h3
  · right; simp [h3]
  · left; simp [h3]

private lemma QSI_Good.ppow {m : ℕ} {P : ResPoly D N} (hP : QSI_Good V Λ z m P) (n : ℕ) :
    QSI_Good V Λ z (m * n) (QSI_ppow P n) := by
  induction n with
  | zero =>
    intro t ht
    simp only [QSI_ppow, List.mem_singleton] at ht
    subst ht
    exact ⟨by simp, fun f hf => by simp at hf⟩
  | succ n ih =>
    rw [QSI_ppow, show m * (n + 1) = m * n + m by ring]
    exact ih.mul hP

private lemma QSI_Good.mono {m m' : ℕ} {P : ResPoly D N} (hP : QSI_Good V Λ z m P) (h : m ≤ m') :
    QSI_Good V Λ z m' P := fun t ht => ⟨(hP t ht).1.trans h, (hP t ht).2⟩

private lemma QSI_Good.pair (hΛ : Λ.IsHermitian) (hz : z.im ≠ 0) {m : ℕ} {P : ResPoly D N}
    (hP : QSI_Good V Λ z m P) : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
  intro t ht f hf
  rcases ((hP t ht).2 f hf).2.2 with h | h <;> rw [h]
  · exact ⟨hΛ, hz⟩
  · exact ⟨hΛ, by simpa using hz⟩

end

/-- A resolvent polynomial of a member of the class is almost everywhere strongly measurable. -/
private lemma QSI_aesm {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) :
    AEStronglyMeasurable (fun h => resPolyEval P h) μ := by
  have hc : Continuous (fun h : Idx D N → Idx D N → ℂ => resPolyEval P (symArr h)) :=
    (contDiff_resPoly_symArr P hP 0).continuous
  refine hc.aestronglyMeasurable.congr ?_
  filter_upwards [hμ] with h hh
  rw [symArr_of_isHermitian h hh]

/-- The deterministic bound on the derivatives of a resolvent polynomial along a Hermitian slice:
the forms are at most `max 1 η⁻¹`. -/
private lemma QSI_wirt_det {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (V : Set (Idx D N → ℂ)) (hV : ∀ x ∈ V, ∑ r, ‖x r‖ ^ 2 ≤ 1)
    (m : ℕ) (P : ResPoly D N) (hP : QSI_Good V Λ z m P)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N)
    (hi : Pi.single i 1 ∈ V) (hj : Pi.single j 1 ∈ V) (w : ℂ) (a b : ℕ) :
    ‖wirt a b (fun w' => resPolyEval P (setEntry h i j w')) w‖ ≤
      ((m + a + b : ℕ) : ℝ) ^ (a + b) * QSI_wt P * (max 1 z.im⁻¹) ^ (m + a + b) := by
  have hX : (Matrix.of (setEntry h i j w) + Λ).IsHermitian := (QSI_slice_herm h hh i j w).add hΛ
  have hres : opNorm (res (Matrix.of (setEntry h i j w) + Λ) z) ≤ z.im⁻¹ :=
    opNorm_res_le _ hX z hz
  have hres' : opNorm (res (Matrix.of (setEntry h i j w) + Λ) (starRingEnd ℂ z)) ≤ z.im⁻¹ := by
    rw [res_conj _ hX z hz, QSI_opNorm_conjTranspose]; exact hres
  exact resPoly_wirt_le h hh i j V {(Λ, z), (Λ, starRingEnd ℂ z)} hi hj
    (by
      intro pr hpr
      rcases hpr with rfl | hpr
      · exact ⟨hΛ, hz.ne'⟩
      · rw [Set.mem_singleton_iff.mp hpr]; exact ⟨hΛ, by simpa using hz.ne'⟩)
    P m (fun t ht => ⟨(hP t ht).1, fun f hf => by
      obtain ⟨h1, h2, h3⟩ := (hP t ht).2 f hf
      refine ⟨h1, h2, ?_⟩
      rcases h3 with h3 | h3 <;> rw [h3] <;> simp⟩)
    (max 1 z.im⁻¹) (le_max_left _ _) w
    (by
      intro pr hpr x hx y hy
      have hx1 := hV x hx
      have hy1 := hV y hy
      rcases hpr with rfl | hpr
      · exact (QSI_form_le _ x y hx1 hy1).trans (hres.trans (le_max_right _ _))
      · rw [Set.mem_singleton_iff.mp hpr]
        exact (QSI_form_le _ x y hx1 hy1).trans (hres'.trans (le_max_right _ _)))
    a b


private lemma QSI_hyp_resMonoD {D N : ℕ} (Pr : Matrix (Idx D N) (Idx D N) ℂ × ℂ → Prop) (a b : Idx D N)
    (c : ℂ) (m : ResMono D N) (hm : ∀ f ∈ m, Pr f.2.2) :
    ∀ t ∈ resMonoD a b c m, ∀ f ∈ t.2, Pr f.2.2 := by
  induction m with
  | nil => simp [resMonoD]
  | cons f m ih =>
    intro t ht g hg
    simp only [resMonoD, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | ⟨s, hs, rfl⟩
    · simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact hm f List.mem_cons_self
      · exact hm f List.mem_cons_self
      · exact hm g (List.mem_cons_of_mem _ hg)
    · simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact hm _ List.mem_cons_self
      · exact ih (fun f' hf' => hm f' (List.mem_cons_of_mem _ hf')) s hs g hg

private lemma QSI_hyp_iter {D N : ℕ} (Pr : Matrix (Idx D N) (Idx D N) ℂ × ℂ → Prop) (a b : Idx D N)
    (c : ℂ) (P : ResPoly D N) (hP : ∀ t ∈ P, ∀ f ∈ t.2, Pr f.2.2) (n : ℕ) :
    ∀ t ∈ (resPolyD a b c)^[n] P, ∀ f ∈ t.2, Pr f.2.2 := by
  induction n with
  | zero => exact hP
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    intro t ht f hf
    simp only [resPolyD, List.mem_flatMap, List.mem_map] at ht
    obtain ⟨u, hu, s, hs, rfl⟩ := ht
    exact QSI_hyp_resMonoD Pr a b c u.2 (ih u hu) s hs f hf

/-- The derivatives along the slice in the entry `(j, i)`, evaluated at `w = h_{ji}`, of a
resolvent polynomial are almost everywhere strongly measurable in the array. -/
private lemma QSI_aesm_wirt {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0) (i j : Idx D N) (a b : ℕ) :
    AEStronglyMeasurable
      (fun h => wirt a b (fun w => resPolyEval P (setEntry h j i w)) (h j i)) μ := by
  set c : ℂ := if j = i then 1 / 2 else 1
  set P' := (resPolyD j i c)^[a] ((resPolyD i j c)^[b] P)
  have hP' : ∀ t ∈ P', ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 :=
    QSI_hyp_iter (fun pr => pr.1.IsHermitian ∧ pr.2.im ≠ 0) j i c _
      (QSI_hyp_iter (fun pr => pr.1.IsHermitian ∧ pr.2.im ≠ 0) i j c P hP b) a
  refine (QSI_aesm μ hμ P' hP').congr ?_
  filter_upwards [hμ] with h hh
  rw [resPoly_wirt h hh j i P hP a b]
  simp only [QSI_setEntry_self h hh j i]
  rfl

/-- `DN · Q_{kl} = Σ_{ij} (G B)_{ki} h_{ij} G_{jl} + (G B S_θ(G) G)_{kl} + Σ_a c_a(G) (G E_a G)_{kl}`
((2.30) [eq:HGline] for `Q`). -/
private lemma QSI_decomp {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (h : Idx D N → Idx D N → ℂ) (k l : Idx D N) :
    ((D : ℂ) * N) * qMat D N θ (Matrix.of h) Λ B z k l =
      (∑ i, ∑ j, (res (Matrix.of h + Λ) z * B) k i * h i j * res (Matrix.of h + Λ) z j l) +
        ((res (Matrix.of h + Λ) z * B * sTheta D N θ (res (Matrix.of h + Λ) z) *
            res (Matrix.of h + Λ) z) k l +
          (∑ a, QSI_cA D N θ B a (res (Matrix.of h + Λ) z) •
            (res (Matrix.of h + Λ) z * Ea D N a * res (Matrix.of h + Λ) z)) k l) := by
  have hD : ((D : ℂ) * N) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 k.1.pos.ne') (Nat.cast_ne_zero.2 k.2.pos.ne')
  set G := res (Matrix.of h + Λ) z with hG
  have e1 : (G * B * (Matrix.of h * G + sTheta D N θ G * G)) k l =
      (∑ i, ∑ j, (G * B) k i * h i j * G j l) + (G * B * sTheta D N θ G * G) k l := by
    rw [Matrix.mul_add, Matrix.add_apply, Matrix.mul_assoc (G * B) (sTheta D N θ G) G]
    congr 1
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]
  unfold qMat hgUnder
  rw [← hG]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
  rw [← mul_assoc, mul_inv_cancel₀ hD, one_mul, e1]
  simp only [QSI_cA, add_assoc]

private lemma QSI_kap_eq (D N : ℕ) (θ : ℝ) (r m : Idx D N) :
    QSI_kap D N θ r m = (varProf D N θ r m : ℂ) := by
  unfold QSI_kap varProf
  push_cast
  split_ifs <;> simp

/-- The cancellation of the terms of order one against `(G B S_θ(G) G)_{kl} + Σ_a c_a(G)
(G E_a G)_{kl}`: `Σ_{ij} s_{ji} (G_{kj} (GB)_{ii} G_{jl} + (GB)_{ki} G_{jj} G_{il})`. -/
private lemma QSI_cancel {D N : ℕ} (θ : ℝ) (B G : Matrix (Idx D N) (Idx D N) ℂ) (k l : Idx D N) :
    ∑ i, ∑ j, (varProf D N θ j i : ℂ) * (G k j * (G * B) i i * G j l + (G * B) k i * G j j * G i l) =
      (G * B * sTheta D N θ G * G) k l + (∑ a, QSI_cA D N θ B a G • (G * Ea D N a * G)) k l := by
  have p1 : (G * B * sTheta D N θ G * G) k l =
      ∑ i, ∑ j, (varProf D N θ j i : ℂ) * ((G * B) k i * G j j * G i l) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (G * B * sTheta D N θ G) k i = (G * B) k i * ∑ j, (varProf D N θ j i : ℂ) * G j j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [QSI_sTheta_apply, if_pos rfl]
        simp only [QSI_kap_eq]
      · intro b _ hb; rw [QSI_sTheta_apply, if_neg hb, mul_zero]
      · simp
    rw [e, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have p2 : (∑ a, QSI_cA D N θ B a G • (G * Ea D N a * G)) k l =
      ∑ i, ∑ j, (varProf D N θ j i : ℂ) * (G k j * (G * B) i i * G j l) := by
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, QSI_Ea_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_comm (f := fun i j => (varProf D N θ j i : ℂ) * (G k j * (G * B) i i * G j l))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j.1]
    · rw [if_pos rfl]
      unfold QSI_cA
      rw [Matrix.mul_assoc, QSI_trEa]
      simp only [Matrix.trace, Matrix.diag_apply, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold varProf
      by_cases hij : j.1 = i.1
      · rw [if_pos hij.symm, if_pos hij]; push_cast; ring
      · rw [if_neg (Ne.symm hij), if_neg hij]; push_cast; ring
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; simp
    · simp
  rw [p1, p2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma QSI_avgVecs_norm {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛn : opNorm Λ ≤ 1 / 10)
    (hB : opNorm B ≤ 1) : ∀ x ∈ avgVecs D N Λ B, ∑ r, ‖x r‖ ^ 2 ≤ 1 := by
  have he : ∀ p : Idx D N, ∑ r, ‖(Pi.single p (1 : ℂ) : Idx D N → ℂ) r‖ ^ 2 = 1 := fun p => by
    rw [Finset.sum_eq_single p]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hT : ∀ (T : Matrix (Idx D N) (Idx D N) ℂ), opNorm T ≤ 1 → ∀ p : Idx D N,
      ∑ r, ‖(T *ᵥ Pi.single p 1) r‖ ^ 2 ≤ 1 := fun T hT p => by
    refine (QSI_mulVec_sq T _).trans ?_
    rw [he p, mul_one]
    have := norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) T)
    have h0 : 0 ≤ opNorm T := this
    nlinarith
  intro x hx
  unfold avgVecs at hx
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with ((⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩
  · rw [he p]
  · exact hT B hB p
  · exact hT Bᴴ (by rw [QSI_opNorm_conjTranspose]; exact hB) p
  · exact hT Λ (hΛn.trans (by norm_num)) p

/-- The derivatives along the slice of a resolvent polynomial over `avgVecs` are integrable. -/
private lemma QSI_int_wirt {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (V : Set (Idx D N → ℂ))
    (hV : ∀ x ∈ V, ∑ r, ‖x r‖ ^ 2 ≤ 1) (m : ℕ) (P : ResPoly D N) (hP : QSI_Good V Λ z m P)
    (i j : Idx D N) (hi : Pi.single i 1 ∈ V) (hj : Pi.single j 1 ∈ V) (a b : ℕ) :
    Integrable (fun h => wirt a b (fun w => resPolyEval P (setEntry h j i w)) (h j i)) μ := by
  refine Integrable.of_bound (QSI_aesm_wirt μ hμ P (hP.pair hΛ hz.ne') i j a b)
    (((m + a + b : ℕ) : ℝ) ^ (a + b) * QSI_wt P * (max 1 z.im⁻¹) ^ (m + a + b)) ?_
  filter_upwards [hμ] with h hh
  exact QSI_wirt_det Λ hΛ z hz V hV m P hP h hh j i hj hi (h j i) a b

/-- The terms of order one of the expansion of `(GB)_{ki} G_{jl} f` in the entry `(j, i)`
combine into `-s_{ji} (G_{kj} (GB)_{ii} G_{jl} + (GB)_{ki} G_{jj} G_{il}) f`. -/
private lemma QSI_dA {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (k l i j : Idx D N) :
    (varProf D N θ j i : ℂ) * dW (QSI_A h Λ B z k l i j) (h j i) +
        (if j = i then (varProf D N θ j i : ℂ) else 0) * dWbar (QSI_A h Λ B z k l i j) (h j i) =
      -(varProf D N θ j i : ℂ) * (res (Matrix.of h + Λ) z k j *
        (res (Matrix.of h + Λ) z * B) i i * res (Matrix.of h + Λ) z j l +
        (res (Matrix.of h + Λ) z * B) k i * res (Matrix.of h + Λ) z j j *
          res (Matrix.of h + Λ) z i l) := by
  have s1 := QSI_Sm_form h hh j i (Pi.single k 1) (B *ᵥ Pi.single i 1) Λ hΛ z hz.ne'
  have s2 := QSI_Sm_form h hh j i (Pi.single j 1) (Pi.single l 1) Λ hΛ z hz.ne'
  obtain ⟨d1, d2⟩ := QSI_dW_mul s1 s2
  obtain ⟨f1, f2⟩ := QSI_dW_form h hh j i (Pi.single k 1) (B *ᵥ Pi.single i 1) Λ hΛ z hz.ne'
  obtain ⟨g1, g2⟩ := QSI_dW_form h hh j i (Pi.single j 1) (Pi.single l 1) Λ hΛ z hz.ne'
  have eA : QSI_A h Λ B z k l i j = fun w =>
      resFactorEval (Pi.single k 1, B *ᵥ Pi.single i 1, Λ, z) (setEntry h j i w) *
        resFactorEval (Pi.single j 1, Pi.single l 1, Λ, z) (setEntry h j i w) := rfl
  set G := res (Matrix.of h + Λ) z with hG
  set c : ℂ := if j = i then 1 / 2 else 1 with hc
  have hd1 : dW (QSI_A h Λ B z k l i j) (h j i) =
      -c * (G k j * (G * B) i i) * G j l + (G * B) k i * (-c * (G j j * G i l)) := by
    rw [eA, d1]
    beta_reduce
    rw [f1, g1]
    beta_reduce
    simp only [QSI_setEntry_self h hh j i, QSI_f_ee, QSI_f_eM, ← hG]
  have hd2 : dWbar (QSI_A h Λ B z k l i j) (h j i) =
      -c * (G k i * (G * B) j i) * G j l + (G * B) k i * (-c * (G j i * G j l)) := by
    rw [eA, d2]
    beta_reduce
    rw [f2, g2]
    beta_reduce
    simp only [QSI_setEntry_self h hh j i, QSI_f_ee, QSI_f_eM, ← hG]
  rw [hd1, hd2]
  by_cases hji : j = i
  · subst hji
    simp only [hc, if_pos rfl, if_true]
    ring
  · simp only [hc, if_neg hji]
    ring

/-- The terms of order at most one of the expansion. -/
private lemma QSI_split (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (f : ℕ → ℕ → ℂ) :
    ∑ a ∈ Finset.range (ℓ + 1), ∑ b ∈ Finset.range (ℓ + 1 - a), f a b =
      f 0 0 + f 1 0 + f 0 1 + ∑ a ∈ Finset.range (ℓ + 1), ∑ b ∈ Finset.range (ℓ + 1 - a),
        (if 2 ≤ a + b then f a b else 0) := by
  have e : ∀ a b, f a b = (if a + b ≤ 1 then f a b else 0) + (if 2 ≤ a + b then f a b else 0) :=
    fun a b => by split_ifs <;> first | omega | simp
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e a b]
  simp only [Finset.sum_add_distrib]
  congr 1
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have h2 : ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range (n + 1 + 1 - (a + 1 + 1)),
      (if a + 1 + 1 + b ≤ 1 then f (a + 1 + 1) b else 0) = 0 :=
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => if_neg (by omega)
  have h1 : ∑ b ∈ Finset.range (n + 1 + 1 - (0 + 1)), (if 0 + 1 + b ≤ 1 then f (0 + 1) b else 0) =
      f 1 0 := by
    rw [show n + 1 + 1 - (0 + 1) = n + 1 by omega, Finset.sum_range_succ']
    rw [Finset.sum_eq_zero fun b _ => if_neg (by omega)]
    simp
  have h0 : ∑ b ∈ Finset.range (n + 1 + 1 - 0), (if 0 + b ≤ 1 then f 0 b else 0) =
      f 0 0 + f 0 1 := by
    rw [show n + 1 + 1 - 0 = n + 2 by omega, Finset.sum_range_succ', Finset.sum_range_succ']
    rw [Finset.sum_eq_zero fun b _ => if_neg (by omega)]
    simp only [zero_add, Nat.zero_le, if_true, le_refl]
    ring
  rw [h2, h1, h0]
  ring


private lemma QSI_rp {N : ℝ} (hN : 1 ≤ N) (a b : ℝ) (h : a ≤ b) : N ^ a ≤ N ^ b :=
  Real.rpow_le_rpow_of_exponent_le hN h

private lemma QSI_npow {N : ℝ} (hN : 0 < N) (n : ℕ) (a : ℝ) : (N ^ a) ^ n = N ^ (a * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]

/-- The remainder of the one-entry expansion, summed over the entries: with `ℓ = 16p + 16`,
`m = 6p - 1`, `k = 160p + 120`, `M = (24Γ)⁻¹`. -/
private lemma QSI_exp_rem (p : ℕ) (hp : 1 ≤ p) (D : ℝ) (hD : 1 ≤ D) (N : ℝ) (hN : 1 ≤ N) (Γ Z η ε₀ wt : ℝ)
    (hΓ : 1 ≤ Γ) (hΓN : Γ ≤ N ^ ((1 : ℝ) / 6)) (hZ : 1 ≤ Z) (hZN : Z ≤ 2 * N ^ ((1 : ℝ) / 9))
    (hη : N⁻¹ ≤ η) (hε : 0 ≤ ε₀) (hwt0 : 0 ≤ wt) (hwt : wt ≤ (4 * Z) ^ (2 * p - 1)) :
    D * N * (wt * (N ^ (-(((16 * p + 16 : ℕ) : ℝ) + 2) / 2) * (6 * Γ) ^ (6 * p - 1 + (16 * p + 16) + 1) +
      (1 + η⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) *
        Real.sqrt (ε₀ + (N ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^ (-((160 * p + 120 : ℕ) : ℝ))))) ≤
      D * (8 ^ (2 * p - 1) * (6 ^ (22 * p + 16) + 2 ^ (22 * p + 16) * (1 + 24 ^ (80 * p + 60)))) *
        (N ^ (-(3 * (p : ℝ) + 1)) + N ^ (23 * (p : ℝ) + 18) * Real.sqrt ε₀) := by
  have hN0 : 0 < N := by linarith
  have hη0 : 0 < η := lt_of_lt_of_le (inv_pos.2 hN0) hη
  have hΓ0 : 0 < Γ := by linarith
  set E := 22 * p + 16 with hE
  have hE' : 6 * p - 1 + (16 * p + 16) + 1 = E := by omega
  rw [hE']
  have hEr : (E : ℝ) = 22 * p + 16 := by rw [hE]; push_cast; ring
  have hlr : -(((16 * p + 16 : ℕ) : ℝ) + 2) / 2 = -(8 * (p : ℝ) + 9) := by push_cast; ring
  rw [hlr]
  have hp1 : ((2 * p - 1 : ℕ) : ℝ) = 2 * p - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  set c := 80 * p + 60 with hc
  set kt := 160 * p + 120 with hkt
  have hktr : (kt : ℝ) = 160 * p + 120 := by rw [hkt]; push_cast; ring
  have hkc : 2 * c = kt := by omega
  clear_value E c kt
  -- the weight
  have hwN : wt ≤ 8 ^ (2 * p - 1) * N ^ (((2 * p - 1 : ℕ) : ℝ) / 9) := by
    refine hwt.trans ?_
    calc (4 * Z) ^ (2 * p - 1) ≤ (8 * N ^ ((1 : ℝ) / 9)) ^ (2 * p - 1) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = 8 ^ (2 * p - 1) * N ^ (((2 * p - 1 : ℕ) : ℝ) / 9) := by
          rw [mul_pow, QSI_npow hN0]; congr 2; ring
  -- the factor `(6Γ)^E`
  have h6 : (6 * Γ) ^ E ≤ 6 ^ E * N ^ ((E : ℝ) / 6) := by
    rw [mul_pow]
    gcongr
    calc Γ ^ E ≤ (N ^ ((1 : ℝ) / 6)) ^ E := pow_le_pow_left₀ hΓ0.le hΓN E
      _ = N ^ ((E : ℝ) / 6) := by rw [QSI_npow hN0]; ring_nf
  -- the factor `(1 + η⁻¹)^E`
  have h1η : (1 + η⁻¹) ^ E ≤ 2 ^ E * N ^ (E : ℝ) := by
    have : η⁻¹ ≤ N := by rw [inv_le_comm₀ hη0 hN0]; exact hη
    calc (1 + η⁻¹) ^ E ≤ (2 * N) ^ E := by gcongr; linarith
      _ = 2 ^ E * N ^ (E : ℝ) := by rw [mul_pow, Real.rpow_natCast]
  -- the truncation
  have htr : (N ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^ (-(kt : ℝ)) ≤
      24 ^ (2 * c) * N ^ (-((kt : ℝ) / 3)) := by
    have hb : 0 < N ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹ := by positivity
    rw [Real.rpow_neg hb.le, ← Real.inv_rpow hb.le, mul_inv, inv_inv]
    have e1 : ((N ^ ((1 : ℝ) / 2))⁻¹ * (24 * Γ)) ^ (kt : ℝ) =
        (N ^ ((1 : ℝ) / 2))⁻¹ ^ (kt : ℝ) * (24 * Γ) ^ (kt : ℝ) :=
      Real.mul_rpow (by positivity) (by positivity)
    rw [e1, Real.inv_rpow (by positivity), ← Real.rpow_mul hN0.le, Real.rpow_natCast]
    have e2 : (24 * Γ) ^ kt ≤ 24 ^ kt * N ^ ((kt : ℝ) / 6) := by
      rw [mul_pow]
      gcongr
      calc Γ ^ kt ≤ (N ^ ((1 : ℝ) / 6)) ^ kt := pow_le_pow_left₀ hΓ0.le hΓN kt
        _ = N ^ ((kt : ℝ) / 6) := by rw [QSI_npow hN0]; ring_nf
    calc (N ^ ((1 : ℝ) / 2 * kt))⁻¹ * (24 * Γ) ^ kt ≤
          (N ^ ((1 : ℝ) / 2 * kt))⁻¹ * (24 ^ kt * N ^ ((kt : ℝ) / 6)) := by gcongr
      _ = 24 ^ kt * (N ^ ((kt : ℝ) / 6) * N ^ (-((1 : ℝ) / 2 * kt))) := by
          rw [Real.rpow_neg hN0.le]; ring
      _ = 24 ^ (2 * c) * N ^ (-((kt : ℝ) / 3)) := by
          rw [← Real.rpow_add hN0, hkc]; congr 2; ring
  -- the square root
  have hsq : Real.sqrt (ε₀ + (N ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^ (-(kt : ℝ))) ≤
      Real.sqrt ε₀ + 24 ^ c * N ^ (-((kt : ℝ) / 6)) := by
    have htr0 : 0 ≤ (N ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^ (-(kt : ℝ)) := by positivity
    have hN2 : (N ^ (-((kt : ℝ) / 6))) ^ 2 = N ^ (-((kt : ℝ) / 3)) := by
      rw [QSI_npow hN0]; congr 1; push_cast; ring
    have hsq2 : (24 ^ c * N ^ (-((kt : ℝ) / 6))) ^ 2 = 24 ^ (2 * c) * N ^ (-((kt : ℝ) / 3)) := by
      rw [mul_pow, hN2, ← pow_mul, mul_comm c 2]
    have hb0 : 0 ≤ 24 ^ c * N ^ (-((kt : ℝ) / 6)) := by positivity
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.sq_sqrt hε
    have := Real.sqrt_nonneg ε₀
    nlinarith
  -- the exponents
  have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hne : (1 : ℝ) + ((2 * p - 1 : ℕ) : ℝ) / 9 ≠ 0 := ne_of_gt (by rw [hp1]; linarith)
  have x1 : N * N ^ (((2 * p - 1 : ℕ) : ℝ) / 9) * (N ^ (-(8 * (p : ℝ) + 9)) * N ^ ((E : ℝ) / 6)) ≤
      N ^ (-(3 * (p : ℝ) + 1)) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_one_add' hN0.le hne,
      ← Real.rpow_add hN0]
    apply QSI_rp hN
    rw [hp1, hEr]; linarith
  have x2 : N * N ^ (((2 * p - 1 : ℕ) : ℝ) / 9) * N ^ (E : ℝ) ≤ N ^ (23 * (p : ℝ) + 18) := by
    rw [← Real.rpow_one_add' hN0.le hne, ← Real.rpow_add hN0]
    apply QSI_rp hN
    rw [hp1, hEr]; linarith
  have x3 : N * N ^ (((2 * p - 1 : ℕ) : ℝ) / 9) * N ^ (E : ℝ) * N ^ (-((kt : ℝ) / 6)) ≤
      N ^ (-(3 * (p : ℝ) + 1)) := by
    rw [← Real.rpow_one_add' hN0.le hne, ← Real.rpow_add hN0,
      ← Real.rpow_add hN0]
    apply QSI_rp hN
    rw [hp1, hEr, hktr]; linarith
  set W8 := 8 ^ (2 * p - 1) * N ^ (((2 * p - 1 : ℕ) : ℝ) / 9) with hW8
  have step1 : D * N * (wt * (N ^ (-(8 * (p : ℝ) + 9)) * (6 * Γ) ^ E + (1 + η⁻¹) ^ E *
      Real.sqrt (ε₀ + (N ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^ (-(kt : ℝ))))) ≤
      D * N * (W8 * (N ^ (-(8 * (p : ℝ) + 9)) * (6 ^ E * N ^ ((E : ℝ) / 6)) +
        2 ^ E * N ^ (E : ℝ) * (Real.sqrt ε₀ + 24 ^ c * N ^ (-((kt : ℝ) / 6))))) := by
    gcongr
  refine step1.trans ?_
  set X1 := N * N ^ (((2 * p - 1 : ℕ) : ℝ) / 9) * (N ^ (-(8 * (p : ℝ) + 9)) * N ^ ((E : ℝ) / 6))
  set X2 := N * N ^ (((2 * p - 1 : ℕ) : ℝ) / 9) * N ^ (E : ℝ)
  set X3 := N * N ^ (((2 * p - 1 : ℕ) : ℝ) / 9) * N ^ (E : ℝ) * N ^ (-((kt : ℝ) / 6))
  have e : D * N * (W8 * (N ^ (-(8 * (p : ℝ) + 9)) * (6 ^ E * N ^ ((E : ℝ) / 6)) +
      2 ^ E * N ^ (E : ℝ) * (Real.sqrt ε₀ + 24 ^ c * N ^ (-((kt : ℝ) / 6))))) =
      D * 8 ^ (2 * p - 1) * (6 ^ E * X1 + 2 ^ E * X2 * Real.sqrt ε₀ + 2 ^ E * 24 ^ c * X3) := by
    simp only [hW8, X1, X2, X3]; ring
  rw [e]
  set Nm := N ^ (-(3 * (p : ℝ) + 1))
  set Np := N ^ (23 * (p : ℝ) + 18)
  have hs := Real.sqrt_nonneg ε₀
  have hNm : 0 ≤ Nm := by positivity
  have hNp : 0 ≤ Np := by positivity
  have hD8 : 0 ≤ D * 8 ^ (2 * p - 1) := by positivity
  have y1 : 6 ^ E * X1 ≤ 6 ^ E * Nm := mul_le_mul_of_nonneg_left x1 (by positivity)
  have y2 : 2 ^ E * X2 * Real.sqrt ε₀ ≤ 2 ^ E * Np * Real.sqrt ε₀ := by gcongr
  have y3 : 2 ^ E * 24 ^ c * X3 ≤ 2 ^ E * 24 ^ c * Nm := by gcongr
  have z1 : 6 ^ E * X1 + 2 ^ E * X2 * Real.sqrt ε₀ + 2 ^ E * 24 ^ c * X3 ≤
      (6 ^ E + 2 ^ E * (1 + 24 ^ c)) * (Nm + Np * Real.sqrt ε₀) := by
    have a1 : 0 ≤ 6 ^ E * (Np * Real.sqrt ε₀) := by positivity
    have a2 : 0 ≤ 2 ^ E * Nm := by positivity
    have a3 : 0 ≤ 2 ^ E * 24 ^ c * (Np * Real.sqrt ε₀) := by positivity
    have e2 : (6 ^ E + 2 ^ E * (1 + 24 ^ c)) * (Nm + Np * Real.sqrt ε₀) =
        6 ^ E * Nm + 2 ^ E * Np * Real.sqrt ε₀ + 2 ^ E * 24 ^ c * Nm +
          (6 ^ E * (Np * Real.sqrt ε₀) + 2 ^ E * Nm + 2 ^ E * 24 ^ c * (Np * Real.sqrt ε₀)) := by
      ring
    rw [e2]
    linarith
  calc D * 8 ^ (2 * p - 1) * (6 ^ E * X1 + 2 ^ E * X2 * Real.sqrt ε₀ + 2 ^ E * 24 ^ c * X3) ≤
        D * 8 ^ (2 * p - 1) * ((6 ^ E + 2 ^ E * (1 + 24 ^ c)) * (Nm + Np * Real.sqrt ε₀)) :=
        mul_le_mul_of_nonneg_left z1 hD8
    _ = _ := by ring



/-- The resolvent polynomial `(G B)_{ki} G_{jl}`. -/
private def QSI_PA {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l i j : Idx D N) :
    ResPoly D N :=
  [((1 : ℂ), [(Pi.single k 1, B *ᵥ Pi.single i 1, Λ, z), (Pi.single j 1, Pi.single l 1, Λ, z)])]

/-- The resolvent polynomial `P^{p-1} P̄^p`. -/
private def QSI_PY {D N : ℕ} (p : ℕ) (P : ResPoly D N) : ResPoly D N :=
  resPolyMul (QSI_ppow P (p - 1)) (QSI_ppow (resPolyStar P) p)

private lemma QSI_eval_PA {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l i j : Idx D N)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (QSI_PA Λ B z k l i j) h =
      resFactorEval (Pi.single k 1, B *ᵥ Pi.single i 1, Λ, z) h *
        resFactorEval (Pi.single j 1, Pi.single l 1, Λ, z) h := by
  simp [QSI_PA, resPolyEval, resMonoEval]

private lemma QSI_wt_PA {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l i j : Idx D N) :
    QSI_wt (QSI_PA Λ B z k l i j) = 1 := by
  simp [QSI_wt, QSI_PA]

private lemma QSI_Good_PA {D N : ℕ} (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l i j : Idx D N) :
    QSI_Good (↑(avgVecs D N Λ B)) Λ z 2 (QSI_PA Λ B z k l i j) := by
  intro t ht
  simp only [QSI_PA, List.mem_singleton] at ht
  subst ht
  refine ⟨by simp, fun f hf => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨Finset.mem_coe.2 (QSI_avgVecs_e Λ B k), Finset.mem_coe.2 (QSI_avgVecs_Be Λ B i),
      Or.inl rfl⟩
  · exact ⟨Finset.mem_coe.2 (QSI_avgVecs_e Λ B j), Finset.mem_coe.2 (QSI_avgVecs_e Λ B l),
      Or.inl rfl⟩

private lemma QSI_eval_PY {D N : ℕ} (p : ℕ) (P : ResPoly D N)
    (hP : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) :
    resPolyEval (QSI_PY p P) h =
      resPolyEval P h ^ (p - 1) * starRingEnd ℂ (resPolyEval P h) ^ p := by
  rw [QSI_PY, resPolyEval_mul, QSI_eval_ppow, QSI_eval_ppow, resPolyEval_star P hP h hh]

private lemma QSI_wt_PY {D N : ℕ} (p : ℕ) (hp : 1 ≤ p) (P : ResPoly D N) :
    QSI_wt (QSI_PY p P) = QSI_wt P ^ (2 * p - 1) := by
  rw [QSI_PY, QSI_wt_mul, QSI_wt_ppow, QSI_wt_ppow, QSI_wt_star, ← pow_add]
  congr 1
  omega

private lemma QSI_Good_PY {D N : ℕ} {V : Set (Idx D N → ℂ)} {Λ : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    (p : ℕ) (hp : 1 ≤ p) {P : ResPoly D N} (hP : QSI_Good V Λ z 3 P) :
    QSI_Good V Λ z (6 * p - 3) (QSI_PY p P) :=
  ((hP.ppow (p - 1)).mul (hP.star.ppow p)).mono (by omega)

/-- The polynomial `P` of an entry of `Q` from `qMat_resPoly`, in the form used below. -/
private structure QSI_QP {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l : Idx D N)
    (P : ResPoly D N) : Prop where
  good : QSI_Good (↑(avgVecs D N Λ B)) Λ z 3 P
  wt : QSI_wt P ≤ 4 * (1 + ‖z‖)
  eval : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
    resPolyEval P h = qMat D N θ (Matrix.of h) Λ B z k l

private lemma QSI_QP_exists {D N : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (B : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (k l : Idx D N) : ∃ P, QSI_QP θ Λ B z k l P := by
  obtain ⟨P, h1, h2, h3⟩ := qMat_resPoly D N θ hθ0 hθ1 Λ hΛ B z hz k l
  refine ⟨P, ⟨fun t ht => ⟨(h1 t ht).1, fun f hf => ?_⟩, h2, h3⟩⟩
  obtain ⟨a, b, c⟩ := (h1 t ht).2 f hf
  exact ⟨Finset.mem_coe.2 a, Finset.mem_coe.2 b, Or.inl c⟩

private lemma QSI_QP.herm {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ} {k l : Idx D N}
    {P : ResPoly D N} (hP : QSI_QP θ Λ B z k l P) (hΛ : Λ.IsHermitian) :
    ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian := fun t ht f hf => by
  rcases ((hP.good t ht).2 f hf).2.2 with e | e <;> rw [e] <;> exact hΛ

/-- `Q^{p-1} Q̄^p` along the slice is the polynomial `QSI_PY`. -/
private lemma QSI_slice_PY {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {k l : Idx D N} {P : ResPoly D N} (hP : QSI_QP θ Λ B z k l P) (hΛ : Λ.IsHermitian)
    (p : ℕ) (hp : 1 ≤ p) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) :
    (fun w => resPolyEval (QSI_PY p P) (setEntry h j i w)) =
      QSI_Y p (QSI_X θ h Λ B z k l i j) := by
  funext w
  have hs := QSI_slice_herm h hh j i w
  rw [QSI_eval_PY p P (hP.herm hΛ) _ hs, QSI_Y_eq p hp, hP.eval _ hs]
  rfl

/-- `(G B)_{ki} G_{jl} Q^{p-1} Q̄^p` along the slice is the polynomial `QSI_PA · QSI_PY`. -/
private lemma QSI_slice_PF {D N : ℕ} {θ : ℝ} {Λ B : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ}
    {k l : Idx D N} {P : ResPoly D N} (hP : QSI_QP θ Λ B z k l P) (hΛ : Λ.IsHermitian)
    (p : ℕ) (hp : 1 ≤ p) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) :
    (fun w => resPolyEval (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) (setEntry h j i w)) =
      fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w := by
  rw [← QSI_slice_PY hP hΛ p hp h hh i j]
  funext w
  rw [resPolyEval_mul, QSI_eval_PA]
  rfl

/-- The rest of the expansion after the cancellation: the order-one terms where the derivative
hits `Q^{p-1} Q̄^p`, and the terms of order `≥ 2`. -/
private def QSI_gp {D N : ℕ} (θ : ℝ) (h : Idx D N → Idx D N → ℂ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (z : ℂ) (k l : Idx D N) (p L : ℕ) (cc : Idx D N → Idx D N → ℕ → ℕ → ℂ) : ℂ :=
  (∑ i, ∑ j, QSI_A h Λ B z k l i j (h j i) *
      ((varProf D N θ j i : ℂ) * dW (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i) +
        (if j = i then (varProf D N θ j i : ℂ) else 0) *
          dWbar (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i))) +
    ∑ i, ∑ j, ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a),
      (if 2 ≤ a + b then cc j i a b * wirt a b
        (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w) (h j i) else 0)

/-- The pointwise identity behind the cancellation of the order-one terms. -/
private lemma QSI_pt_identity {D N : ℕ} (θ : ℝ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (p L : ℕ) (hp : 1 ≤ p) (hL : 1 ≤ L)
    (cc : Idx D N → Idx D N → ℕ → ℕ → ℂ) (h00 : ∀ i j, cc j i 0 0 = 0)
    (h10 : ∀ i j, cc j i 1 0 = varProf D N θ j i)
    (h01 : ∀ i j, cc j i 0 1 = if j = i then (varProf D N θ j i : ℂ) else 0)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (k l : Idx D N) :
    (∑ i, ∑ j, ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a),
        cc j i a b * wirt a b
          (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w) (h j i)) +
      ((res (Matrix.of h + Λ) z * B * sTheta D N θ (res (Matrix.of h + Λ) z) *
          res (Matrix.of h + Λ) z) k l +
        (∑ a, QSI_cA D N θ B a (res (Matrix.of h + Λ) z) •
          (res (Matrix.of h + Λ) z * Ea D N a * res (Matrix.of h + Λ) z)) k l) *
        (qMat D N θ (Matrix.of h) Λ B z k l ^ (p - 1) *
          starRingEnd ℂ (qMat D N θ (Matrix.of h) Λ B z k l) ^ p) =
    QSI_gp θ h Λ B z k l p L cc := by
  set G := res (Matrix.of h + Λ) z with hG
  set Y0 := qMat D N θ (Matrix.of h) Λ B z k l ^ (p - 1) *
    starRingEnd ℂ (qMat D N θ (Matrix.of h) Λ B z k l) ^ p with hY0
  have hcan := QSI_cancel θ B G k l
  have key : ∀ i j, ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a),
      cc j i a b * wirt a b
        (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w) (h j i) =
      -(varProf D N θ j i : ℂ) * (G k j * (G * B) i i * G j l + (G * B) k i * G j j * G i l) * Y0 +
        QSI_A h Λ B z k l i j (h j i) *
          ((varProf D N θ j i : ℂ) * dW (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i) +
            (if j = i then (varProf D N θ j i : ℂ) else 0) *
              dWbar (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)) +
        ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a),
          (if 2 ≤ a + b then cc j i a b * wirt a b
            (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w) (h j i)
            else 0) := by
    intro i j
    rw [QSI_split L hL]
    have hAs : QSI_Sm (QSI_A h Λ B z k l i j) :=
      (QSI_Sm_form h hh j i _ _ Λ hΛ z hz.ne').mul (QSI_Sm_form h hh j i _ _ Λ hΛ z hz.ne')
    have hXs : QSI_Sm (QSI_X θ h Λ B z k l i j) := (QSI_MSm_Q θ h hh j i Λ B hΛ z hz) k l
    have hYs : QSI_Sm (QSI_Y p (QSI_X θ h Λ B z k l i j)) := by
      unfold QSI_Y
      refine contDiff_prod fun s _ => ?_
      unfold QSI_phi
      by_cases hs : s < p - 1
      · simp only [hs, ite_true]; exact hXs
      · simp only [hs, ite_false]; exact hXs.conj
    have hF := QSI_dW_mul hAs hYs
    have e10 : wirt 1 0 (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w)
        (h j i) = dW (QSI_A h Λ B z k l i j) (h j i) * QSI_Y p (QSI_X θ h Λ B z k l i j) (h j i) +
          QSI_A h Λ B z k l i j (h j i) * dW (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i) := by
      show dW (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w) (h j i) = _
      rw [hF.1]
    have e01 : wirt 0 1 (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w)
        (h j i) = dWbar (QSI_A h Λ B z k l i j) (h j i) *
            QSI_Y p (QSI_X θ h Λ B z k l i j) (h j i) +
          QSI_A h Λ B z k l i j (h j i) * dWbar (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i) := by
      show dWbar (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w)
        (h j i) = _
      rw [hF.2]
    have hdA := QSI_dA θ Λ B hΛ z hz h hh k l i j
    have hYv : QSI_Y p (QSI_X θ h Λ B z k l i j) (h j i) = Y0 := by
      rw [QSI_Y_eq p hp]
      simp only [QSI_X, QSI_setEntry_self h hh j i, hY0]
    rw [h00, h10, h01, e10, e01, hYv]
    rw [← hG] at hdA
    linear_combination Y0 * hdA
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j]
  rw [← hcan]
  unfold QSI_gp
  simp only [Finset.sum_add_distrib, Finset.sum_mul]
  have hn : ∀ i j : Idx D N, -(varProf D N θ j i : ℂ) *
      (G k j * (G * B) i i * G j l + (G * B) k i * G j j * G i l) * Y0 =
      -((varProf D N θ j i : ℂ) * (G k j * (G * B) i i * G j l + (G * B) k i * G j j * G i l) *
        Y0) := fun i j => by ring
  simp only [hn, Finset.sum_neg_distrib]
  ring

private lemma QSI_varProf_le {D N : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (i j : Idx D N) :
    0 ≤ varProf D N θ i j ∧ varProf D N θ i j ≤ (N : ℝ)⁻¹ := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast i.1.pos
  have hN : (0 : ℝ) < N := by exact_mod_cast i.2.pos
  have h1 : ((D : ℝ) * N)⁻¹ ≤ (N : ℝ)⁻¹ := by
    rw [mul_inv]
    calc (D : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤ 1 * (N : ℝ)⁻¹ := by
          gcongr; exact inv_le_one_of_one_le₀ hD
      _ = _ := one_mul _
  have h2 : (0 : ℝ) ≤ ((D : ℝ) * N)⁻¹ := by positivity
  unfold varProf
  constructor
  · split_ifs <;> nlinarith [inv_pos.2 hN]
  · split_ifs <;> nlinarith [inv_pos.2 hN]

private lemma QSI_sum_tri_le (L : ℕ) (X : ℕ → ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hX : ∀ a b, a + b ≤ L → X a b ≤ c) :
    ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a), X a b ≤ ((L : ℝ) + 1) ^ 2 * c := by
  calc ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a), X a b ≤
        ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a), c :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hX a b (by
          have := Finset.mem_range.1 ha; have := Finset.mem_range.1 hb; omega)
    _ = ∑ a ∈ Finset.range (L + 1), ((L + 1 - a : ℕ) : ℝ) * c := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ Finset.range (L + 1), ((L : ℝ) + 1) * c :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (by
          have : ((L + 1 - a : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
          simpa using this) hc
    _ = ((L : ℝ) + 1) ^ 2 * c := by simp [Finset.sum_const]; ring

/-- The abstract bound on the rest `QSI_gp`. -/
private lemma QSI_gp_le {D N : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (h : Idx D N → Idx D N → ℂ)
    (Λ B : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (k l : Idx D N) (p L : ℕ)
    (cc : Idx D N → Idx D N → ℕ → ℕ → ℂ) (s Kc T1 T2 : ℝ) (hs : 0 ≤ s) (hKc : 0 ≤ Kc)
    (hT2 : 0 ≤ T2) (hcc : ∀ i j a b, a + b ≤ L → ‖cc j i a b‖ ≤ Kc * s ^ (a + b + 1))
    (h1 : (N : ℝ)⁻¹ * ∑ i, ∑ j, ‖QSI_A h Λ B z k l i j (h j i)‖ *
      (‖wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ +
        ‖wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖) ≤ T1)
    (h2 : ∀ kk, 2 ≤ kk → kk ≤ L → s ^ (kk + 1) * ∑ i, ∑ j, ∑ a ∈ Finset.range (kk + 1),
      ‖wirt a (kk - a) (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w)
        (h j i)‖ ≤ T2) :
    ‖QSI_gp θ h Λ B z k l p L cc‖ ≤ T1 + ((L : ℝ) + 1) ^ 2 * (Kc * T2) := by
  unfold QSI_gp
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine le_trans ?_ h1
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    obtain ⟨v0, v1⟩ := QSI_varProf_le θ hθ0 hθ1 j i
    have hc1 : ‖(varProf D N θ j i : ℂ)‖ ≤ (N : ℝ)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg v0]; exact v1
    have hc2 : ‖(if j = i then (varProf D N θ j i : ℂ) else 0)‖ ≤ (N : ℝ)⁻¹ := by
      split_ifs
      · exact hc1
      · simp
    rw [norm_mul]
    have e1 : dW (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i) =
        wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i) := rfl
    have e2 : dWbar (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i) =
        wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i) := rfl
    rw [e1, e2]
    have hn : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    calc ‖QSI_A h Λ B z k l i j (h j i)‖ *
          ‖(varProf D N θ j i : ℂ) * wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i) +
            (if j = i then (varProf D N θ j i : ℂ) else 0) *
              wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ ≤
        ‖QSI_A h Λ B z k l i j (h j i)‖ *
          ((N : ℝ)⁻¹ * ‖wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ +
            (N : ℝ)⁻¹ * ‖wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖) := by
          gcongr
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul] <;> gcongr
      _ = (N : ℝ)⁻¹ * (‖QSI_A h Λ B z k l i j (h j i)‖ *
          (‖wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ +
            ‖wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖)) := by ring
  · set F : Idx D N → Idx D N → ℂ → ℂ := fun i j w =>
      QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w with hF
    have hA : ‖∑ i, ∑ j, ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a),
        (if 2 ≤ a + b then cc j i a b * wirt a b (F i j) (h j i) else 0)‖ ≤
        ∑ i, ∑ j, ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a),
          ‖(if 2 ≤ a + b then cc j i a b * wirt a b (F i j) (h j i) else 0)‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      exact norm_sum_le _ _
    refine hA.trans ?_
    have swap : ∑ i, ∑ j, ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a),
        ‖(if 2 ≤ a + b then cc j i a b * wirt a b (F i j) (h j i) else 0)‖ =
        ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a), ∑ i, ∑ j,
          ‖(if 2 ≤ a + b then cc j i a b * wirt a b (F i j) (h j i) else 0)‖ := by
      have e1 : ∀ i : Idx D N, ∑ j, ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a),
          ‖(if 2 ≤ a + b then cc j i a b * wirt a b (F i j) (h j i) else 0)‖ =
          ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L + 1 - a), ∑ j,
            ‖(if 2 ≤ a + b then cc j i a b * wirt a b (F i j) (h j i) else 0)‖ := fun i => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
      rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    rw [swap]
    refine QSI_sum_tri_le L _ (Kc * T2) (mul_nonneg hKc hT2) fun a b hab => ?_
    by_cases h2ab : 2 ≤ a + b
    · simp only [h2ab, ite_true, norm_mul]
      have hs1 : ∀ i j, ‖cc j i a b‖ * ‖wirt a b (F i j) (h j i)‖ ≤
          Kc * (s ^ (a + b + 1) * ‖wirt a b (F i j) (h j i)‖) := fun i j => by
        rw [← mul_assoc]; gcongr; exact hcc i j a b hab
      refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hs1 i j).trans ?_
      rw [show (∑ i, ∑ j, Kc * (s ^ (a + b + 1) * ‖wirt a b (F i j) (h j i)‖)) =
          Kc * (s ^ (a + b + 1) * ∑ i, ∑ j, ‖wirt a b (F i j) (h j i)‖) by
        simp only [Finset.mul_sum]]
      gcongr
      refine le_trans ?_ (h2 (a + b) h2ab hab)
      gcongr with i _ j _
      have hb : b = a + b - a := by omega
      have := Finset.single_le_sum (f := fun a' => ‖wirt a' (a + b - a') (F i j) (h j i)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega : a < a + b + 1))
      rw [← hb] at this
      exact this
    · simp only [h2ab, ite_false, norm_zero, Finset.sum_const_zero]
      exact mul_nonneg hKc hT2


private lemma QSI_ccum01 {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) (i j : Idx D N) : ccum (μ.map fun h => h i j) 0 1 = 0 := by
  have hprob := hμ.prob
  have hmeas : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hint : ∀ q : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ q) (μ.map fun h => h i j) := fun q =>
    (integrable_map_measure (continuous_norm.pow q).aestronglyMeasurable hmeas.aemeasurable).2
      (hμ.integrable q i j)
  have hr := moment_ccum_recursion _ hint 0 0
  rw [integral_map hmeas.aemeasurable (by fun_prop)] at hr
  simp only [pow_zero, one_mul, zero_add, pow_one, Finset.range_one, Finset.sum_singleton,
    Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, integral_const] at hr
  rw [integral_conj, hμ.mean i j, map_zero] at hr
  simpa using hr.symm

private lemma QSI_poly_bdd {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (V : Set (Idx D N → ℂ)) (hV : ∀ x ∈ V, ∑ r, ‖x r‖ ^ 2 ≤ 1) (m : ℕ)
    (P : ResPoly D N) (hP : QSI_Good V Λ z m P) (i : Idx D N) (hi : Pi.single i 1 ∈ V)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ‖resPolyEval P h‖ ≤ QSI_wt P * (max 1 z.im⁻¹) ^ m := by
  have := QSI_wirt_det Λ hΛ z hz V hV m P hP h hh i i hi hi (h i i) 0 0
  simpa [wirt, QSI_setEntry_self h hh i i] using this

private lemma QSI_int_poly {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (V : Set (Idx D N → ℂ))
    (hV : ∀ x ∈ V, ∑ r, ‖x r‖ ^ 2 ≤ 1) (m : ℕ) (P : ResPoly D N) (hP : QSI_Good V Λ z m P)
    (i : Idx D N) (hi : Pi.single i 1 ∈ V) (q : ℕ) :
    Integrable (fun h => resPolyEval P h) μ ∧ Integrable (fun h => ‖resPolyEval P h‖ ^ q) μ := by
  have hm := QSI_aesm μ hμ P (hP.pair hΛ hz.ne')
  have hb : ∀ᵐ h ∂μ, ‖resPolyEval P h‖ ≤ QSI_wt P * (max 1 z.im⁻¹) ^ m := by
    filter_upwards [hμ] with h hh using QSI_poly_bdd Λ hΛ z hz V hV m P hP i hi h hh
  have hw := QSI_wt_nonneg P
  refine ⟨Integrable.of_bound hm _ hb,
    Integrable.of_bound (hm.norm.pow q) ((QSI_wt P * (max 1 z.im⁻¹) ^ m) ^ q) ?_⟩
  filter_upwards [hb] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hh q

private lemma QSI_sqrt_pow {N : ℝ} (hN : 0 < N) (n : ℕ) :
    (Real.sqrt N)⁻¹ ^ n = N ^ (-((n : ℝ) / 2)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hN.le, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  congr 1
  ring

private lemma QSI_norm_pow_eq (q : ℂ) (p : ℕ) (hp : 1 ≤ p) :
    ((‖q‖ ^ (2 * p) : ℝ) : ℂ) = q * (q ^ (p - 1) * starRingEnd ℂ q ^ p) := by
  have e : q * (q ^ (p - 1) * starRingEnd ℂ q ^ p) = (q * starRingEnd ℂ q) ^ p := by
    rw [mul_pow, ← mul_assoc, ← pow_succ']
    congr 2
    omega
  rw [e, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- The moment inequality for the entries of `Q`: with `ϖ = (1 + |z|)² Γ⁴ (Υ/(Nη))^{3/2} ≤ λ_Q`
and the good event `avgGood` off probability `ε₀`,
`E|Q_{kl}|^{2p} ≤ K Σ_{n=1}^{2p} (ϖ λ_Q)^{n/2} E|Q_{kl}|^{2p-n}`
`+ K (N^{-3p-1} + N^{23p+18} ε₀^{1/2})`. -/
theorem q_moment_ineq (D p : ℕ) (hp : 1 ≤ p) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ∀ z : ℂ, ((N : ℝ))⁻¹ ≤ z.im → ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) →
      ∀ Γ Υ bQ ε₀ : ℝ, 1 ≤ Γ → Γ ≤ (N : ℝ) ^ ((1 : ℝ) / 6) → z.im ≤ Υ →
        Υ ≤ (N : ℝ) * z.im →
        (1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3 ≤ bQ →
        μ (avgGood D N θ Λ B z Γ Υ bQ)ᶜ ≤ ENNReal.ofReal ε₀ →
        ∀ k l : Idx D N,
          ∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p) ∂μ ≤
            K * (∑ n ∈ Finset.Icc 1 (2 * p),
                ((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3 * bQ) ^
                  ((n : ℝ) / 2) *
                ∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - n) ∂μ) +
              K * ((N : ℝ) ^ (-(3 * (p : ℝ) + 1)) +
                (N : ℝ) ^ (23 * (p : ℝ) + 18) * Real.sqrt ε₀) := by
  obtain ⟨Ke, hKe0, hKe⟩ := expansion_hp (16 * p + 16) (6 * p - 1) (160 * p + 120) C
  obtain ⟨Kpt, hKpt0, hKpt⟩ := QSI_point D p (16 * p + 16) hp (by omega)
  obtain ⟨Kp1, hKp10, hKp1⟩ := QSI_point1 D p hp
  choose Kc hKc using fun ab : ℕ × ℕ => llClass_ccum_le C ab.1 ab.2
  set Kcm : ℝ := ∑ a ∈ Finset.range (16 * p + 18), ∑ b ∈ Finset.range (16 * p + 18),
    max (Kc (a, b)) 0 with hKcm
  have hKcm0 : 0 ≤ Kcm :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hKcle : ∀ a b, a ≤ 16 * p + 17 → b ≤ 16 * p + 17 → Kc (a, b) ≤ Kcm := fun a b ha hb => by
    have h1 := Finset.single_le_sum (f := fun b => max (Kc (a, b)) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_range.2 (by omega : b < 16 * p + 18))
    have h2 := Finset.single_le_sum
      (f := fun a => ∑ b ∈ Finset.range (16 * p + 18), max (Kc (a, b)) 0)
      (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _)
      (Finset.mem_range.2 (by omega : a < 16 * p + 18))
    exact (le_max_left _ _).trans (h1.trans h2)
  set Lr : ℝ := ((16 * p + 16 : ℕ) : ℝ) with hLr
  set mL : ℝ := ((6 * p - 1 + (16 * p + 16) : ℕ) : ℝ) with hmL
  have hmL1 : 1 ≤ mL := by rw [hmL]; exact_mod_cast (by omega : 1 ≤ 6 * p - 1 + (16 * p + 16))
  set Krem : ℝ := (D : ℝ) * (8 ^ (2 * p - 1) * (6 ^ (22 * p + 16) + 2 ^ (22 * p + 16) *
    (1 + 24 ^ (80 * p + 60)))) with hKrem
  set K1 := Kp1 + (Lr + 1) ^ 2 * (Kcm * Kpt) with hK1
  set Bb := 2 * mL ^ (16 * p + 16) + (Lr + 1) ^ 2 * (Kcm * ((Lr + 1) * mL ^ (16 * p + 16)))
    with hBb
  have hK10 : 0 ≤ K1 := by positivity
  have hBb0 : 0 ≤ Bb := by positivity
  have hKrem0 : 0 ≤ Krem := by positivity
  refine ⟨K1 + (Ke + Bb) * Krem, by positivity, ?_⟩
  intro N θ μ hμ hθ0 hθ1 Λ hΛ hΛn B hB z hzN hzn Γ Υ bQ ε₀ hΓ1 hΓN hΥ1 hΥ2 hϖ hbad k l
  have hprob := hμ.prob
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast k.1.pos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast k.2.pos
  have hN0 : (0 : ℝ) < N := by linarith
  have hz : 0 < z.im := lt_of_lt_of_le (inv_pos.2 hN0) hzN
  have hΓ0 : 0 < Γ := by linarith
  set V := avgVecs D N Λ B with hVdef
  have hV := QSI_avgVecs_norm Λ B hΛn hB
  have hV' : ∀ x ∈ (↑V : Set (Idx D N → ℂ)), ∑ r, ‖x r‖ ^ 2 ≤ 1 := fun x hx => hV x hx
  have he : ∀ r : Idx D N, Pi.single r 1 ∈ (↑V : Set (Idx D N → ℂ)) := fun r =>
    Finset.mem_coe.2 (QSI_avgVecs_e Λ B r)
  obtain ⟨P, hP⟩ := QSI_QP_exists θ hθ0 hθ1 Λ hΛ B z hz k l
  set W : ℝ := (4 * (1 + ‖z‖)) ^ (2 * p - 1) with hW
  have hW0 : 0 ≤ W := by positivity
  have hwtP0 := QSI_wt_nonneg P
  have hwtY : QSI_wt (QSI_PY p P) ≤ W := by
    rw [QSI_wt_PY p hp]; exact pow_le_pow_left₀ hwtP0 hP.wt _
  have hwtF : ∀ i j, QSI_wt (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) ≤ W := fun i j => by
    rw [QSI_wt_mul, QSI_wt_PA, one_mul]; exact hwtY
  have hGY : QSI_Good (↑V) Λ z (6 * p - 3) (QSI_PY p P) := QSI_Good_PY p hp hP.good
  have hGF : ∀ i j, QSI_Good (↑V) Λ z (6 * p - 1)
      (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) :=
    fun i j => ((QSI_Good_PA Λ B z k l i j).mul hGY).mono (by omega)
  have hGQY : QSI_Good (↑V) Λ z (6 * p) (resPolyMul P (QSI_PY p P)) :=
    (hP.good.mul hGY).mono (by omega)
  -- the bad event of the expansion
  set ε₁ := max ε₀ 0 with hε₁
  have hε₁0 : 0 ≤ ε₁ := le_max_right _ _
  have hnull : μ {h | ¬ (Matrix.of h).IsHermitian} = 0 := ae_iff.mp hμ.herm
  have hbadE : μ {h | ∃ q ∈ ({(Λ, z)} : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ)),
      ∃ x ∈ V, ∃ y ∈ V, Γ < ‖resFactorEval (x, y, q.1, q.2) (symArr h)‖} ≤
      ENNReal.ofReal ε₁ := by
    refine (measure_mono (μ := μ) (t := {h | ¬ (Matrix.of h).IsHermitian} ∪
      (avgGood D N θ Λ B z Γ Υ bQ)ᶜ) ?_).trans ?_
    · rintro h ⟨q, hq, x, hx, y, hy, hlt⟩
      by_contra hc
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff, not_or, not_not] at hc
      obtain ⟨hh, hg⟩ := hc
      rw [Finset.mem_singleton] at hq
      subst hq
      rw [symArr_of_isHermitian h hh] at hlt
      exact absurd hlt (not_lt.2 (hg.1 x hx y hy).1)
    · refine (measure_union_le _ _).trans ?_
      rw [hnull, zero_add]
      exact hbad.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the expansion in each entry
  have hM : (0 : ℝ) < (24 * Γ)⁻¹ := by positivity
  have hexp : ∀ i j, ‖(∫ h, resPolyEval (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) h *
        starRingEnd ℂ (h j i) ∂μ) -
      ∑ a ∈ Finset.range (16 * p + 16 + 1), ∑ b ∈ Finset.range (16 * p + 16 + 1 - a),
        ccum (μ.map fun h => h j i) a (b + 1) / ((a.factorial * b.factorial : ℕ) : ℂ) *
          ∫ h, wirt a b (fun w => resPolyEval (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P))
            (setEntry h j i w)) (h j i) ∂μ‖ ≤
      Ke * W * ((N : ℝ) ^ (-(((16 * p + 16 : ℕ) : ℝ) + 2) / 2) *
          (6 * Γ) ^ (6 * p - 1 + (16 * p + 16) + 1) +
        (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) *
          Real.sqrt (ε₁ + ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^
            (-((160 * p + 120 : ℕ) : ℝ)))) := fun i j => by
    have := hKe D N θ μ hμ {(Λ, z)} z.im hz
      (by intro q hq; rw [Finset.mem_singleton] at hq; subst hq; exact ⟨hΛ, le_rfl⟩) j i V
      (QSI_avgVecs_e Λ B j) (QSI_avgVecs_e Λ B i) hV
      (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P))
      (fun t ht => ⟨(hGF i j t ht).1, fun f hf => by
        obtain ⟨a, b, c⟩ := (hGF i j t ht).2 f hf
        exact ⟨a, b, (Λ, z), Finset.mem_singleton_self _, c⟩⟩)
      Γ (24 * Γ)⁻¹ ε₁ hΓ1 hM (le_of_eq (by field_simp)) hε₁0 hbadE
    refine this.trans ?_
    have hR0 : 0 ≤ (N : ℝ) ^ (-(((16 * p + 16 : ℕ) : ℝ) + 2) / 2) *
          (6 * Γ) ^ (6 * p - 1 + (16 * p + 16) + 1) +
        (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) *
          Real.sqrt (ε₁ + ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^
            (-((160 * p + 120 : ℕ) : ℝ))) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hwtF i j) hKe0) hR0
  -- the cumulant coefficients
  set cc : Idx D N → Idx D N → ℕ → ℕ → ℂ := fun j' i' a b =>
    ccum (μ.map fun h => h j' i') a (b + 1) / ((a.factorial * b.factorial : ℕ) : ℂ) with hcc
  have h00 : ∀ i j, cc j i 0 0 = 0 := fun i j => by simp [cc, QSI_ccum01 hμ j i]
  have h10 : ∀ i j, cc j i 1 0 = varProf D N θ j i := fun i j => by
    simp [cc, (llClass_ccum_low D N C θ μ hμ j i).2.1]
  have h01 : ∀ i j, cc j i 0 1 = if j = i then (varProf D N θ j i : ℂ) else 0 := fun i j => by
    simp [cc, (llClass_ccum_low D N C θ μ hμ j i).2.2.2]
  set s : ℝ := (Real.sqrt N)⁻¹ with hs
  have hs0 : 0 < s := by positivity
  have hccb : ∀ i j a b, a + b ≤ 16 * p + 16 → ‖cc j i a b‖ ≤ Kcm * s ^ (a + b + 1) := by
    intro i j a b hab
    have hf : (1 : ℝ) ≤ ‖((a.factorial * b.factorial : ℕ) : ℂ)‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero a)
        (Nat.factorial_ne_zero b))
    have h1 : ‖cc j i a b‖ ≤ ‖ccum (μ.map fun h => h j i) a (b + 1)‖ := by
      simp only [cc, norm_div]
      exact div_le_self (norm_nonneg _) hf
    refine h1.trans ((hKc (a, b + 1) D N θ μ hμ j i).trans ?_)
    have e : (N : ℝ) ^ (-(((a + (b + 1) : ℕ) : ℝ) / 2)) = s ^ (a + b + 1) := by
      rw [hs, QSI_sqrt_pow hN0]; congr 3
    simp only at e ⊢
    rw [e]
    exact mul_le_mul_of_nonneg_right (hKcle a (b + 1) (by omega) (by omega)) (by positivity)
  -- the scales
  set ζ := Real.sqrt (Υ / ((N : ℝ) * z.im)) with hζ
  set ϖ := (1 + ‖z‖) ^ 2 * Γ ^ 4 * ζ ^ 3 with hϖdef
  have hϖ0 : 0 ≤ ϖ := by positivity
  have hbQ0 : 0 ≤ bQ := hϖ0.trans hϖ
  set u := Real.sqrt (ϖ * bQ) with hu
  have hΓs : Γ ≤ Real.sqrt N := by
    refine hΓN.trans ?_
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hsN : s ^ 2 * N = 1 := by
    rw [hs, inv_pow, Real.sq_sqrt hN0.le, inv_mul_cancel₀ hN0.ne']
  have hNη : 0 < (N : ℝ) * z.im := by positivity
  have hWd : Υ / z.im = N * ζ ^ 2 := by
    have hΥ0 : 0 ≤ Υ := hz.le.trans hΥ1
    rw [hζ, Real.sq_sqrt (div_nonneg hΥ0 hNη.le)]
    field_simp
  have hSc : QSI_Sc s ζ Γ (1 + ‖z‖) bQ u := by
    refine ⟨hs0, ?_, ?_, hΓ1, ?_, by linarith [norm_nonneg z], hϖ, Real.sqrt_nonneg _, ?_⟩
    · rw [hs, hζ, ← Real.sqrt_inv]
      apply Real.sqrt_le_sqrt
      rw [le_div_iff₀ hNη]
      field_simp
      linarith
    · rw [hζ, Real.sqrt_le_one]
      rw [div_le_one hNη]; exact hΥ2
    · rw [hs, inv_mul_le_iff₀ (by positivity), mul_one]; exact hΓs
    · rw [hu, Real.sq_sqrt (mul_nonneg hϖ0 hbQ0)]
  -- the pointwise bound
  set Mx := max 1 z.im⁻¹ with hMx
  have hMx1 : 1 ≤ Mx := le_max_left _ _
  have hMxle : Mx ≤ 1 + z.im⁻¹ := max_le (by linarith [inv_pos.2 hz]) (by linarith)
  have hMxE : ∀ n, n ≤ 6 * p - 1 + (16 * p + 16) + 1 →
      Mx ^ n ≤ (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) := fun n hn =>
    (pow_le_pow_right₀ hMx1 hn).trans (pow_le_pow_left₀ (by linarith) hMxle _)
  have hwd : ∀ (m' : ℕ) (P' : ResPoly D N), QSI_Good (↑V) Λ z m' P' → QSI_wt P' ≤ W →
      ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → ∀ (i j : Idx D N) (a b : ℕ),
      m' + a + b ≤ 6 * p - 1 + (16 * p + 16) → a + b ≤ 16 * p + 16 →
      ‖wirt a b (fun w => resPolyEval P' (setEntry h j i w)) (h j i)‖ ≤
        mL ^ (16 * p + 16) * W * Mx ^ (m' + a + b) := by
    intro m' P' hG hw h hh i j a b h1 h2
    refine (QSI_wirt_det Λ hΛ z hz ↑V hV' m' P' hG h hh j i (he j) (he i) (h j i) a b).trans ?_
    have hp1 : ((m' + a + b : ℕ) : ℝ) ^ (a + b) ≤ mL ^ (16 * p + 16) := by
      refine (pow_le_pow_left₀ (by positivity) ?_ _).trans (pow_le_pow_right₀ hmL1 h2)
      rw [hmL]; exact_mod_cast h1
    have := QSI_wt_nonneg P'
    exact mul_le_mul_of_nonneg_right (mul_le_mul hp1 hw this (by positivity)) (by positivity)
  set Gd := avgGood D N θ Λ B z Γ Υ bQ with hGd
  set T := toMeasurable μ Gdᶜ with hT
  set S : (Idx D N → Idx D N → ℂ) → ℝ := fun h => ∑ n ∈ Finset.Icc 1 (2 * p),
    u ^ n * ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - n) with hSdef
  have hS0 : ∀ h, 0 ≤ S h := fun h => Finset.sum_nonneg fun n _ => by positivity
  set cbad : ℝ := ((D : ℝ) * N) ^ 2 *
    (Bb * (W * (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1))) with hcbad
  have hcbad0 : 0 ≤ cbad := by positivity
  have hDN : (0 : ℝ) < (D : ℝ) * N := by positivity
  have hcard : ∀ c : ℝ, ∑ _i : Idx D N, ∑ _j : Idx D N, c = ((D : ℝ) * N) ^ 2 * c := fun c => by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]; ring
  have hpt : ∀ h, (Matrix.of h).IsHermitian →
      ‖QSI_gp θ h Λ B z k l p (16 * p + 16) cc‖ ≤
        ((D : ℝ) * N) * K1 * S h + T.indicator (fun _ => cbad) h := by
    intro h hh
    by_cases hg : h ∈ Gd
    · have hP1 := hKp1 N θ Λ B z Γ Υ bQ s ζ u h k l hθ0 hθ1 hΛ hΛn hB hz hΓ1 hΥ1 hh hg hSc hsN
        hWd
      have hPt := hKpt N θ Λ B z Γ Υ bQ s ζ u h k l hθ0 hθ1 hΛ hΛn hB hz hΓ1 hΥ1 hh hg hSc hsN
        hWd
      have hu2 : u ^ 2 * ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - 2) ≤ S h :=
        Finset.single_le_sum (f := fun n => u ^ n * ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^
          (2 * p - n)) (fun n _ => by positivity) (Finset.mem_Icc.2 ⟨by norm_num, by omega⟩)
      have hb := QSI_gp_le θ hθ0 hθ1 h Λ B z k l p (16 * p + 16) cc s Kcm
        (((D : ℝ) * N) * (Kp1 * u ^ 2 * ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - 2)))
        (((D : ℝ) * N) * (Kpt * S h)) hs0.le hKcm0 (by have := hS0 h; positivity) hccb
        (by
          have := mul_le_mul_of_nonneg_left hP1 hDN.le
          rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hDN.ne', one_mul] at this)
        (fun kk h2 hL => by
          have := mul_le_mul_of_nonneg_left (hPt kk h2 hL) hDN.le
          rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hDN.ne', one_mul] at this)
      refine hb.trans ?_
      have hi0 : 0 ≤ T.indicator (fun _ => cbad) h := Set.indicator_nonneg (fun _ _ => hcbad0) h
      have : ((D : ℝ) * N) * (Kp1 * u ^ 2 * ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - 2)) ≤
          ((D : ℝ) * N) * (Kp1 * S h) := by
        refine mul_le_mul_of_nonneg_left ?_ hDN.le
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hu2 hKp10
      calc _ ≤ ((D : ℝ) * N) * (Kp1 * S h) +
            (Lr + 1) ^ 2 * (Kcm * (((D : ℝ) * N) * (Kpt * S h))) := by linarith
        _ = ((D : ℝ) * N) * K1 * S h := by rw [hK1]; ring
        _ ≤ _ := le_add_of_nonneg_right hi0
    · have hTm : h ∈ T := subset_toMeasurable μ _ hg
      rw [Set.indicator_of_mem hTm]
      set X := W * (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) with hX
      have hX0 : 0 ≤ X := by positivity
      have hb := QSI_gp_le θ hθ0 hθ1 h Λ B z k l p (16 * p + 16) cc s Kcm
        (((D : ℝ) * N) ^ 2 * (2 * mL ^ (16 * p + 16) * X))
        (((D : ℝ) * N) ^ 2 * ((Lr + 1) * mL ^ (16 * p + 16) * X)) hs0.le hKcm0 (by positivity)
        hccb ?_ ?_
      · have := hS0 h
        have h3 : 0 ≤ ((D : ℝ) * N) * K1 * S h := by positivity
        refine hb.trans (le_trans (le_of_eq ?_) (le_add_of_nonneg_left h3))
        rw [hcbad, hBb]; ring
      · have hNi : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
        have hterm : ∀ i j, ‖QSI_A h Λ B z k l i j (h j i)‖ *
            (‖wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ +
              ‖wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖) ≤
            2 * mL ^ (16 * p + 16) * X := by
          intro i j
          have eA : QSI_A h Λ B z k l i j (h j i) = resPolyEval (QSI_PA Λ B z k l i j) h := by
            rw [QSI_eval_PA]; simp only [QSI_A, QSI_setEntry_self h hh j i]
          have hA : ‖QSI_A h Λ B z k l i j (h j i)‖ ≤ Mx ^ 2 := by
            rw [eA]
            have := QSI_poly_bdd Λ hΛ z hz ↑V hV' 2 _ (QSI_Good_PA Λ B z k l i j) k (he k) h hh
            rwa [QSI_wt_PA, one_mul] at this
          have hY : ∀ a b, a + b = 1 → ‖wirt a b (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ ≤
              mL ^ (16 * p + 16) * W * Mx ^ (6 * p - 2) := by
            intro a b hab
            rw [← QSI_slice_PY hP hΛ p hp h hh i j]
            have := hwd (6 * p - 3) _ hGY hwtY h hh i j a b (by omega) (by omega)
            rwa [show 6 * p - 3 + a + b = 6 * p - 2 by omega] at this
          have hY1 := hY 1 0 rfl
          have hY2 := hY 0 1 rfl
          have hMp : Mx ^ 2 * Mx ^ (6 * p - 2) ≤ (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) := by
            rw [← pow_add]; exact hMxE _ (by omega)
          have h0 : 0 ≤ mL ^ (16 * p + 16) * W := by positivity
          calc ‖QSI_A h Λ B z k l i j (h j i)‖ *
                (‖wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ +
                  ‖wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖) ≤
                Mx ^ 2 * (2 * (mL ^ (16 * p + 16) * W * Mx ^ (6 * p - 2))) := by
                gcongr; linarith
            _ = 2 * (mL ^ (16 * p + 16) * W) * (Mx ^ 2 * Mx ^ (6 * p - 2)) := by ring
            _ ≤ 2 * (mL ^ (16 * p + 16) * W) *
                (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) := by gcongr
            _ = 2 * mL ^ (16 * p + 16) * X := by rw [hX]; ring
        have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
          Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm i j
        rw [hcard] at hsum
        have h0 : 0 ≤ ∑ i, ∑ j, ‖QSI_A h Λ B z k l i j (h j i)‖ *
            (‖wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ +
              ‖wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖) :=
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
        calc _ ≤ 1 * ∑ i, ∑ j, ‖QSI_A h Λ B z k l i j (h j i)‖ *
                (‖wirt 1 0 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖ +
                  ‖wirt 0 1 (QSI_Y p (QSI_X θ h Λ B z k l i j)) (h j i)‖) :=
              mul_le_mul_of_nonneg_right hNi h0
          _ ≤ _ := by rw [one_mul]; exact hsum
      · intro kk hkk hkL
        have hs1 : s ^ (kk + 1) ≤ 1 := by
          refine pow_le_one₀ hs0.le ?_
          rw [hs]; exact inv_le_one_of_one_le₀ (by rw [Real.one_le_sqrt]; exact hN1)
        have hterm : ∀ i j, ∑ a ∈ Finset.range (kk + 1), ‖wirt a (kk - a)
            (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w) (h j i)‖ ≤
            (Lr + 1) * mL ^ (16 * p + 16) * X := by
          intro i j
          rw [← QSI_slice_PF hP hΛ p hp h hh i j]
          have ht : ∀ a ∈ Finset.range (kk + 1), ‖wirt a (kk - a) (fun w => resPolyEval
              (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) (setEntry h j i w)) (h j i)‖ ≤
              mL ^ (16 * p + 16) * X := by
            intro a ha
            have ha' := Finset.mem_range.1 ha
            refine (hwd (6 * p - 1) _ (hGF i j) (hwtF i j) h hh i j a (kk - a) (by omega)
              (by omega)).trans ?_
            rw [hX, ← mul_assoc]
            have h0 : 0 ≤ mL ^ (16 * p + 16) * W := by positivity
            exact mul_le_mul_of_nonneg_left (hMxE _ (by omega)) h0
          refine (Finset.sum_le_sum ht).trans ?_
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]
          have h0 : 0 ≤ mL ^ (16 * p + 16) * X := by positivity
          refine mul_le_mul_of_nonneg_right ?_ h0
          rw [hLr]; push_cast; exact_mod_cast (by omega : kk + 1 ≤ 16 * p + 16 + 1)
        have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
          Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm i j
        rw [hcard] at hsum
        have h0 : 0 ≤ ∑ i, ∑ j, ∑ a ∈ Finset.range (kk + 1), ‖wirt a (kk - a)
            (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w) (h j i)‖ :=
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => norm_nonneg _
        calc _ ≤ 1 * ∑ i, ∑ j, ∑ a ∈ Finset.range (kk + 1), ‖wirt a (kk - a)
                (fun w => QSI_A h Λ B z k l i j w * QSI_Y p (QSI_X θ h Λ B z k l i j) w)
                  (h j i)‖ :=
              mul_le_mul_of_nonneg_right hs1 h0
          _ ≤ _ := by rw [one_mul]; exact hsum
  -- integrability
  have hQint : ∀ q : ℕ, Integrable (fun h => ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ q) μ :=
    fun q => (QSI_int_poly μ hμ.herm Λ hΛ z hz ↑V hV' 3 P hP.good k (he k) q).2.congr (by
      filter_upwards [hμ.herm] with h hh; rw [hP.eval h hh])
  set QY : (Idx D N → Idx D N → ℂ) → ℂ := fun h => qMat D N θ (Matrix.of h) Λ B z k l *
    (qMat D N θ (Matrix.of h) Λ B z k l ^ (p - 1) *
      starRingEnd ℂ (qMat D N θ (Matrix.of h) Λ B z k l) ^ p) with hQY
  have hQYint : Integrable QY μ :=
    (QSI_int_poly μ hμ.herm Λ hΛ z hz ↑V hV' (6 * p) _ hGQY k (he k) 0).1.congr (by
      filter_upwards [hμ.herm] with h hh
      rw [resPolyEval_mul, QSI_eval_PY p P (hP.herm hΛ) h hh, hP.eval h hh])
  have hFint : ∀ i j, Integrable (fun h => resPolyEval
      (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) h * starRingEnd ℂ (h j i)) μ := by
    intro i j
    refine Integrable.mono' ((hμ.integrable 1 j i).const_mul
      (QSI_wt (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) * Mx ^ (6 * p - 1))) ?_ ?_
    · exact (QSI_aesm μ hμ.herm _ ((hGF i j).pair hΛ hz.ne')).mul
        (Complex.continuous_conj.comp ((continuous_apply i).comp
          (continuous_apply j))).aestronglyMeasurable
    · filter_upwards [hμ.herm] with h hh
      rw [norm_mul, Complex.norm_conj, pow_one]
      exact mul_le_mul_of_nonneg_right
        (QSI_poly_bdd Λ hΛ z hz ↑V hV' (6 * p - 1) _ (hGF i j) k (he k) h hh) (norm_nonneg _)
  have hWint : ∀ i j a b, Integrable (fun h => wirt a b (fun w => resPolyEval
      (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) (setEntry h j i w)) (h j i)) μ :=
    fun i j a b => QSI_int_wirt μ hμ.herm Λ hΛ z hz ↑V hV' (6 * p - 1) _ (hGF i j) i j (he i)
      (he j) a b
  -- the integral identity
  set Rf : (Idx D N → Idx D N → ℂ) → ℂ := fun h => ((D : ℂ) * N) * QY h -
    ∑ i, ∑ j, resPolyEval (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) h *
      starRingEnd ℂ (h j i) with hRf
  have hSFint : Integrable (fun h => ∑ i, ∑ j, resPolyEval
      (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) h * starRingEnd ℂ (h j i)) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hFint i j
  have hRfint : Integrable Rf μ := (hQYint.const_mul _).sub hSFint
  set Tij : Idx D N → Idx D N → ℂ := fun i j =>
    ∑ a ∈ Finset.range (16 * p + 16 + 1), ∑ b ∈ Finset.range (16 * p + 16 + 1 - a),
      cc j i a b * ∫ h, wirt a b (fun w => resPolyEval
        (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) (setEntry h j i w)) (h j i) ∂μ with hTij
  have hInner : ∀ i j, Integrable (fun h => ∑ a ∈ Finset.range (16 * p + 16 + 1),
      ∑ b ∈ Finset.range (16 * p + 16 + 1 - a), cc j i a b * wirt a b (fun w => resPolyEval
        (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) (setEntry h j i w)) (h j i)) μ :=
    fun i j => integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (hWint i j a b).const_mul _
  have e1 : ∀ i j, Tij i j = ∫ h, ∑ a ∈ Finset.range (16 * p + 16 + 1),
      ∑ b ∈ Finset.range (16 * p + 16 + 1 - a), cc j i a b * wirt a b (fun w => resPolyEval
        (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) (setEntry h j i w)) (h j i) ∂μ := by
    intro i j
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (hWint i j a b).const_mul _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => (hWint i j a b).const_mul _]
    exact Finset.sum_congr rfl fun b _ => (integral_const_mul _ _).symm
  have hTsum : (∑ i, ∑ j, Tij i j) + ∫ h, Rf h ∂μ =
      ∫ h, QSI_gp θ h Λ B z k l p (16 * p + 16) cc ∂μ := by
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e1 i j]
    rw [Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun j _ => hInner i j).symm]
    rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hInner i j]
    rw [← integral_add (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      hInner i j) hRfint]
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    have hd := QSI_decomp θ Λ B z h k l
    have hPFh : ∀ i j, resPolyEval (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) h *
        starRingEnd ℂ (h j i) = (res (Matrix.of h + Λ) z * B) k i * h i j *
          res (Matrix.of h + Λ) z j l * (qMat D N θ (Matrix.of h) Λ B z k l ^ (p - 1) *
            starRingEnd ℂ (qMat D N θ (Matrix.of h) Λ B z k l) ^ p) := by
      intro i j
      rw [resPolyEval_mul, QSI_eval_PA, QSI_eval_PY p P (hP.herm hΛ) h hh, hP.eval h hh,
        QSI_f_eM, QSI_f_ee]
      have hc : starRingEnd ℂ (h j i) = h i j := by simpa using hh.apply i j
      rw [hc]; ring
    have hRfh : Rf h = ((res (Matrix.of h + Λ) z * B * sTheta D N θ (res (Matrix.of h + Λ) z) *
          res (Matrix.of h + Λ) z) k l +
        (∑ a, QSI_cA D N θ B a (res (Matrix.of h + Λ) z) •
          (res (Matrix.of h + Λ) z * Ea D N a * res (Matrix.of h + Λ) z)) k l) *
        (qMat D N θ (Matrix.of h) Λ B z k l ^ (p - 1) *
          starRingEnd ℂ (qMat D N θ (Matrix.of h) Λ B z k l) ^ p) := by
      simp only [hRf, hQY]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hPFh i j]
      simp only [← Finset.sum_mul]
      linear_combination (qMat D N θ (Matrix.of h) Λ B z k l ^ (p - 1) *
        starRingEnd ℂ (qMat D N θ (Matrix.of h) Λ B z k l) ^ p) * hd
    rw [hRfh]
    simp only [QSI_slice_PF hP hΛ p hp h hh]
    exact QSI_pt_identity θ Λ B hΛ z hz p (16 * p + 16) hp (by omega) cc h00 h10 h01 h hh k l
  -- the main identity
  have hmain : ((D : ℂ) * N) * ∫ h, QY h ∂μ =
      (∑ i, ∑ j, ((∫ h, resPolyEval (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) h *
        starRingEnd ℂ (h j i) ∂μ) - Tij i j)) +
      ∫ h, QSI_gp θ h Λ B z k l p (16 * p + 16) cc ∂μ := by
    rw [← hTsum, ← integral_const_mul]
    have e2 : (fun h => ((D : ℂ) * N) * QY h) = fun h => (∑ i, ∑ j, resPolyEval
        (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) h * starRingEnd ℂ (h j i)) + Rf h := by
      funext h; simp only [hRf]; ring
    rw [e2, integral_add hSFint hRfint, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hFint i j]
    rw [Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hFint i j]
    simp only [Finset.sum_sub_distrib]
    ring
  -- the left side
  have hI0 : 0 ≤ ∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p) ∂μ :=
    integral_nonneg fun _ => by positivity
  have hLHS : ((D : ℝ) * N) * ∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p) ∂μ =
      ‖((D : ℂ) * N) * ∫ h, QY h ∂μ‖ := by
    have e3 : ∫ h, QY h ∂μ = ((∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p) ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      simp only [hQY]
      exact (QSI_norm_pow_eq _ p hp).symm
    have hDNc : ‖((D : ℂ) * N)‖ = (D : ℝ) * N := by
      rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    rw [e3, norm_mul, hDNc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hI0]
  -- the remainder of the expansion
  set Rem : ℝ := (N : ℝ) ^ (-(((16 * p + 16 : ℕ) : ℝ) + 2) / 2) *
      (6 * Γ) ^ (6 * p - 1 + (16 * p + 16) + 1) +
    (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) *
      Real.sqrt (ε₁ + ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^
        (-((160 * p + 120 : ℕ) : ℝ))) with hRem
  have hRem0 : 0 ≤ Rem := by positivity
  have hE1 : ‖∑ i, ∑ j, ((∫ h, resPolyEval (resPolyMul (QSI_PA Λ B z k l i j) (QSI_PY p P)) h *
        starRingEnd ℂ (h j i) ∂μ) - Tij i j)‖ ≤ ((D : ℝ) * N) ^ 2 * (Ke * W * Rem) := by
    rw [← hcard]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hexp i j)
  -- the rest
  have hTmeas : MeasurableSet T := measurableSet_toMeasurable _ _
  have hbint : Integrable (fun h => ((D : ℝ) * N) * K1 * S h + T.indicator (fun _ => cbad) h) μ :=
    ((integrable_finsetSum _ fun n _ => (hQint (2 * p - n)).const_mul (u ^ n)).const_mul _).add
      ((integrable_const cbad).indicator hTmeas)
  have hE2 : ‖∫ h, QSI_gp θ h Λ B z k l p (16 * p + 16) cc ∂μ‖ ≤
      ((D : ℝ) * N) * K1 * (∑ n ∈ Finset.Icc 1 (2 * p),
        u ^ n * ∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - n) ∂μ) +
        μ.real T * cbad := by
    refine (norm_integral_le_of_norm_le hbint (by
      filter_upwards [hμ.herm] with h hh using hpt h hh)).trans (le_of_eq ?_)
    rw [integral_add (((integrable_finsetSum _ fun n _ =>
      (hQint (2 * p - n)).const_mul (u ^ n))).const_mul _) ((integrable_const cbad).indicator hTmeas),
      integral_const_mul, integral_finsetSum _ fun n _ => (hQint (2 * p - n)).const_mul (u ^ n),
      integral_indicator_const _ hTmeas, smul_eq_mul]
    simp only [integral_const_mul]
  have hμT : μ.real T ≤ Real.sqrt ε₁ := by
    have h1 : μ.real T ≤ 1 := measureReal_le_one
    have h2 : μ.real T ≤ ε₁ := by
      rw [measureReal_def, hT, measure_toMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hε₁0
        (hbad.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    have h0 : 0 ≤ μ.real T := measureReal_nonneg
    rw [Real.le_sqrt h0 hε₁0, sq]
    have := mul_le_mul h1 h2 h0 zero_le_one
    linarith
  have hsq : Real.sqrt ε₁ ≤ Real.sqrt (ε₁ + ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^
      (-((160 * p + 120 : ℕ) : ℝ))) := Real.sqrt_le_sqrt (by
    have : 0 ≤ ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^ (-((160 * p + 120 : ℕ) : ℝ)) := by
      positivity
    linarith)
  have hbadRem : μ.real T * cbad ≤ ((D : ℝ) * N) ^ 2 * (Bb * W * Rem) := by
    have hX0 : 0 ≤ (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) := by positivity
    have h3 : μ.real T * (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) ≤ Rem := by
      rw [hRem]
      have : μ.real T * (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) ≤
          (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1) *
            Real.sqrt (ε₁ + ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^
              (-((160 * p + 120 : ℕ) : ℝ))) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hμT.trans hsq) hX0
      have : 0 ≤ (N : ℝ) ^ (-(((16 * p + 16 : ℕ) : ℝ) + 2) / 2) *
          (6 * Γ) ^ (6 * p - 1 + (16 * p + 16) + 1) := by positivity
      linarith
    rw [hcbad]
    have hDN2 : 0 ≤ ((D : ℝ) * N) ^ 2 * (Bb * W) := by positivity
    calc μ.real T * (((D : ℝ) * N) ^ 2 *
          (Bb * (W * (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1)))) =
        ((D : ℝ) * N) ^ 2 * (Bb * W) *
          (μ.real T * (1 + z.im⁻¹) ^ (6 * p - 1 + (16 * p + 16) + 1)) := by ring
      _ ≤ ((D : ℝ) * N) ^ 2 * (Bb * W) * Rem := mul_le_mul_of_nonneg_left h3 hDN2
      _ = _ := by ring
  -- the exponents
  have hZN : 1 + ‖z‖ ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 9) := by
    have := Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1 / 9)
    linarith
  have hrem := QSI_exp_rem p hp D hD1 N hN1 Γ (1 + ‖z‖) z.im ε₁ W hΓ1 hΓN
    (by linarith [norm_nonneg z]) hZN hzN hε₁0 hW0 le_rfl
  have hsqε : Real.sqrt ε₁ = Real.sqrt ε₀ := by
    rcases le_total 0 ε₀ with h0 | h0
    · rw [hε₁, max_eq_left h0]
    · rw [hε₁, max_eq_right h0, Real.sqrt_zero, Real.sqrt_eq_zero'.2 h0]
  rw [hsqε] at hrem
  -- the main term
  have hun : ∀ n : ℕ, u ^ n = ((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3 * bQ) ^
      ((n : ℝ) / 2) := fun n => by
    rw [hu, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (mul_nonneg hϖ0 hbQ0),
      show (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) / 2 by ring]
  set Sm := ∑ n ∈ Finset.Icc 1 (2 * p),
    u ^ n * ∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - n) ∂μ with hSm
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun n _ =>
    mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)
  have hSme : Sm = ∑ n ∈ Finset.Icc 1 (2 * p),
      ((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3 * bQ) ^ ((n : ℝ) / 2) *
        ∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - n) ∂μ := by
    rw [hSm]; exact Finset.sum_congr rfl fun n _ => by rw [hun n]
  rw [← hSme]
  -- assembly
  have hfin : ((D : ℝ) * N) * ∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p) ∂μ ≤
      ((D : ℝ) * N) * (K1 * Sm + (Ke + Bb) * ((D : ℝ) * N * (W * Rem))) := by
    rw [hLHS, hmain]
    refine (norm_add_le _ _).trans ?_
    have := add_le_add hE1 (hE2.trans (add_le_add le_rfl hbadRem))
    refine this.trans (le_of_eq ?_)
    ring
  have hfin' := le_of_mul_le_mul_left hfin hDN
  set Nt := (N : ℝ) ^ (-(3 * (p : ℝ) + 1)) + (N : ℝ) ^ (23 * (p : ℝ) + 18) * Real.sqrt ε₀ with hNt
  have hNt0 : 0 ≤ Nt := by positivity
  have hrem' : (D : ℝ) * N * (W * Rem) ≤ Krem * Nt := by
    rw [hRem, hKrem]; exact hrem
  have hKB : 0 ≤ Ke + Bb := by positivity
  calc _ ≤ K1 * Sm + (Ke + Bb) * ((D : ℝ) * N * (W * Rem)) := hfin'
    _ ≤ K1 * Sm + (Ke + Bb) * (Krem * Nt) := by gcongr
    _ ≤ (K1 + (Ke + Bb) * Krem) * Sm + (K1 + (Ke + Bb) * Krem) * Nt := by
        have h1 : 0 ≤ (Ke + Bb) * Krem * Sm := by positivity
        have h2 : 0 ≤ K1 * Nt := by positivity
        have e : (K1 + (Ke + Bb) * Krem) * Sm + (K1 + (Ke + Bb) * Krem) * Nt =
            K1 * Sm + (Ke + Bb) * (Krem * Nt) + ((Ke + Bb) * Krem * Sm + K1 * Nt) := by ring
        rw [e]; linarith


private lemma QSI_young_pt (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 1 ≤ c) (m n : ℕ) (hn : 1 ≤ n)
    (hnm : n ≤ m) : a ^ n * b ^ (m - n) ≤ c ^ m * a ^ m + c⁻¹ * b ^ m := by
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  rw [show n + d - n = d by omega]
  have hc0 : 0 < c := by linarith
  rcases le_total b (c * a) with h | h
  · have h1 : a ^ n * b ^ d ≤ a ^ n * (c * a) ^ d := by gcongr
    have h2 : a ^ n * (c * a) ^ d = c ^ d * a ^ (n + d) := by ring
    have h3 : c ^ d ≤ c ^ (n + d) := pow_le_pow_right₀ hc (by omega)
    have h4 : c ^ d * a ^ (n + d) ≤ c ^ (n + d) * a ^ (n + d) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have h5 : 0 ≤ c⁻¹ * b ^ (n + d) := by positivity
    linarith
  · have hab : a ≤ c⁻¹ * b := by rw [le_inv_mul_iff₀ hc0]; linarith
    have h1 : a ^ n * b ^ d ≤ (c⁻¹ * b) ^ n * b ^ d := by gcongr
    have h2 : (c⁻¹ * b) ^ n * b ^ d = c⁻¹ ^ n * b ^ (n + d) := by ring
    have h3 : c⁻¹ ^ n ≤ c⁻¹ :=
      pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ hc) (by omega)
    have h4 : c⁻¹ ^ n * b ^ (n + d) ≤ c⁻¹ * b ^ (n + d) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have h5 : 0 ≤ c ^ (n + d) * a ^ (n + d) := by positivity
    linarith

/-- One round of the self-improvement for `Q` at a single `N`, with explicit exponents: under the
hypotheses of `q_moment_ineq`, Markov's inequality and Young's inequality give, for every `s > 0`,
`P(|Q_{kl}| > s) ≤ K s^{-2p} ((ϖ λ_Q)^p + N^{-3p-1} + N^{23p+18} ε₀^{1/2})`. -/
theorem q_round (D p : ℕ) (hp : 1 ≤ p) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
      ∀ z : ℂ, ((N : ℝ))⁻¹ ≤ z.im → ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) →
      ∀ Γ Υ bQ ε₀ : ℝ, 1 ≤ Γ → Γ ≤ (N : ℝ) ^ ((1 : ℝ) / 6) → z.im ≤ Υ →
        Υ ≤ (N : ℝ) * z.im →
        (1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3 ≤ bQ →
        μ (avgGood D N θ Λ B z Γ Υ bQ)ᶜ ≤ ENNReal.ofReal ε₀ →
        ∀ (k l : Idx D N) (s : ℝ), 0 < s →
          μ {h | s < ‖qMat D N θ (Matrix.of h) Λ B z k l‖} ≤
            ENNReal.ofReal (K * (s ^ (2 * p))⁻¹ *
              (((1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3 * bQ) ^ p +
                (N : ℝ) ^ (-(3 * (p : ℝ) + 1)) +
                (N : ℝ) ^ (23 * (p : ℝ) + 18) * Real.sqrt ε₀)) := by
  obtain ⟨K₀, hK₀, hK⟩ := q_moment_ineq D p hp C
  set c : ℝ := max 1 (4 * p * K₀) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  have hc4 : 4 * p * K₀ ≤ c := le_max_right _ _
  refine ⟨4 * p * K₀ * c ^ (2 * p) + 2 * K₀, by positivity, ?_⟩
  intro N θ μ hμ hθ0 hθ1 Λ hΛ hΛn B hB z hzN hzn Γ Υ bQ ε₀ hΓ1 hΓN hΥ1 hΥ2 hϖ hbad k l s hs
  have hprob := hμ.prob
  have hN0 : (0 : ℝ) < N := by exact_mod_cast k.2.pos
  have hz : 0 < z.im := lt_of_lt_of_le (inv_pos.2 hN0) hzN
  have hmom := hK N θ μ hμ hθ0 hθ1 Λ hΛ hΛn B hB z hzN hzn Γ Υ bQ ε₀ hΓ1 hΓN hΥ1 hΥ2 hϖ hbad k l
  -- integrability of the moments
  obtain ⟨P, hP⟩ := QSI_QP_exists θ hθ0 hθ1 Λ hΛ B z hz k l
  have hV' : ∀ x ∈ (↑(avgVecs D N Λ B) : Set (Idx D N → ℂ)), ∑ r, ‖x r‖ ^ 2 ≤ 1 :=
    fun x hx => QSI_avgVecs_norm Λ B hΛn hB x hx
  have hQint : ∀ q : ℕ, Integrable (fun h => ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ q) μ :=
    fun q => (QSI_int_poly μ hμ.herm Λ hΛ z hz _ hV' 3 P hP.good k
      (Finset.mem_coe.2 (QSI_avgVecs_e Λ B k)) q).2.congr (by
        filter_upwards [hμ.herm] with h hh; rw [hP.eval h hh])
  set X := (1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3 * bQ with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ (1 + ‖z‖) ^ 2 * Γ ^ 4 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ^ 3 := by positivity
    rw [hX]; exact mul_nonneg this (this.trans hϖ)
  set w := X ^ ((1 : ℝ) / 2) with hw
  have hw0 : 0 ≤ w := by positivity
  have hwn : ∀ n : ℕ, X ^ ((n : ℝ) / 2) = w ^ n := fun n => by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hX0]; congr 1; ring
  have hw2p : w ^ (2 * p) = X ^ p := by
    rw [← hwn, show ((2 * p : ℕ) : ℝ) / 2 = (p : ℝ) by push_cast; ring, Real.rpow_natCast]
  set I := ∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p) ∂μ with hI
  set Nt := (N : ℝ) ^ (-(3 * (p : ℝ) + 1)) + (N : ℝ) ^ (23 * (p : ℝ) + 18) * Real.sqrt ε₀
    with hNt
  have hNt0 : 0 ≤ Nt := by positivity
  -- the pointwise Young inequality, integrated
  have hterm : ∀ n ∈ Finset.Icc 1 (2 * p), w ^ n *
      ∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - n) ∂μ ≤
      c ^ (2 * p) * w ^ (2 * p) + c⁻¹ * I := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    have hm : ∫ h, w ^ n * ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - n) ∂μ ≤
        ∫ h, (c ^ (2 * p) * w ^ (2 * p) + c⁻¹ * ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p))
          ∂μ := integral_mono ((hQint (2 * p - n)).const_mul (w ^ n))
      ((integrable_const (c ^ (2 * p) * w ^ (2 * p))).add ((hQint (2 * p)).const_mul c⁻¹))
      fun h => QSI_young_pt w _ c hw0 (norm_nonneg _) hc1 (2 * p) n hn1 hn2
    rw [integral_add (integrable_const _) ((hQint (2 * p)).const_mul c⁻¹)] at hm
    simp only [integral_const, probReal_univ, one_smul, integral_const_mul] at hm
    simpa only [hI] using hm
  have hI0 : 0 ≤ I := integral_nonneg fun _ => by positivity
  have hsum : ∑ n ∈ Finset.Icc 1 (2 * p), X ^ ((n : ℝ) / 2) *
      ∫ h, ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p - n) ∂μ ≤
      (2 * p : ℝ) * (c ^ (2 * p) * w ^ (2 * p) + c⁻¹ * I) := by
    simp only [hwn]
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    push_cast; ring
  have hc0 : 0 < c := by linarith
  have hhalf : K₀ * ((2 * p : ℝ) * (c⁻¹ * I)) ≤ I / 2 := by
    have : K₀ * (2 * p : ℝ) * c⁻¹ ≤ 1 / 2 := by
      rw [mul_inv_le_iff₀ hc0]; linarith
    calc K₀ * ((2 * p : ℝ) * (c⁻¹ * I)) = (K₀ * (2 * p : ℝ) * c⁻¹) * I := by ring
      _ ≤ (1 / 2) * I := mul_le_mul_of_nonneg_right this hI0
      _ = I / 2 := by ring
  have hIb : I ≤ 4 * p * K₀ * c ^ (2 * p) * w ^ (2 * p) + 2 * K₀ * Nt := by
    have h1 := hmom.trans (add_le_add (mul_le_mul_of_nonneg_left hsum hK₀) le_rfl)
    have e : K₀ * ((2 * p : ℝ) * (c ^ (2 * p) * w ^ (2 * p) + c⁻¹ * I)) =
        2 * p * K₀ * c ^ (2 * p) * w ^ (2 * p) + K₀ * ((2 * p : ℝ) * (c⁻¹ * I)) := by ring
    rw [e] at h1
    linarith
  rw [hw2p] at hIb
  -- Markov
  have hs2p : 0 < s ^ (2 * p) := by positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun h => by
    simp only [Pi.zero_apply]; positivity) (hQint (2 * p)) (s ^ (2 * p))
  have hsub : {h : Idx D N → Idx D N → ℂ | s < ‖qMat D N θ (Matrix.of h) Λ B z k l‖} ⊆
      {h | s ^ (2 * p) ≤ ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p)} := fun h hh =>
    pow_le_pow_left₀ hs.le (le_of_lt hh) _
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hμr : μ.real {h | s ^ (2 * p) ≤ ‖qMat D N θ (Matrix.of h) Λ B z k l‖ ^ (2 * p)} ≤
      (s ^ (2 * p))⁻¹ * I := by
    rw [le_inv_mul_iff₀ hs2p]; exact hmk
  refine hμr.trans ?_
  have hKX : I ≤ (4 * p * K₀ * c ^ (2 * p) + 2 * K₀) * (X ^ p + Nt) := by
    have h1 : 0 ≤ 4 * p * K₀ * c ^ (2 * p) * Nt := by positivity
    have h2 : 0 ≤ 2 * K₀ * X ^ p := by positivity
    nlinarith
  calc (s ^ (2 * p))⁻¹ * I ≤ (s ^ (2 * p))⁻¹ *
      ((4 * p * K₀ * c ^ (2 * p) + 2 * K₀) * (X ^ p + Nt)) :=
        mul_le_mul_of_nonneg_left hKX (by positivity)
    _ = _ := by rw [hNt]; ring


section QSI_Lam

open scoped Matrix.Norms.L2Operator

/-- The embedding of `ℂ^N` as the block `a` of `Idx D N`. -/
private def QSI_J (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Fin N) ℂ :=
  Matrix.of fun p i => if p = (a, i) then 1 else 0

private lemma QSI_J_conj_mul (D N : ℕ) (a : Fin D) :
    (QSI_J D N a)ᴴ * QSI_J D N a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, QSI_J, Matrix.of_apply,
    Matrix.one_apply]
  have : ∀ p : Idx D N, star (if p = (a, i) then (1 : ℂ) else 0) * (if p = (a, j) then 1 else 0) =
      if p = (a, i) then (if i = j then 1 else 0) else 0 := by
    intro p
    by_cases h : p = (a, i)
    · subst h
      by_cases hij : i = j <;> simp [hij]
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma QSI_J_norm (D N : ℕ) (hN : 1 ≤ N) (a : Fin D) :
    ‖QSI_J D N a‖ ≤ 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (QSI_J D N a)
  rw [QSI_J_conj_mul, norm_one] at h1
  have h0 : 0 ≤ ‖QSI_J D N a‖ := norm_nonneg _
  nlinarith

private lemma QSI_block_norm (D N : ℕ) (hN : 1 ≤ N) (a b : Fin D)
    (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖QSI_J D N a * M * (QSI_J D N b)ᴴ‖ ≤ ‖M‖ := by
  have ha := QSI_J_norm D N hN a
  have hb := QSI_J_norm D N hN b
  calc ‖QSI_J D N a * M * (QSI_J D N b)ᴴ‖
      ≤ ‖QSI_J D N a * M‖ * ‖(QSI_J D N b)ᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖QSI_J D N a‖ * ‖M‖) * ‖(QSI_J D N b)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
    _ = ‖M‖ := by ring

private lemma QSI_block_apply (D N : ℕ) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ)
    (p q : Idx D N) :
    (QSI_J D N a * M * (QSI_J D N b)ᴴ) p q =
      if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = a <;> by_cases h2 : q1 = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, QSI_J, Prod.ext_iff, h1, h2]

private lemma QSI_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = ∑ a : Fin D, ∑ b : Fin D,
      ((if fwd D a b then QSI_J D N a * A * (QSI_J D N b)ᴴ else 0) +
        (if fwd D b a then QSI_J D N a * Aᴴ * (QSI_J D N b)ᴴ else 0)) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.add_apply]
  have e1 : ∀ a b : Fin D,
      (if fwd D a b then QSI_J D N a * A * (QSI_J D N b)ᴴ else 0) p q =
      if fwd D a b ∧ p.1 = a ∧ q.1 = b then A p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D a b <;> simp [h, QSI_block_apply]
  have e2 : ∀ a b : Fin D,
      (if fwd D b a then QSI_J D N a * Aᴴ * (QSI_J D N b)ᴴ else 0) p q =
      if fwd D b a ∧ p.1 = a ∧ q.1 = b then Aᴴ p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D b a <;> simp [h, QSI_block_apply]
  simp only [e1, e2, Finset.sum_add_distrib]
  unfold lam
  congr 1
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D p.1 q.1 <;> simp [h]
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D q.1 p.1 <;> simp [h, Matrix.conjTranspose_apply]

/-- `‖Λ‖ ≤ 2 D² ‖A‖` for the interaction `Λ = lam D N A` of (1.3) [matrix_H]. -/
private lemma QSI_opNorm_lam (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := by
  change ‖lam D N A‖ ≤ 2 * (D : ℝ) ^ 2 * ‖A‖
  rw [QSI_lam_eq]
  have hb : ∀ a b : Fin D,
      ‖(if fwd D a b then QSI_J D N a * A * (QSI_J D N b)ᴴ else 0) +
      (if fwd D b a then QSI_J D N a * Aᴴ * (QSI_J D N b)ᴴ else 0)‖ ≤
        2 * ‖A‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D a b then QSI_J D N a * A * (QSI_J D N b)ᴴ else 0)‖ ≤
        ‖A‖ := by
      split_ifs
      · exact QSI_block_norm D N hN a b A
      · simp
    have h2 : ‖(if fwd D b a then QSI_J D N a * Aᴴ * (QSI_J D N b)ᴴ else 0)‖ ≤
        ‖A‖ := by
      split_ifs
      · exact (QSI_block_norm D N hN a b Aᴴ).trans (by rw [Matrix.l2_opNorm_conjTranspose])
      · simp
    linarith
  calc ‖∑ a : Fin D, ∑ b : Fin D, _‖ ≤ ∑ a : Fin D, ‖∑ b : Fin D, _‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin D, ∑ b : Fin D, 2 * ‖A‖ := by
        refine Finset.sum_le_sum fun a _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb a b)
    _ = 2 * (D : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end QSI_Lam

/-- `ϖ` with the scales of the a priori bound against `ϖ_φ`. -/
private lemma QSI_varpi_le (Z0 φ η im Nr t : ℝ) (hφ : 0 ≤ φ) (hη : 0 < η)
    (him : 0 ≤ im) (hN : 0 < Nr) (ht : 1 ≤ t) :
    Z0 ^ 2 * (5 / 4 + t ^ 2 * φ) ^ 4 *
        Real.sqrt ((41 / 16 * η + 25 / 16 * im + t ^ 2 * φ) / (Nr * η)) ^ 3 ≤
      11 * t ^ 11 * (Z0 ^ 2 * (1 + φ) ^ 4 * Real.sqrt ((im + φ + η) / (Nr * η)) ^ 3) := by
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have hNη : 0 < Nr * η := mul_pos hN hη
  have hΓ : 5 / 4 + t ^ 2 * φ ≤ 5 / 4 * t ^ 2 * (1 + φ) := by nlinarith
  have hΓ4 : (5 / 4 + t ^ 2 * φ) ^ 4 ≤ (5 / 4 * t ^ 2 * (1 + φ)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hΓ 4
  set X := (im + φ + η) / (Nr * η) with hX
  have hX0 : 0 ≤ X := by positivity
  have hΥ : (41 / 16 * η + 25 / 16 * im + t ^ 2 * φ) / (Nr * η) ≤ (13 / 8 * t) ^ 2 * X := by
    rw [hX, div_le_iff₀ hNη]
    rw [show (13 / 8 * t) ^ 2 * ((im + φ + η) / (Nr * η)) * (Nr * η) =
      (13 / 8 * t) ^ 2 * (im + φ + η) by field_simp]
    nlinarith
  have hs : Real.sqrt ((41 / 16 * η + 25 / 16 * im + t ^ 2 * φ) / (Nr * η)) ≤
      13 / 8 * t * Real.sqrt X := by
    calc _ ≤ Real.sqrt ((13 / 8 * t) ^ 2 * X) := Real.sqrt_le_sqrt hΥ
      _ = 13 / 8 * t * Real.sqrt X := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hs3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 3
  have h1 : Z0 ^ 2 * (5 / 4 + t ^ 2 * φ) ^ 4 *
      Real.sqrt ((41 / 16 * η + 25 / 16 * im + t ^ 2 * φ) / (Nr * η)) ^ 3 ≤
      Z0 ^ 2 * (5 / 4 * t ^ 2 * (1 + φ)) ^ 4 * (13 / 8 * t * Real.sqrt X) ^ 3 := by
    gcongr
  calc _ ≤ _ := h1
    _ = (5 / 4) ^ 4 * (13 / 8) ^ 3 * t ^ 11 * (Z0 ^ 2 * (1 + φ) ^ 4 * Real.sqrt X ^ 3) := by ring
    _ ≤ 11 * t ^ 11 * (Z0 ^ 2 * (1 + φ) ^ 4 * Real.sqrt X ^ 3) := by
      gcongr
      norm_num

/-- `ϖ_φ ≥ N^{-3/2}`. -/
private lemma QSI_varpi_ge (Z0 φ η im Nr : ℝ) (hZ0 : 1 ≤ Z0) (hφ : 0 ≤ φ) (hη : 0 < η)
    (him : 0 ≤ im) (hN : 0 < Nr) :
    Nr ^ (-(3 : ℝ) / 2) ≤ Z0 ^ 2 * (1 + φ) ^ 4 * Real.sqrt ((im + φ + η) / (Nr * η)) ^ 3 := by
  have hNη : 0 < Nr * η := mul_pos hN hη
  have h1 : Nr⁻¹ ≤ (im + φ + η) / (Nr * η) := by
    rw [le_div_iff₀ hNη]; field_simp; linarith
  have h2 : Real.sqrt Nr⁻¹ ^ 3 ≤ Real.sqrt ((im + φ + η) / (Nr * η)) ^ 3 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h1) 3
  have h3 : Nr ^ (-(3 : ℝ) / 2) = Real.sqrt Nr⁻¹ ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.inv_rpow hN.le, ← Real.rpow_neg hN.le]
    congr 1; norm_num
  have h4 : 1 ≤ Z0 ^ 2 * (1 + φ) ^ 4 := by
    have : 1 ≤ Z0 ^ 2 := one_le_pow₀ hZ0
    have : 1 ≤ (1 + φ) ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  rw [h3]
  calc Real.sqrt Nr⁻¹ ^ 3 ≤ 1 * Real.sqrt ((im + φ + η) / (Nr * η)) ^ 3 := by rw [one_mul]; exact h2
    _ ≤ _ := mul_le_mul_of_nonneg_right h4 (by positivity)

/-- The exponent bookkeeping of one round at a single `N`. -/
private lemma QSI_round_arith (Nr : ℝ) (hN : 1 ≤ Nr) (p : ℕ) (τ' D' K Dd Y Wb : ℝ) (hK : 0 ≤ K)
    (hDd : 0 ≤ Dd) (hτ' : 0 < τ') (hpτ : D' + 1 ≤ p * τ') (hY : Nr ^ (-(3 : ℝ)) ≤ Y)
    (hW0 : 0 ≤ Wb) (hWb : Wb ≤ 198 * Nr ^ τ' * Y) :
    K * ((Nr ^ τ' * Y ^ ((1 : ℝ) / 2)) ^ (2 * p))⁻¹ *
      (Wb ^ p + Nr ^ (-(3 * (p : ℝ) + 1)) + Nr ^ (23 * (p : ℝ) + 18) *
        Real.sqrt (17 * Dd ^ 2 * Nr ^ 2 * Nr ^ (-(2 * (26 * (p : ℝ) + 20 + D'))))) ≤
      K * (198 ^ p + 1 + 5 * Dd) * Nr ^ (-(D' + 1)) := by
  have hN0 : 0 < Nr := by linarith
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hpτ0 : 0 ≤ (p : ℝ) * τ' := by positivity
  -- the normalization
  have hs : (Nr ^ τ' * Y ^ ((1 : ℝ) / 2)) ^ (2 * p) = Nr ^ (2 * (p : ℝ) * τ') * Y ^ p := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_natCast (Y ^ _),
      ← Real.rpow_mul hY0.le, ← Real.rpow_natCast Y p]
    congr 2 <;> push_cast <;> ring
  rw [hs]
  have hYp : Nr ^ (-(3 * (p : ℝ))) ≤ Y ^ p := by
    calc Nr ^ (-(3 * (p : ℝ))) = (Nr ^ (-(3 : ℝ))) ^ p := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; ring
      _ ≤ Y ^ p := pow_le_pow_left₀ (by positivity) hY p
  have hYi : (Y ^ p)⁻¹ ≤ Nr ^ (3 * (p : ℝ)) := by
    rw [inv_le_comm₀ (by positivity) (by positivity), ← Real.rpow_neg hN0.le]; exact hYp
  have hinv : (Nr ^ (2 * (p : ℝ) * τ') * Y ^ p)⁻¹ ≤ Nr ^ (-(2 * (p : ℝ) * τ') + 3 * p) := by
    rw [mul_inv, Real.rpow_add hN0, Real.rpow_neg hN0.le]
    exact mul_le_mul_of_nonneg_left hYi (by positivity)
  set E0 := Nr ^ (-(D' + 1)) with hE0
  -- the main term
  have hT1 : (Nr ^ (2 * (p : ℝ) * τ') * Y ^ p)⁻¹ * Wb ^ p ≤ 198 ^ p * E0 := by
    have h1 : Wb ^ p ≤ 198 ^ p * Nr ^ ((p : ℝ) * τ') * Y ^ p := by
      calc Wb ^ p ≤ (198 * Nr ^ τ' * Y) ^ p := pow_le_pow_left₀ hW0 hWb p
        _ = 198 ^ p * Nr ^ ((p : ℝ) * τ') * Y ^ p := by
          rw [mul_pow, mul_pow, ← Real.rpow_natCast (Nr ^ τ'), ← Real.rpow_mul hN0.le, mul_comm τ']
    have h2 : (Nr ^ (2 * (p : ℝ) * τ') * Y ^ p)⁻¹ * (198 ^ p * Nr ^ ((p : ℝ) * τ') * Y ^ p) =
        198 ^ p * Nr ^ (-((p : ℝ) * τ')) := by
      rw [show 2 * (p : ℝ) * τ' = (p : ℝ) * τ' + (p : ℝ) * τ' by ring, Real.rpow_add hN0,
        Real.rpow_neg hN0.le]
      field_simp
    calc _ ≤ (Nr ^ (2 * (p : ℝ) * τ') * Y ^ p)⁻¹ * (198 ^ p * Nr ^ ((p : ℝ) * τ') * Y ^ p) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 198 ^ p * Nr ^ (-((p : ℝ) * τ')) := h2
      _ ≤ 198 ^ p * E0 := by
          gcongr; exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  -- the remainder
  have hT2 : (Nr ^ (2 * (p : ℝ) * τ') * Y ^ p)⁻¹ * Nr ^ (-(3 * (p : ℝ) + 1)) ≤ E0 := by
    calc _ ≤ Nr ^ (-(2 * (p : ℝ) * τ') + 3 * p) * Nr ^ (-(3 * (p : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = Nr ^ (-(2 * (p : ℝ) * τ') - 1) := by rw [← Real.rpow_add hN0]; congr 1; ring
      _ ≤ E0 := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  -- the bad event
  have hsq : Real.sqrt (17 * Dd ^ 2 * Nr ^ 2 * Nr ^ (-(2 * (26 * (p : ℝ) + 20 + D')))) ≤
      5 * Dd * Nr ^ (1 - (26 * (p : ℝ) + 20 + D')) := by
    have e : 17 * Dd ^ 2 * Nr ^ 2 * Nr ^ (-(2 * (26 * (p : ℝ) + 20 + D'))) =
        17 * (Dd * Nr ^ (1 - (26 * (p : ℝ) + 20 + D'))) ^ 2 := by
      have e1 : (Nr ^ (1 - (26 * (p : ℝ) + 20 + D'))) ^ 2 =
          Nr ^ ((2 : ℝ) - 2 * (26 * (p : ℝ) + 20 + D')) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
      have e2 : Nr ^ 2 * Nr ^ (-(2 * (26 * (p : ℝ) + 20 + D'))) =
          Nr ^ ((2 : ℝ) - 2 * (26 * (p : ℝ) + 20 + D')) := by
        rw [← Real.rpow_natCast Nr 2, ← Real.rpow_add hN0]; congr 1
      rw [mul_pow, e1, mul_assoc (17 * Dd ^ 2), e2]
      ring
    rw [e, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    have : Real.sqrt 17 ≤ 5 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have h0 : 0 ≤ Dd * Nr ^ (1 - (26 * (p : ℝ) + 20 + D')) := by positivity
    calc Real.sqrt 17 * (Dd * Nr ^ (1 - (26 * (p : ℝ) + 20 + D'))) ≤
        5 * (Dd * Nr ^ (1 - (26 * (p : ℝ) + 20 + D'))) := mul_le_mul_of_nonneg_right this h0
      _ = _ := by ring
  have hT3 : (Nr ^ (2 * (p : ℝ) * τ') * Y ^ p)⁻¹ * (Nr ^ (23 * (p : ℝ) + 18) *
      Real.sqrt (17 * Dd ^ 2 * Nr ^ 2 * Nr ^ (-(2 * (26 * (p : ℝ) + 20 + D'))))) ≤
      5 * Dd * E0 := by
    calc _ ≤ Nr ^ (-(2 * (p : ℝ) * τ') + 3 * p) * (Nr ^ (23 * (p : ℝ) + 18) *
          (5 * Dd * Nr ^ (1 - (26 * (p : ℝ) + 20 + D')))) := by
          gcongr
      _ = 5 * Dd * Nr ^ (-(2 * (p : ℝ) * τ') - 1 - D') := by
          rw [show 5 * Dd * Nr ^ (-(2 * (p : ℝ) * τ') - 1 - D') =
            5 * Dd * (Nr ^ (-(2 * (p : ℝ) * τ') + 3 * p) * (Nr ^ (23 * (p : ℝ) + 18) *
              Nr ^ (1 - (26 * (p : ℝ) + 20 + D')))) by
            rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 2; ring]
          ring
      _ ≤ 5 * Dd * E0 := by
          gcongr; exact Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  have hsum := add_le_add (add_le_add hT1 hT2) hT3
  calc _ = K * ((Nr ^ (2 * (p : ℝ) * τ') * Y ^ p)⁻¹ * Wb ^ p +
        (Nr ^ (2 * (p : ℝ) * τ') * Y ^ p)⁻¹ * Nr ^ (-(3 * (p : ℝ) + 1)) +
        (Nr ^ (2 * (p : ℝ) * τ') * Y ^ p)⁻¹ * (Nr ^ (23 * (p : ℝ) + 18) *
          Real.sqrt (17 * Dd ^ 2 * Nr ^ 2 * Nr ^ (-(2 * (26 * (p : ℝ) + 20 + D')))))) := by ring
    _ ≤ K * (198 ^ p * E0 + E0 + 5 * Dd * E0) := mul_le_mul_of_nonneg_left hsum hK
    _ = _ := by ring



private lemma QSI_ev_le (C a : ℝ) (ha : 0 < a) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C ≤ (N : ℝ) ^ a := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop C)

/-- The a priori bound restricted to the points of positive imaginary part. -/
private lemma QSI_apriori_restrict {D : ℕ} {μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)}
    {A : ∀ N, Matrix (Fin N) (Fin N) ℂ} {Z : ℕ → Set ℂ} {φ : ℕ → ℂ → ℝ}
    (hLL : aprioriLL D μ A Z φ) : aprioriLL D μ A (fun N => {z | z ∈ Z N ∧ 0 < z.im}) φ := by
  intro τ hτ D' hD'
  obtain ⟨N₀, hN₀⟩ := hLL τ hτ D' hD'
  exact ⟨N₀, fun N hN u => hN₀ N hN ⟨⟨u.1.1, u.1.2.1⟩, u.2⟩⟩

private lemma QSI_card_avgVecs (D N : ℕ) (Λ B : Matrix (Idx D N) (Idx D N) ℂ) :
    ((avgVecs D N Λ B).card : ℝ) ≤ 4 * ((D : ℝ) * N) := by
  have h : (avgVecs D N Λ B).card ≤ 4 * (D * N) := by
    unfold avgVecs
    have e : ∀ f : Idx D N → Idx D N → ℂ, (Finset.univ.image f).card ≤ D * N := fun f =>
      (Finset.card_image_le).trans (by simp)
    have h1 := Finset.card_union_le
      (Finset.univ.image (fun k : Idx D N => (Pi.single k 1 : Idx D N → ℂ)) ∪
        Finset.univ.image (fun k => B *ᵥ Pi.single k 1) ∪
        Finset.univ.image (fun k => Bᴴ *ᵥ Pi.single k 1))
      (Finset.univ.image (fun k => Λ *ᵥ Pi.single k 1))
    have h2 := Finset.card_union_le
      (Finset.univ.image (fun k : Idx D N => (Pi.single k 1 : Idx D N → ℂ)) ∪
        Finset.univ.image (fun k => B *ᵥ Pi.single k 1))
      (Finset.univ.image (fun k => Bᴴ *ᵥ Pi.single k 1))
    have h3 := Finset.card_union_le
      (Finset.univ.image (fun k : Idx D N => (Pi.single k 1 : Idx D N → ℂ)))
      (Finset.univ.image (fun k => B *ᵥ Pi.single k 1))
    have := e (fun k => Pi.single k 1); have := e (fun k => B *ᵥ Pi.single k 1)
    have := e (fun k => Bᴴ *ᵥ Pi.single k 1); have := e (fun k => Λ *ᵥ Pi.single k 1)
    omega
  exact_mod_cast h

set_option maxHeartbeats 1000000 in
/-- One self-improving step for `Q`: under `LLSeq`, `10 δ₀ ≤ τ` and `aprioriLL`,
if `Q_{kl} ≺ λ_Q` in sup form over `z ∈ Z_N`, `‖B‖ ≤ 1` and `k, l` for a deterministic
`λ_Q ≥ ϖ_φ = (1 + |z|)² (1 + φ)⁴ ((Im m + φ + η)/(Nη))^{3/2}`, then `Q_{kl} ≺ (ϖ_φ λ_Q)^{1/2}`
(Definition 2.8 [stoch_domination]). -/
theorem q_self_improv :
    ∀ (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
      (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ),
      LLSeq D δA C θ μ A → 0 < τ → 0 ≤ δ₀ → 10 * δ₀ ≤ τ →
    ∀ Z : ℕ → Set ℂ, (∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im) →
    ∀ φ : ℕ → ℂ → ℝ, (∀ N, ∀ z ∈ Z N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀) →
    aprioriLL D μ A Z φ →
    ∀ bQ : ℕ → ℂ → ℝ, (∀ N, ∀ z ∈ Z N, (1 + ‖z‖) ^ 2 * (1 + φ N z) ^ 4 *
        Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im)) ^ 3 ≤
          bQ N z) →
    PrecS μ (U := fun N => {z // z ∈ Z N} ×
        {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1} × Idx D N × Idx D N)
      (fun N w h => ‖qMat D N (θ N) (Matrix.of h) (lam D N (A N)) w.2.1.1 w.1.1 w.2.2.1
        w.2.2.2‖)
      (fun N w _ => bQ N w.1.1) →
    PrecS μ (U := fun N => {z // z ∈ Z N} ×
        {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1} × Idx D N × Idx D N)
      (fun N w h => ‖qMat D N (θ N) (Matrix.of h) (lam D N (A N)) w.2.1.1 w.1.1 w.2.2.1
        w.2.2.2‖)
      (fun N w _ => ((1 + ‖w.1.1‖) ^ 2 * (1 + φ N w.1.1) ^ 4 *
        Real.sqrt (((mExt (lam D N (A N)) w.1.1).im + φ N w.1.1 + w.1.1.im) /
          ((N : ℝ) * w.1.1.im)) ^ 3 * bQ N w.1.1) ^ ((1 : ℝ) / 2)) := by
  intro D δA τ δ₀ C θ μ A hseq hτ hδ₀ h10 Z hZ φ hφ hLL bQ hbQ hpre τ' hτ' D' hD'
  have hD1 : 1 ≤ D := hseq.one_le_D
  by_cases hδ9 : δ₀ ≤ 1 / 9
  swap
  · refine ⟨2, fun N hN u => ?_⟩
    exfalso
    obtain ⟨⟨z, hz⟩, -⟩ := u
    have h1 := hZ N z hz
    have h2 : (N : ℝ) ^ (-1 + τ) ≤ (N : ℝ) ^ δ₀ :=
      h1.2.trans ((Complex.im_le_norm z).trans h1.1)
    rw [Real.rpow_le_rpow_left_iff (by exact_mod_cast (by omega : 1 < N))] at h2
    linarith
  -- the exponents of the round
  set p : ℕ := ⌈(D' + 1) / τ'⌉₊ + 1 with hpdef
  have hp : 1 ≤ p := by omega
  have hpτ : D' + 1 ≤ p * τ' := by
    have h1 : (D' + 1) / τ' ≤ ⌈(D' + 1) / τ'⌉₊ := Nat.le_ceil _
    have h2 : (⌈(D' + 1) / τ'⌉₊ : ℝ) ≤ p := by rw [hpdef]; push_cast; linarith
    rw [div_le_iff₀ hτ'] at h1
    nlinarith
  clear_value p
  obtain ⟨K, hK0, hK⟩ := q_round D p hp C
  set ε₂ := τ' / 2 with hε₂
  have hε₂0 : 0 < ε₂ := by positivity
  set ε₁ := min (τ' / 11) (min (τ / 20) (1 / 36)) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hε₁a : ε₁ ≤ τ' / 11 := min_le_left _ _
  have hε₁b : ε₁ ≤ τ / 20 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₁c : ε₁ ≤ 1 / 36 := (min_le_right _ _).trans (min_le_right _ _)
  clear_value ε₁ ε₂
  set D'' : ℝ := 2 * (26 * (p : ℝ) + 20 + D') with hD''
  have hD''0 : 0 < D'' := by positivity
  obtain ⟨N₁, hN₁⟩ := apriori_good D δA C θ μ A hseq (fun N => {z | z ∈ Z N ∧ 0 < z.im})
    (fun N z hz => hz.2) φ (QSI_apriori_restrict hLL) ε₁ D'' hε₁0 hD''0
  obtain ⟨N₂, hN₂⟩ := hpre ε₂ hε₂0 D'' hD''0
  obtain ⟨N₃, hN₃⟩ := QSI_ev_le 2 (1 / 36) (by norm_num)
  obtain ⟨N₄, hN₄⟩ := QSI_ev_le 6 (τ / 2) (by positivity)
  obtain ⟨N₅, hN₅⟩ := QSI_ev_le (20 * (D : ℝ) ^ 2) δA hseq.pos
  obtain ⟨N₆, hN₆⟩ := QSI_ev_le (K * (198 ^ p + 1 + 5 * (D : ℝ))) 1 one_pos
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) 2), fun N hN u => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hN1, hN2⟩, hN3, hN4⟩, ⟨hN5, hN6⟩, hN7⟩ := hN
  obtain ⟨⟨z, hzZ⟩, ⟨B, hB⟩, k, l⟩ := u
  dsimp only
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNr0 : (0 : ℝ) < N := by linarith
  obtain ⟨hzn0, hzim0⟩ := hZ N z hzZ
  have hz : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr0 _) hzim0
  have hΛ : (lam D N (A N)).IsHermitian := lam_isHermitian D N (A N)
  have hΛn : opNorm (lam D N (A N)) ≤ 1 / 10 := by
    have h1 := QSI_opNorm_lam D N (by omega) (A N)
    have h2 := hseq.small N
    have h3 := hN₅ N hN5
    have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    have hD0 : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
    have hpos : 0 < (N : ℝ) ^ δA := Real.rpow_pos_of_pos hNr0 _
    calc opNorm (lam D N (A N)) ≤ 2 * (D : ℝ) ^ 2 * opNorm (A N) := h1
      _ ≤ 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ (-δA) := by gcongr
      _ ≤ 1 / 10 := by
        rw [Real.rpow_neg hNr0.le, ← div_eq_mul_inv, div_le_iff₀ hpos]
        linarith
  have : Nonempty (Idx D N) := ⟨k⟩
  have hmS := mSol_spec (lam D N (A N)) hΛ z hz
  have hmA := mSol_apriori (lam D N (A N)) hΛ hΛn z hz
  have hme : mExt (lam D N (A N)) z = mSol (lam D N (A N)) z := by simp [mExt, hz]
  have him0 : 0 ≤ (mExt (lam D N (A N)) z).im := by rw [hme]; exact hmS.1.le
  have him1 : (mExt (lam D N (A N)) z).im ≤ 1 := by
    rw [hme]; exact (Complex.im_le_norm _).trans hmA.2.1.le
  obtain ⟨hφ1, hφ2⟩ := hφ N z hzZ
  have hφ0 : 0 ≤ φ N z := le_trans (by positivity) hφ1
  set t := (N : ℝ) ^ (ε₁ / 2) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hNr1 (by positivity)
  have ht2 : t ^ 2 = (N : ℝ) ^ ε₁ := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hNr0.le]; congr 1; push_cast; ring
  have hNε1 : 1 ≤ (N : ℝ) ^ ε₁ := Real.one_le_rpow hNr1 hε₁0.le
  have hNφ : (N : ℝ) ^ ε₁ * φ N z ≤ (N : ℝ) ^ (δ₀ + ε₁) := by
    rw [Real.rpow_add hNr0, mul_comm ((N : ℝ) ^ δ₀)]
    exact mul_le_mul_of_nonneg_left hφ2 (by positivity)
  have hδε : δ₀ + ε₁ ≤ τ / 2 := by linarith
  -- the hypotheses of the round
  have hzN : ((N : ℝ))⁻¹ ≤ z.im := by
    rw [← Real.rpow_neg_one]
    exact (Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)).trans hzim0
  have hzn : ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) :=
    hzn0.trans (Real.rpow_le_rpow_of_exponent_le hNr1 hδ9)
  have hΓ1 : 1 ≤ 5 / 4 + (N : ℝ) ^ ε₁ * φ N z := by
    have : 0 ≤ (N : ℝ) ^ ε₁ * φ N z := by positivity
    linarith
  have hΓN : 5 / 4 + (N : ℝ) ^ ε₁ * φ N z ≤ (N : ℝ) ^ ((1 : ℝ) / 6) := by
    have a1 : (N : ℝ) ^ (δ₀ + ε₁) ≤ (N : ℝ) ^ ((5 : ℝ) / 36) :=
      Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
    have a2 : 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 36) := hN₃ N hN3
    have a3 : (N : ℝ) ^ ((1 : ℝ) / 36) ≤ (N : ℝ) ^ ((5 : ℝ) / 36) :=
      Real.rpow_le_rpow_of_exponent_le hNr1 (by norm_num)
    have a4 : (N : ℝ) ^ ((1 : ℝ) / 6) = (N : ℝ) ^ ((5 : ℝ) / 36) * (N : ℝ) ^ ((1 : ℝ) / 36) := by
      rw [← Real.rpow_add hNr0]; norm_num
    rw [a4]; nlinarith
  have hΥ1 : z.im ≤ 41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im +
      (N : ℝ) ^ ε₁ * φ N z := by
    have : 0 ≤ (N : ℝ) ^ ε₁ * φ N z := by positivity
    linarith
  have hΥ2 : 41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im +
      (N : ℝ) ^ ε₁ * φ N z ≤ (N : ℝ) * z.im := by
    have b1 : z.im ≤ (N : ℝ) ^ (δ₀ + ε₁) := (Complex.im_le_norm z).trans
      (hzn0.trans (Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)))
    have b2 : 1 ≤ (N : ℝ) ^ (δ₀ + ε₁) := Real.one_le_rpow hNr1 (by positivity)
    have b3 : (N : ℝ) ^ (δ₀ + ε₁) ≤ (N : ℝ) ^ (τ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hNr1 hδε
    have b4 : 6 ≤ (N : ℝ) ^ (τ / 2) := hN₄ N hN4
    have b5 : (N : ℝ) ^ τ ≤ (N : ℝ) * z.im := by
      have : (N : ℝ) ^ τ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := by
        rw [← Real.rpow_one_add' hNr0.le (by linarith)]; ring_nf
      rw [this]; exact mul_le_mul_of_nonneg_left hzim0 hNr0.le
    have b6 : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_add hNr0]; ring_nf
    nlinarith
  set ϖφ := (1 + ‖z‖) ^ 2 * (1 + φ N z) ^ 4 *
    Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im)) ^ 3 with hϖφ
  have hbQz : ϖφ ≤ bQ N z := hbQ N z hzZ
  have hϖφ0 : (N : ℝ) ^ (-(3 : ℝ) / 2) ≤ ϖφ :=
    QSI_varpi_ge (1 + ‖z‖) (φ N z) z.im _ (N : ℝ) (by linarith [norm_nonneg z]) hφ0 hz him0 hNr0
  have hNm : 0 < (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hNr0 _
  have ht11 : t ^ 11 ≤ (N : ℝ) ^ ε₂ := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hNr0.le]
    exact Real.rpow_le_rpow_of_exponent_le hNr1 (by push_cast; linarith)
  have hvp := QSI_varpi_le (1 + ‖z‖) (φ N z) z.im (mExt (lam D N (A N)) z).im (N : ℝ) t hφ0 hz
    him0 hNr0 ht1
  rw [ht2] at hvp
  have hϖ' : (1 + ‖z‖) ^ 2 * (5 / 4 + (N : ℝ) ^ ε₁ * φ N z) ^ 4 *
      Real.sqrt ((41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im +
        (N : ℝ) ^ ε₁ * φ N z) / ((N : ℝ) * z.im)) ^ 3 ≤ 11 * (N : ℝ) ^ ε₂ * ϖφ := by
    refine hvp.trans ?_
    have : 0 ≤ ϖφ := hNm.le.trans hϖφ0
    gcongr
  have hϖ : (1 + ‖z‖) ^ 2 * (5 / 4 + (N : ℝ) ^ ε₁ * φ N z) ^ 4 *
      Real.sqrt ((41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im +
        (N : ℝ) ^ ε₁ * φ N z) / ((N : ℝ) * z.im)) ^ 3 ≤ 11 * (N : ℝ) ^ ε₂ * bQ N z :=
    hϖ'.trans (by gcongr)
  -- the bad event
  have hbQ0 : 0 ≤ bQ N z := (hNm.le.trans hϖφ0).trans hbQz
  have hbQle : (N : ℝ) ^ ε₂ * bQ N z ≤ 11 * (N : ℝ) ^ ε₂ * bQ N z := by
    have : 0 ≤ (N : ℝ) ^ ε₂ * bQ N z := by positivity
    linarith
  have hV := QSI_avgVecs_norm (lam D N (A N)) B hΛn hB
  have hg := hN₁ N hN1 z ⟨hzZ, hz⟩ (avgVecs D N (lam D N (A N)) B) hV
  have hq : ∀ kl : Idx D N × Idx D N, μ N {h | (N : ℝ) ^ ε₂ * bQ N z <
      ‖qMat D N (θ N) (Matrix.of h) (lam D N (A N)) B z kl.1 kl.2‖} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D'')) := fun kl => hN₂ N hN2 (⟨z, hzZ⟩, ⟨B, hB⟩, kl.1, kl.2)
  have hsub : (avgGood D N (θ N) (lam D N (A N)) B z (5 / 4 + (N : ℝ) ^ ε₁ * φ N z)
      (41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im + (N : ℝ) ^ ε₁ * φ N z)
      (11 * (N : ℝ) ^ ε₂ * bQ N z))ᶜ ⊆
      (goodSet (lam D N (A N)) z (avgVecs D N (lam D N (A N)) B)
        (5 / 4 + (N : ℝ) ^ ε₁ * φ N z)
        (41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im + (N : ℝ) ^ ε₁ * φ N z))ᶜ ∪
      ⋃ kl : Idx D N × Idx D N, {h | (N : ℝ) ^ ε₂ * bQ N z <
        ‖qMat D N (θ N) (Matrix.of h) (lam D N (A N)) B z kl.1 kl.2‖} := by
    intro h hh
    by_cases h1 : h ∈ goodSet (lam D N (A N)) z (avgVecs D N (lam D N (A N)) B)
        (5 / 4 + (N : ℝ) ^ ε₁ * φ N z)
        (41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im + (N : ℝ) ^ ε₁ * φ N z)
    · right
      have h2 : ¬ ∀ k' l', ‖qMat D N (θ N) (Matrix.of h) (lam D N (A N)) B z k' l'‖ ≤
          11 * (N : ℝ) ^ ε₂ * bQ N z := fun h2 => hh ⟨h1, h2⟩
      push Not at h2
      obtain ⟨k', l', hlt⟩ := h2
      exact Set.mem_iUnion.2 ⟨(k', l'), lt_of_le_of_lt hbQle hlt⟩
    · left; exact h1
  have hcardV := QSI_card_avgVecs D N (lam D N (A N)) B
  have hDN0 : (0 : ℝ) ≤ (D : ℝ) * N := by positivity
  have hNd : 0 ≤ (N : ℝ) ^ (-D'') := by positivity
  have hbad : μ N (avgGood D N (θ N) (lam D N (A N)) B z (5 / 4 + (N : ℝ) ^ ε₁ * φ N z)
      (41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im + (N : ℝ) ^ ε₁ * φ N z)
      (11 * (N : ℝ) ^ ε₂ * bQ N z))ᶜ ≤
      ENNReal.ofReal (17 * (D : ℝ) ^ 2 * (N : ℝ) ^ 2 * (N : ℝ) ^ (-D'')) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have hU : μ N (⋃ kl : Idx D N × Idx D N, {h | (N : ℝ) ^ ε₂ * bQ N z <
        ‖qMat D N (θ N) (Matrix.of h) (lam D N (A N)) B z kl.1 kl.2‖}) ≤
        ENNReal.ofReal (((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'')) := by
      refine (measure_iUnion_fintype_le _ _).trans ?_
      refine (Finset.sum_le_sum fun kl _ => hq kl).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hNd)]
      congr 1
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    refine (add_le_add hg hU).trans ?_
    have hn1 : 0 ≤ ((avgVecs D N (lam D N (A N)) B).card : ℝ) ^ 2 * (N : ℝ) ^ (-D'') := by
      positivity
    have hn2 : 0 ≤ ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'') := by positivity
    rw [← ENNReal.ofReal_add hn1 hn2]
    refine ENNReal.ofReal_le_ofReal ?_
    have hc2 : ((avgVecs D N (lam D N (A N)) B).card : ℝ) ^ 2 ≤ 16 * ((D : ℝ) * N) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ((avgVecs D N (lam D N (A N)) B).card : ℝ) := Nat.cast_nonneg _
      calc ((avgVecs D N (lam D N (A N)) B).card : ℝ) ^ 2 ≤ (4 * ((D : ℝ) * N)) ^ 2 :=
            pow_le_pow_left₀ h0 hcardV 2
        _ = 16 * ((D : ℝ) * N) ^ 2 := by ring
    have h3 := mul_le_mul_of_nonneg_right hc2 hNd
    have e : 17 * (D : ℝ) ^ 2 * (N : ℝ) ^ 2 * (N : ℝ) ^ (-D'') =
        16 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'') + ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D'') := by
      ring
    rw [e]
    exact add_le_add h3 le_rfl
  -- the round
  have hYpos : (N : ℝ) ^ (-(3 : ℝ)) ≤ ϖφ * bQ N z := by
    have e : (N : ℝ) ^ (-(3 : ℝ)) = (N : ℝ) ^ (-(3 : ℝ) / 2) * (N : ℝ) ^ (-(3 : ℝ) / 2) := by
      rw [← Real.rpow_add hNr0]; norm_num
    rw [e]
    exact mul_le_mul hϖφ0 (hϖφ0.trans hbQz) hNm.le (hNm.le.trans hϖφ0)
  have hY0 : 0 < ϖφ * bQ N z := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr0 _) hYpos
  have hs : 0 < (N : ℝ) ^ τ' * (ϖφ * bQ N z) ^ ((1 : ℝ) / 2) :=
    mul_pos (Real.rpow_pos_of_pos hNr0 _) (Real.rpow_pos_of_pos hY0 _)
  have hr := hK N (θ N) (μ N) (hseq.mem N) (hseq.theta N).1 (hseq.theta N).2 (lam D N (A N)) hΛ
    hΛn B hB z hzN hzn (5 / 4 + (N : ℝ) ^ ε₁ * φ N z)
    (41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im + (N : ℝ) ^ ε₁ * φ N z)
    (11 * (N : ℝ) ^ ε₂ * bQ N z) (17 * (D : ℝ) ^ 2 * (N : ℝ) ^ 2 * (N : ℝ) ^ (-D''))
    hΓ1 hΓN hΥ1 hΥ2 hϖ hbad k l _ hs
  refine hr.trans (ENNReal.ofReal_le_ofReal ?_)
  have hW0 : 0 ≤ (1 + ‖z‖) ^ 2 * (5 / 4 + (N : ℝ) ^ ε₁ * φ N z) ^ 4 *
      Real.sqrt ((41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im +
        (N : ℝ) ^ ε₁ * φ N z) / ((N : ℝ) * z.im)) ^ 3 * (11 * (N : ℝ) ^ ε₂ * bQ N z) := by
    have h1 : (0 : ℝ) ≤ (1 + ‖z‖) ^ 2 * (5 / 4 + (N : ℝ) ^ ε₁ * φ N z) ^ 4 *
      Real.sqrt ((41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im +
        (N : ℝ) ^ ε₁ * φ N z) / ((N : ℝ) * z.im)) ^ 3 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by have := mul_nonneg (Real.rpow_nonneg hNr0.le ε₁) hφ0; linarith) 4))
        (pow_nonneg (Real.sqrt_nonneg _) 3)
    exact mul_nonneg h1 (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hNr0.le _)) hbQ0)
  have hWb : (1 + ‖z‖) ^ 2 * (5 / 4 + (N : ℝ) ^ ε₁ * φ N z) ^ 4 *
      Real.sqrt ((41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im +
        (N : ℝ) ^ ε₁ * φ N z) / ((N : ℝ) * z.im)) ^ 3 * (11 * (N : ℝ) ^ ε₂ * bQ N z) ≤
      198 * (N : ℝ) ^ τ' * (ϖφ * bQ N z) := by
    have e : (N : ℝ) ^ τ' = (N : ℝ) ^ ε₂ * (N : ℝ) ^ ε₂ := by
      rw [← Real.rpow_add hNr0, hε₂]; ring_nf
    calc _ ≤ (11 * (N : ℝ) ^ ε₂ * ϖφ) * (11 * (N : ℝ) ^ ε₂ * bQ N z) :=
          mul_le_mul_of_nonneg_right hϖ'
            (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hNr0.le _)) hbQ0)
      _ = 121 * (N : ℝ) ^ τ' * (ϖφ * bQ N z) := by rw [e]; ring
      _ ≤ 198 * (N : ℝ) ^ τ' * (ϖφ * bQ N z) := by gcongr; norm_num
  have ha := QSI_round_arith (N : ℝ) hNr1 p τ' D' K (D : ℝ) (ϖφ * bQ N z) _ hK0 (Nat.cast_nonneg _)
    hτ' hpτ hYpos hW0 hWb
  refine ha.trans ?_
  have h6 := hN₆ N hN6
  rw [Real.rpow_one] at h6
  have e : (N : ℝ) ^ (-D') = (N : ℝ) * (N : ℝ) ^ (-(D' + 1)) := by
    rw [show -D' = 1 + -(D' + 1) by ring, Real.rpow_add hNr0, Real.rpow_one]
  rw [e]
  exact mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hNr0.le _)


private lemma QSI_precS_congr {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    {U : ℕ → Type*} (ξ ζ₁ ζ₂ : ∀ N, U N → Ω N → ℝ) (h : ∀ N u x₀, ζ₁ N u x₀ = ζ₂ N u x₀)
    (h1 : PrecS P ξ ζ₁) : PrecS P ξ ζ₂ := by
  have : ζ₁ = ζ₂ := funext fun N => funext fun u => funext fun x₀ => h N u x₀
  rw [← this]; exact h1

/-- `(W · N^x W)^{1/2} = N^{x/2} W`. -/
private lemma QSI_sqrt_step (Nr x W : ℝ) (hN : 0 ≤ Nr) (hW : 0 ≤ W) :
    (W * (Nr ^ x * W)) ^ ((1 : ℝ) / 2) = Nr ^ (x / 2) * W := by
  rw [show W * (Nr ^ x * W) = Nr ^ x * W ^ 2 by ring,
    Real.mul_rpow (Real.rpow_nonneg hN _) (by positivity), ← Real.rpow_mul hN,
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hW]
  congr 2; ring

private lemma QSI_lam_small (D N : ℕ) (hD1 : 1 ≤ D) (hN : 1 ≤ N) (δA : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : opNorm A ≤ (N : ℝ) ^ (-δA)) (h5 : 20 * (D : ℝ) ^ 2 ≤ (N : ℝ) ^ δA) :
    opNorm (lam D N A) ≤ 1 / 10 := by
  have hNr0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := QSI_opNorm_lam D N hN A
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hD0 : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  have hpos : 0 < (N : ℝ) ^ δA := Real.rpow_pos_of_pos hNr0 _
  calc opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := h1
    _ ≤ 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ (-δA) := by gcongr
    _ ≤ 1 / 10 := by
      rw [Real.rpow_neg hNr0.le, ← div_eq_mul_inv, div_le_iff₀ hpos]
      linarith

/-- The start of the self-improvement: the bound on `|Q|` on the good event against
`N^{1/2} ϖ_φ`. -/
private lemma QSI_base_le (Z0 φ η im Nr T c : ℝ) (hZ0 : 1 ≤ Z0) (hφ : 0 ≤ φ) (hη : 0 < η)
    (him : 0 ≤ im) (hN : 0 < Nr) (hT : 1 ≤ T) (hc : 0 ≤ c) :
    c * Z0 * (5 / 4 + T * φ) ^ (0 + 0 + 1) * ((41 / 16 * η + 25 / 16 * im + T * φ) / (Nr * η)) ≤
      4 * c * T ^ 2 * (Nr ^ ((1 : ℝ) / 2) *
        (Z0 ^ 2 * (1 + φ) ^ 4 * Real.sqrt ((im + φ + η) / (Nr * η)) ^ 3)) := by
  have hNη : 0 < Nr * η := mul_pos hN hη
  set X := (im + φ + η) / (Nr * η) with hX
  have hX0 : 0 ≤ X := by positivity
  have hXN : Nr⁻¹ ≤ X := by rw [hX, le_div_iff₀ hNη]; field_simp; linarith
  have hΓ : 5 / 4 + T * φ ≤ 5 / 4 * T * (1 + φ) := by nlinarith
  have hΥ : (41 / 16 * η + 25 / 16 * im + T * φ) / (Nr * η) ≤ 41 / 16 * T * X := by
    rw [hX, div_le_iff₀ hNη]
    rw [show 41 / 16 * T * ((im + φ + η) / (Nr * η)) * (Nr * η) = 41 / 16 * T * (im + φ + η) by
      field_simp]
    nlinarith
  have hsX : 1 ≤ Nr ^ ((1 : ℝ) / 2) * Real.sqrt X := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul hN.le]
    rw [Real.one_le_sqrt]
    calc (1 : ℝ) = Nr * Nr⁻¹ := (mul_inv_cancel₀ hN.ne').symm
      _ ≤ Nr * X := mul_le_mul_of_nonneg_left hXN hN.le
  have hS3 : Real.sqrt X ^ 3 = X * Real.sqrt X := by
    rw [pow_succ, pow_two, Real.mul_self_sqrt hX0]
  have hb1 : 1 ≤ (1 + φ) ^ 3 := one_le_pow₀ (by linarith)
  have hZ1 : 1 ≤ Z0 := hZ0
  have hW : Z0 * (1 + φ) * X ≤ Nr ^ ((1 : ℝ) / 2) *
      (Z0 ^ 2 * (1 + φ) ^ 4 * Real.sqrt X ^ 3) := by
    rw [hS3]
    have e : Nr ^ ((1 : ℝ) / 2) * (Z0 ^ 2 * (1 + φ) ^ 4 * (X * Real.sqrt X)) =
        (Z0 * (1 + φ) * X) * (Z0 * (1 + φ) ^ 3 * (Nr ^ ((1 : ℝ) / 2) * Real.sqrt X)) := by ring
    rw [e]
    have h1 : 1 ≤ Z0 * (1 + φ) ^ 3 * (Nr ^ ((1 : ℝ) / 2) * Real.sqrt X) := by
      have := mul_le_mul hZ1 hb1 zero_le_one (by linarith)
      nlinarith
    have h0 : 0 ≤ Z0 * (1 + φ) * X := by
      have : 0 ≤ Z0 := by linarith
      positivity
    nlinarith
  have h1 : c * Z0 * (5 / 4 + T * φ) ^ (0 + 0 + 1) *
      ((41 / 16 * η + 25 / 16 * im + T * φ) / (Nr * η)) ≤
      c * Z0 * (5 / 4 * T * (1 + φ)) * (41 / 16 * T * X) := by
    rw [pow_one]
    have : 0 ≤ c * Z0 := mul_nonneg hc (by linarith)
    have h5 : 0 ≤ 5 / 4 + T * φ := by have := mul_nonneg (by linarith : (0 : ℝ) ≤ T) hφ; linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hΓ this) hΥ (by positivity)
      (mul_nonneg this (by have : (0 : ℝ) ≤ T := by linarith
                           positivity))
  refine h1.trans ?_
  have e : c * Z0 * (5 / 4 * T * (1 + φ)) * (41 / 16 * T * X) =
      (205 / 64) * c * T ^ 2 * (Z0 * (1 + φ) * X) := by ring
  rw [e]
  have hcT : 0 ≤ c * T ^ 2 := by positivity
  calc 205 / 64 * c * T ^ 2 * (Z0 * (1 + φ) * X) ≤
      205 / 64 * c * T ^ 2 * (Nr ^ ((1 : ℝ) / 2) * (Z0 ^ 2 * (1 + φ) ^ 4 * Real.sqrt X ^ 3)) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ ≤ 4 * c * T ^ 2 * (Nr ^ ((1 : ℝ) / 2) * (Z0 ^ 2 * (1 + φ) ^ 4 * Real.sqrt X ^ 3)) := by
        have : 0 ≤ Nr ^ ((1 : ℝ) / 2) * (Z0 ^ 2 * (1 + φ) ^ 4 * Real.sqrt X ^ 3) := by
          have : 0 ≤ Z0 := by linarith
          positivity
        nlinarith

set_option maxHeartbeats 1000000 in
/-- `Q_{kl} ≺ N^{1/2} ϖ_φ` from the a priori bound. -/
private lemma QSI_prec_base (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hseq : LLSeq D δA C θ μ A) (Z : ℕ → Set ℂ)
    (hZ : ∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im)
    (φ : ℕ → ℂ → ℝ) (hφ : ∀ N, ∀ z ∈ Z N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀)
    (hLL : aprioriLL D μ A Z φ) :
    PrecS μ (U := fun N => {z // z ∈ Z N} ×
        {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1} × Idx D N × Idx D N)
      (fun N w h => ‖qMat D N (θ N) (Matrix.of h) (lam D N (A N)) w.2.1.1 w.1.1 w.2.2.1
        w.2.2.2‖)
      (fun N w _ => (N : ℝ) ^ ((1 : ℝ) / 2) * ((1 + ‖w.1.1‖) ^ 2 * (1 + φ N w.1.1) ^ 4 *
        Real.sqrt (((mExt (lam D N (A N)) w.1.1).im + φ N w.1.1 + w.1.1.im) /
          ((N : ℝ) * w.1.1.im)) ^ 3)) := by
  intro τ₀ hτ₀ D₀ hD₀
  have hD1 : 1 ≤ D := hseq.one_le_D
  obtain ⟨c₀, hc₀0, hc₀⟩ := qMat_wirt_le D 0 0
  set ε₁ := τ₀ / 4 with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨N₁, hN₁⟩ := apriori_good D δA C θ μ A hseq (fun N => {z | z ∈ Z N ∧ 0 < z.im})
    (fun N z hz => hz.2) φ (QSI_apriori_restrict hLL) ε₁ (D₀ + 3) hε₁0 (by linarith)
  obtain ⟨N₂, hN₂⟩ := QSI_ev_le (4 * c₀) (τ₀ / 2) (by positivity)
  obtain ⟨N₃, hN₃⟩ := QSI_ev_le (20 * (D : ℝ) ^ 2) δA hseq.pos
  obtain ⟨N₄, hN₄⟩ := QSI_ev_le (16 * (D : ℝ) ^ 2) 1 one_pos
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) 2), fun N hN u => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨hN1, hN2⟩, ⟨hN3, hN4⟩, hN7⟩ := hN
  obtain ⟨⟨z, hzZ⟩, ⟨B, hB⟩, k, l⟩ := u
  dsimp only
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNr0 : (0 : ℝ) < N := by linarith
  obtain ⟨hzn0, hzim0⟩ := hZ N z hzZ
  have hz : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr0 _) hzim0
  have hΛ : (lam D N (A N)).IsHermitian := lam_isHermitian D N (A N)
  have hΛn : opNorm (lam D N (A N)) ≤ 1 / 10 :=
    QSI_lam_small D N hD1 (by omega) δA (A N) (hseq.small N) (hN₃ N hN3)
  have : Nonempty (Idx D N) := ⟨k⟩
  have hme : mExt (lam D N (A N)) z = mSol (lam D N (A N)) z := by simp [mExt, hz]
  have him0 : 0 ≤ (mExt (lam D N (A N)) z).im := by
    rw [hme]; exact (mSol_spec (lam D N (A N)) hΛ z hz).1.le
  obtain ⟨hφ1, hφ2⟩ := hφ N z hzZ
  have hφ0 : 0 ≤ φ N z := le_trans (by positivity) hφ1
  have hNε1 : 1 ≤ (N : ℝ) ^ ε₁ := Real.one_le_rpow hNr1 hε₁0.le
  have hT2 : ((N : ℝ) ^ ε₁) ^ 2 = (N : ℝ) ^ (τ₀ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr0.le]; congr 1; rw [hε₁]; push_cast; ring
  set W := (1 + ‖z‖) ^ 2 * (1 + φ N z) ^ 4 *
    Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im)) ^ 3 with hW
  have hW0 : 0 ≤ W := by positivity
  have hV := QSI_avgVecs_norm (lam D N (A N)) B hΛn hB
  have hg := hN₁ N hN1 z ⟨hzZ, hz⟩ (avgVecs D N (lam D N (A N)) B) hV
  have hsub : {h : Idx D N → Idx D N → ℂ | (N : ℝ) ^ τ₀ * ((N : ℝ) ^ ((1 : ℝ) / 2) * W) <
      ‖qMat D N (θ N) (Matrix.of h) (lam D N (A N)) B z k l‖} ⊆
      {h | ¬ (Matrix.of h).IsHermitian} ∪
      (goodSet (lam D N (A N)) z (avgVecs D N (lam D N (A N)) B)
        (5 / 4 + (N : ℝ) ^ ε₁ * φ N z)
        (41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im + (N : ℝ) ^ ε₁ * φ N z))ᶜ := by
    intro h hlt
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff, not_or, not_not] at hc
    obtain ⟨hh, hgood⟩ := hc
    have hΓ1 : 1 ≤ 5 / 4 + (N : ℝ) ^ ε₁ * φ N z := by
      have : 0 ≤ (N : ℝ) ^ ε₁ * φ N z := by positivity
      linarith
    have hΥ1 : z.im ≤ 41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im +
        (N : ℝ) ^ ε₁ * φ N z := by
      have : 0 ≤ (N : ℝ) ^ ε₁ * φ N z := by positivity
      linarith
    have hb := hc₀ N (θ N) (hseq.theta N).1 (hseq.theta N).2 (lam D N (A N)) hΛ hΛn B hB z hz h
      hh k k (h k k) k l _ _ hΓ1 hΥ1 (by rw [QSI_setEntry_self h hh k k]; exact hgood)
    simp only [wirt, Function.iterate_zero, id, QSI_setEntry_self h hh k k] at hb
    have hb2 := QSI_base_le (1 + ‖z‖) (φ N z) z.im (mExt (lam D N (A N)) z).im (N : ℝ)
      ((N : ℝ) ^ ε₁) c₀ (by linarith [norm_nonneg z]) hφ0 hz him0 hNr0 hNε1 hc₀0
    rw [hT2] at hb2
    have h4c := hN₂ N hN2
    have hNτ : (N : ℝ) ^ τ₀ = (N : ℝ) ^ (τ₀ / 2) * (N : ℝ) ^ (τ₀ / 2) := by
      rw [← Real.rpow_add hNr0]; ring_nf
    have hX0 : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * W := by positivity
    have h5 : 4 * c₀ * (N : ℝ) ^ (τ₀ / 2) * ((N : ℝ) ^ ((1 : ℝ) / 2) * W) ≤
        (N : ℝ) ^ τ₀ * ((N : ℝ) ^ ((1 : ℝ) / 2) * W) := by
      rw [hNτ]
      have : 0 ≤ (N : ℝ) ^ (τ₀ / 2) := by positivity
      have := mul_le_mul_of_nonneg_right h4c this
      have := mul_le_mul_of_nonneg_right this hX0
      linarith
    have := (hb.trans hb2).trans h5
    exact absurd hlt (not_lt.2 this)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hnull : μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := ae_iff.mp (hseq.mem N).herm
  rw [hnull, zero_add]
  refine hg.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcardV := QSI_card_avgVecs D N (lam D N (A N)) B
  have h0 : (0 : ℝ) ≤ ((avgVecs D N (lam D N (A N)) B).card : ℝ) := Nat.cast_nonneg _
  have hc2 : ((avgVecs D N (lam D N (A N)) B).card : ℝ) ^ 2 ≤ 16 * ((D : ℝ) * N) ^ 2 :=
    calc ((avgVecs D N (lam D N (A N)) B).card : ℝ) ^ 2 ≤ (4 * ((D : ℝ) * N)) ^ 2 :=
          pow_le_pow_left₀ h0 hcardV 2
      _ = 16 * ((D : ℝ) * N) ^ 2 := by ring
  have h16 := hN₄ N hN4
  rw [Real.rpow_one] at h16
  have e : (N : ℝ) ^ (-(D₀ + 3)) = (N : ℝ) ^ (-D₀) * ((N : ℝ) ^ 2 * N)⁻¹ := by
    rw [show -(D₀ + 3) = -D₀ + -3 by ring, Real.rpow_add hNr0, Real.rpow_neg hNr0.le (3 : ℝ)]
    congr 2
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  rw [e]
  have hNd : 0 ≤ (N : ℝ) ^ (-D₀) := Real.rpow_nonneg hNr0.le _
  calc ((avgVecs D N (lam D N (A N)) B).card : ℝ) ^ 2 * ((N : ℝ) ^ (-D₀) * ((N : ℝ) ^ 2 * N)⁻¹)
      ≤ 16 * ((D : ℝ) * N) ^ 2 * ((N : ℝ) ^ (-D₀) * ((N : ℝ) ^ 2 * N)⁻¹) :=
        mul_le_mul_of_nonneg_right hc2 (by positivity)
    _ = (16 * (D : ℝ) ^ 2) * ((N : ℝ))⁻¹ * (N : ℝ) ^ (-D₀) := by field_simp
    _ ≤ (N : ℝ) * ((N : ℝ))⁻¹ * (N : ℝ) ^ (-D₀) := by gcongr
    _ = (N : ℝ) ^ (-D₀) := by field_simp

/-- `Q_{kl} ≺ (1 + |z|)² (1 + φ)⁴ ((Im m + φ + η)/(Nη))^{3/2}` in sup form over `z ∈ Z_N`,
`‖B‖ ≤ 1` and `k, l`, under `LLSeq`, `10 δ₀ ≤ τ` and `aprioriLL`
(Definition 2.8 [stoch_domination]). -/
theorem q_prec :
    ∀ (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
      (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ),
      LLSeq D δA C θ μ A → 0 < τ → 0 ≤ δ₀ → 10 * δ₀ ≤ τ →
    ∀ Z : ℕ → Set ℂ, (∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im) →
    ∀ φ : ℕ → ℂ → ℝ, (∀ N, ∀ z ∈ Z N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀) →
    aprioriLL D μ A Z φ →
    PrecS μ (U := fun N => {z // z ∈ Z N} ×
        {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1} × Idx D N × Idx D N)
      (fun N w h => ‖qMat D N (θ N) (Matrix.of h) (lam D N (A N)) w.2.1.1 w.1.1 w.2.2.1
        w.2.2.2‖)
      (fun N w _ => (1 + ‖w.1.1‖) ^ 2 * (1 + φ N w.1.1) ^ 4 *
        Real.sqrt (((mExt (lam D N (A N)) w.1.1).im + φ N w.1.1 + w.1.1.im) /
          ((N : ℝ) * w.1.1.im)) ^ 3) := by
  intro D δA τ δ₀ C θ μ A hseq hτ hδ₀ h10 Z hZ φ hφ hLL
  set W : ℕ → ℂ → ℝ := fun N z => (1 + ‖z‖) ^ 2 * (1 + φ N z) ^ 4 *
    Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im)) ^ 3 with hWdef
  have hW0 : ∀ N z, 0 ≤ W N z := fun N z => by simp only [hWdef]; positivity
  have hrounds : ∀ r : ℕ, PrecS μ (U := fun N => {z // z ∈ Z N} ×
        {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1} × Idx D N × Idx D N)
      (fun N w h => ‖qMat D N (θ N) (Matrix.of h) (lam D N (A N)) w.2.1.1 w.1.1 w.2.2.1
        w.2.2.2‖)
      (fun N w _ => (N : ℝ) ^ ((1 / 2 : ℝ) ^ (r + 1)) * W N w.1.1) := by
    intro r
    induction r with
    | zero =>
      refine QSI_precS_congr _ _ _ _ (fun N u x₀ => ?_)
        (QSI_prec_base D δA τ δ₀ C θ μ A hseq Z hZ φ hφ hLL)
      rw [zero_add, pow_one]
    | succ r ih =>
      have hb : ∀ N, ∀ z ∈ Z N, (1 + ‖z‖) ^ 2 * (1 + φ N z) ^ 4 *
          Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im)) ^ 3 ≤
          (N : ℝ) ^ ((1 / 2 : ℝ) ^ (r + 1)) * W N z := by
        intro N z _
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · simp
        · exact le_mul_of_one_le_left (hW0 N z)
            (Real.one_le_rpow (by exact_mod_cast hN) (by positivity))
      have := q_self_improv D δA τ δ₀ C θ μ A hseq hτ hδ₀ h10 Z hZ φ hφ hLL
        (fun N z => (N : ℝ) ^ ((1 / 2 : ℝ) ^ (r + 1)) * W N z) hb ih
      refine QSI_precS_congr _ _ _ _ (fun N u x₀ => ?_) this
      show (W N u.1.1 * ((N : ℝ) ^ ((1 / 2 : ℝ) ^ (r + 1)) * W N u.1.1)) ^ ((1 : ℝ) / 2) =
        (N : ℝ) ^ ((1 / 2 : ℝ) ^ (r + 1 + 1)) * W N u.1.1
      rw [QSI_sqrt_step _ _ _ (Nat.cast_nonneg _) (hW0 _ _)]
      congr 2
      rw [pow_succ]; ring
  intro τ'' hτ'' D' hD'
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (1 / 2 : ℝ) ^ (r + 1) ≤ τ'' / 2 := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < τ'' / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)).trans hn.le⟩
  obtain ⟨N₀, hN₀⟩ := hrounds r (τ'' / 2) (by positivity) D' hD'
  refine ⟨max N₀ 1, fun N hN u => le_trans (measure_mono ?_) (hN₀ N (le_of_max_le_left hN) u)⟩
  intro h hlt
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hN0 : (0 : ℝ) < N := by linarith
  show (N : ℝ) ^ (τ'' / 2) * ((N : ℝ) ^ ((1 / 2 : ℝ) ^ (r + 1)) * W N u.1.1) < _
  have hle : (N : ℝ) ^ (τ'' / 2) * (N : ℝ) ^ ((1 / 2 : ℝ) ^ (r + 1)) ≤ (N : ℝ) ^ τ'' := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc (N : ℝ) ^ (τ'' / 2) * ((N : ℝ) ^ ((1 / 2 : ℝ) ^ (r + 1)) * W N u.1.1) =
      ((N : ℝ) ^ (τ'' / 2) * (N : ℝ) ^ ((1 / 2 : ℝ) ^ (r + 1))) * W N u.1.1 := by ring
    _ ≤ (N : ℝ) ^ τ'' * W N u.1.1 := mul_le_mul_of_nonneg_right hle (hW0 _ _)
    _ < _ := hlt

end RBMTransitionEdge

end
