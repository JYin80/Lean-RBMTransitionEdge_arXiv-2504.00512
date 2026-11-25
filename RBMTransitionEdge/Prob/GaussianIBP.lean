module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Prob.Cumulant
public import RBMTransitionEdge.Prob.Gaussian

@[expose] public section

/-!
# Gaussian integration by parts

The Wirtinger and real derivatives on block arrays, the Gaussian Laplacian,
integration by parts for the GUE blocks and for the complex Gaussian, its cumulants, and the
derivative of OU expectations used for the single-time laws of §3 and §4.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `e_i` (diagonal), `e_{ij}` and `i e_{ij}` (array) coordinate vectors of block `a`. -/
def bD {D N : ℕ} (a : Fin D) (i : Fin N) : Fin D → Coords N :=
  Pi.single a (Pi.single i 1, 0)

/-- The real array coordinate vector of block `a`. -/
def bRe {D N : ℕ} (a : Fin D) (i j : Fin N) : Fin D → Coords N :=
  Pi.single a (0, Pi.single i (Pi.single j 1))

/-- The imaginary array coordinate vector of block `a`. -/
def bIm {D N : ℕ} (a : Fin D) (i j : Fin N) : Fin D → Coords N :=
  Pi.single a (0, Pi.single i (Pi.single j Complex.I))

/-- The second derivative `D²F(w)[v, v]`. -/
def d2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → ℂ) (w v : V) : ℂ :=
  fderiv ℝ (fun y => fderiv ℝ F y v) w v

/-- The Gaussian Laplacian `E D²F(w)[X, X]` for `X ∼ gueBlocks D N`, in coordinates. -/
def gLap {D N : ℕ} (F : (Fin D → Coords N) → ℂ) (w : Fin D → Coords N) : ℂ :=
  (∑ a, ∑ i, d2 F w (bD a i)) + (1 / 2 : ℂ) * ∑ a, ∑ i, ∑ j, (d2 F w (bRe a i j) + d2 F w (bIm a i j))

open scoped NNReal ENNReal

/-- `μ` integrates by parts in the direction `e` against the coordinate `ℓ` with variance `v`. -/
private def ibpDir {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    (μ : Measure V) (ℓ : V →L[ℝ] ℝ) (e : V) (v : ℝ) : Prop :=
  ∀ G : V → ℂ, ContDiff ℝ 1 G → Integrable G μ → Integrable (fun x => (ℓ x : ℂ) * G x) μ →
    Integrable (fun x => fderiv ℝ G x e) μ →
    ∫ x, (ℓ x : ℂ) * G x ∂μ = (v : ℂ) * ∫ x, fderiv ℝ G x e ∂μ

/-- `f` is integrable for `N(0, v)` iff `φ_v f` is integrable for Lebesgue measure. -/
private lemma ibp_gaussian_integrable_iff (v : ℝ≥0) (hv : v ≠ 0) (f : ℝ → ℂ) :
    Integrable f (gaussianReal 0 v) ↔
      Integrable (fun x => gaussianPDFReal 0 v x • f x) volume := by
  rw [gaussianReal_of_var_ne_zero 0 hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 v)
      (Filter.Eventually.of_forall fun x => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF]

/-- The Gaussian density has derivative `-(x / v) φ_v(x)`. -/
private lemma ibp_hasDerivAt_pdf (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (fun y => ((gaussianPDFReal 0 v y : ℝ) : ℂ))
      (((-(x / v) * gaussianPDFReal 0 v x : ℝ)) : ℂ) x := by
  have hv' : (0 : ℝ) < v := by positivity
  have h1 : HasDerivAt (fun y : ℝ => -(y - 0) ^ 2 / (2 * (v : ℝ))) (-(x) / v) x := by
    have := ((hasDerivAt_id x).sub_const 0).pow 2
    have h := (this.neg).div_const (2 * (v : ℝ))
    convert h using 1
    · simp
    · field_simp
      simp
      ring
  have h2 := (h1.exp).const_mul ((Real.sqrt (2 * Real.pi * v))⁻¹)
  have h3 : HasDerivAt (fun y => gaussianPDFReal 0 v y) (-(x / v) * gaussianPDFReal 0 v x) x := by
    convert h2 using 1
    · funext y; simp [gaussianPDFReal]
    · simp [gaussianPDFReal]; ring
  exact h3.ofReal_comp

/-- One-dimensional Gaussian integration by parts: `E X g(X) = v E g'(X)` for `X ∼ N(0, v)`, when
`g`, `x g` and `g'` are integrable. -/
private lemma ibp_gaussian_one (v : ℝ≥0) (hv : v ≠ 0) (g g' : ℝ → ℂ)
    (hg : ∀ x, HasDerivAt g (g' x) x) (h1 : Integrable g (gaussianReal 0 v))
    (h2 : Integrable (fun x : ℝ => (x : ℂ) * g x) (gaussianReal 0 v))
    (h3 : Integrable g' (gaussianReal 0 v)) :
    ∫ x : ℝ, (x : ℂ) * g x ∂gaussianReal 0 v = (v : ℂ) * ∫ x, g' x ∂gaussianReal 0 v := by
  have hv' : (0 : ℝ) < v := by positivity
  set φ : ℝ → ℂ := fun y => ((gaussianPDFReal 0 v y : ℝ) : ℂ) with hφ
  set φ' : ℝ → ℂ := fun x => (((-(x / v) * gaussianPDFReal 0 v x : ℝ)) : ℂ) with hφ'
  rw [ibp_gaussian_integrable_iff v hv] at h1 h2 h3
  have hsm : ∀ (y : ℝ) (z : ℂ), gaussianPDFReal 0 v y • z = φ y * z := fun y z => by
    simp [hφ, Complex.real_smul]
  simp only [hsm] at h1 h2 h3
  have e1 : (g * φ') = fun x => -((1 / (v : ℂ)) * (φ x * ((x : ℂ) * g x))) := by
    funext x
    simp only [Pi.mul_apply, hφ', hφ]
    push_cast
    field_simp
  have e2 : (g' * φ) = fun x => φ x * g' x := by
    funext x; simp [Pi.mul_apply, mul_comm]
  have e3 : (g * φ) = fun x => φ x * g x := by
    funext x; simp [Pi.mul_apply, mul_comm]
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (A := ℂ) (u := g) (v := φ)
    (u' := g') (v' := φ') (fun x _ => hg x) (fun x _ => ibp_hasDerivAt_pdf v hv x)
    (by rw [e1]; exact (h2.const_mul (1 / (v : ℂ))).neg)
    (by rw [e2]; exact h3) (by rw [e3]; exact h1)
  have hv0 : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  have L : ∀ f : ℝ → ℂ, ∫ x, f x ∂gaussianReal 0 v = ∫ x, φ x * f x := by
    intro f
    rw [integral_gaussianReal_eq_integral_smul hv]
    simp only [hsm]
  rw [L, L]
  have : ∫ x, g x * φ' x = ∫ x, -((1 / (v : ℂ)) * (φ x * ((x : ℂ) * g x))) := by
    exact congrArg (fun f : ℝ → ℂ => ∫ x, f x) e1
  rw [this, integral_neg, integral_const_mul] at key
  have hA : (1 / (v : ℂ)) * ∫ x, φ x * ((x : ℂ) * g x) = ∫ x, φ x * g' x := by
    have key' : ∫ x, g' x * φ x = ∫ x, φ x * g' x := by
      simp only [mul_comm]
    rw [key'] at key
    exact neg_injective key
  calc ∫ x, φ x * ((x : ℂ) * g x) = (v : ℂ) * ((1 / (v : ℂ)) * ∫ x, φ x * ((x : ℂ) * g x)) := by
        field_simp
    _ = (v : ℂ) * ∫ x, φ x * g' x := by rw [hA]

/-- `N(0, v)` integrates by parts against the identity coordinate with variance `v`. -/
private lemma ibpDir_gaussianReal (v : ℝ≥0) (hv : v ≠ 0) :
    ibpDir (gaussianReal 0 v) (ContinuousLinearMap.id ℝ ℝ) 1 (v : ℝ) := by
  intro G hG h1 h2 h3
  have hd : ∀ x, HasDerivAt G (fderiv ℝ G x 1) x := fun x =>
    ((hG.differentiable (by norm_num) x).hasFDerivAt).hasDerivAt
  simpa using ibp_gaussian_one v hv G (fun x => fderiv ℝ G x 1) hd h1 (by simpa using h2) h3

section Lifts

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]

/-- Integration by parts passes to a product measure in the first factor. -/
private lemma ibpDir_prod_left (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ℓ : X →L[ℝ] ℝ) (e : X) (v : ℝ) (h : ibpDir μ ℓ e v) :
    ibpDir (μ.prod ν) (ℓ.comp (ContinuousLinearMap.fst ℝ X Y)) (e, 0) v := by
  intro G hG h1 h2 h3
  have hs : ∀ b : Y, ContDiff ℝ 1 (fun y : X => G (y, b)) := fun b =>
    hG.comp (contDiff_id.prodMk contDiff_const)
  have hd : ∀ (b : Y) (y : X), fderiv ℝ (fun y : X => G (y, b)) y e = fderiv ℝ G (y, b) (e, 0) := by
    intro b y
    have h : HasFDerivAt (fun y : X => G (y, b))
        ((fderiv ℝ G (y, b)).comp (ContinuousLinearMap.inl ℝ X Y)) y :=
      ((hG.differentiable (by norm_num) (y, b)).hasFDerivAt).comp y
        (hasFDerivAt_prodMk_left y b)
    rw [h.fderiv]
    simp
  have a1 := h1.prod_left_ae
  have a2 := h2.prod_left_ae
  have a3 := h3.prod_left_ae
  rw [integral_prod_symm _ h2, integral_prod_symm _ h3]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst']
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [a1, a2, a3] with b b1 b2 b3
  have := h (fun y => G (y, b)) (hs b) b1 (by simpa using b2) (by simpa [hd] using b3)
  simpa [hd] using this

/-- Integration by parts passes to a product measure in the second factor. -/
private lemma ibpDir_prod_right (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ℓ : Y →L[ℝ] ℝ) (e : Y) (v : ℝ) (h : ibpDir ν ℓ e v) :
    ibpDir (μ.prod ν) (ℓ.comp (ContinuousLinearMap.snd ℝ X Y)) (0, e) v := by
  intro G hG h1 h2 h3
  have hs : ∀ a : X, ContDiff ℝ 1 (fun y : Y => G (a, y)) := fun a =>
    hG.comp (contDiff_const.prodMk contDiff_id)
  have hd : ∀ (a : X) (y : Y), fderiv ℝ (fun y : Y => G (a, y)) y e = fderiv ℝ G (a, y) (0, e) := by
    intro a y
    have h : HasFDerivAt (fun y : Y => G (a, y))
        ((fderiv ℝ G (a, y)).comp (ContinuousLinearMap.inr ℝ X Y)) y :=
      ((hG.differentiable (by norm_num) (a, y)).hasFDerivAt).comp y
        (hasFDerivAt_prodMk_right a y)
    rw [h.fderiv]
    simp
  have a1 := h1.prod_right_ae
  have a2 := h2.prod_right_ae
  have a3 := h3.prod_right_ae
  rw [integral_prod _ h2, integral_prod _ h3]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd']
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [a1, a2, a3] with a b1 b2 b3
  have := h (fun y => G (a, y)) (hs a) b1 (by simpa using b2) (by simpa [hd] using b3)
  simpa [hd] using this

end Lifts

section PiJoin

variable {ι X : Type*} [DecidableEq ι]

/-- The point of `ι → X` whose coordinate `i` is `y` and whose other coordinates are `b`. -/
private def piJoin (i : ι) (y : X) (b : {j // j ≠ i} → X) : ι → X :=
  fun j => if h : j = i then y else b ⟨j, h⟩

/-- `piJoin i y b` is `piJoin i 0 b` plus the vector `y` placed at the coordinate `i`. -/
private lemma piJoin_eq [AddCommGroup X] (i : ι) (y : X) (b : {j // j ≠ i} → X) :
    piJoin i y b = piJoin i 0 b + Pi.single i y := by
  funext j
  by_cases h : j = i
  · subst h; simp [piJoin]
  · simp [piJoin, h]

/-- `piJoin` is measurable. -/
private lemma measurable_piJoin [MeasurableSpace X] (i : ι) :
    Measurable (fun p : X × ({j // j ≠ i} → X) => piJoin i p.1 p.2) := by
  refine Measurable.of_eval fun j => ?_
  by_cases h : j = i
  · simp only [piJoin, h, dite_true]
    exact measurable_fst
  · simp only [piJoin, h, dite_false]
    exact (measurable_pi_apply _).comp measurable_snd

/-- The product law splits off the coordinate `i`. -/
private lemma piJoin_map [Fintype ι] [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (i : ι) :
    (μ.prod (Measure.pi fun _ : {j // j ≠ i} => μ)).map (fun p => piJoin i p.1 p.2) =
      Measure.pi fun _ : ι => μ := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_piJoin i) (MeasurableSet.univ_pi hs)]
  have : (fun p : X × ({j // j ≠ i} → X) => piJoin i p.1 p.2) ⁻¹' Set.univ.pi s =
      s i ×ˢ Set.univ.pi (fun j : {j // j ≠ i} => s j) := by
    ext ⟨y, b⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      exact ⟨by simpa [piJoin] using h i, fun j => by simpa [piJoin, j.property] using h j⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa [piJoin] using h1
      · simpa [piJoin, hj] using h2 ⟨j, hj⟩
  rw [this, Measure.prod_prod, Measure.pi_pi,
    Fintype.prod_eq_mul_prod_subtype_ne (fun j => μ (s j)) i]

end PiJoin

section PiLift

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- Integration by parts passes to the product measure `⊗_{j ∈ ι} μ` at the coordinate `i`. -/
private lemma ibpDir_pi (μ : Measure X) [IsProbabilityMeasure μ] (i : ι) (ℓ : X →L[ℝ] ℝ)
    (e : X) (v : ℝ) (h : ibpDir μ ℓ e v) :
    ibpDir (Measure.pi fun _ : ι => μ) (ℓ.comp (ContinuousLinearMap.proj i)) (Pi.single i e) v := by
  intro G hG h1 h2 h3
  set ν : Measure ({j // j ≠ i} → X) := Measure.pi fun _ : {j // j ≠ i} => μ with hν
  set Θ : X × ({j // j ≠ i} → X) → (ι → X) := fun p => piJoin i p.1 p.2 with hΘdef
  have hΘ : Measurable Θ := measurable_piJoin i
  have hmap : (μ.prod ν).map Θ = Measure.pi fun _ : ι => μ := piJoin_map μ i
  have c1 : Continuous G := hG.continuous
  have c2 : Continuous (fun x : ι → X =>
      (((ℓ.comp (ContinuousLinearMap.proj i)) x : ℝ) : ℂ) * G x) :=
    ((Complex.continuous_ofReal.comp
      ((ℓ.comp (ContinuousLinearMap.proj i : (ι → X) →L[ℝ] X)).continuous)).mul c1 :)
  have c3 : Continuous (fun x : ι → X => fderiv ℝ G x (Pi.single i e)) :=
    (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [← hmap] at h1 h2 h3 ⊢
  rw [integrable_map_measure c1.aestronglyMeasurable hΘ.aemeasurable] at h1
  rw [integrable_map_measure c2.aestronglyMeasurable hΘ.aemeasurable] at h2
  rw [integrable_map_measure c3.aestronglyMeasurable hΘ.aemeasurable] at h3
  rw [integral_map hΘ.aemeasurable c2.aestronglyMeasurable,
    integral_map hΘ.aemeasurable c3.aestronglyMeasurable]
  have hs : ∀ b : {j // j ≠ i} → X, ContDiff ℝ 1 (fun y : X => G (piJoin i y b)) := by
    intro b
    have e1 : (fun y : X => G (piJoin i y b)) =
        fun y => G (piJoin i 0 b + (ContinuousLinearMap.single ℝ (fun _ : ι => X) i) y) := by
      funext y; rw [piJoin_eq]; simp
    rw [e1]
    exact hG.comp (contDiff_const.add (ContinuousLinearMap.contDiff _))
  have hd : ∀ (b : {j // j ≠ i} → X) (y : X),
      fderiv ℝ (fun y : X => G (piJoin i y b)) y e = fderiv ℝ G (piJoin i y b) (Pi.single i e) := by
    intro b y
    have hf : HasFDerivAt (fun y : X => piJoin i y b)
        (ContinuousLinearMap.single ℝ (fun _ : ι => X) i) y := by
      have : (fun y : X => piJoin i y b) =
          fun y => piJoin i 0 b + (ContinuousLinearMap.single ℝ (fun _ : ι => X) i) y := by
        funext y; rw [piJoin_eq]; simp
      rw [this]
      exact (ContinuousLinearMap.single ℝ (fun _ : ι => X) i).hasFDerivAt.const_add _
    have h' : HasFDerivAt (fun y : X => G (piJoin i y b))
        ((fderiv ℝ G (piJoin i y b)).comp (ContinuousLinearMap.single ℝ (fun _ : ι => X) i)) y :=
      ((hG.differentiable (by norm_num) (piJoin i y b)).hasFDerivAt).comp y hf
    rw [h'.fderiv]
    simp
  have a1 := h1.prod_left_ae
  have a2 := h2.prod_left_ae
  have a3 := h3.prod_left_ae
  have I2 := integral_prod_symm _ h2
  have I3 := integral_prod_symm _ h3
  simp only [Function.comp] at I2 I3
  rw [I2, I3, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [a1, a2, a3] with b b1 b2 b3
  have key := h (fun y => G (piJoin i y b)) (hs b) b1 (by simpa [hΘdef, piJoin] using b2)
    (by simpa [hΘdef, hd] using b3)
  simpa [hΘdef, hd, piJoin] using key

end PiLift

section MapLift

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Integration by parts passes to the image of a measure under a continuous linear map. -/
private lemma ibpDir_map (μ : Measure X) (T : X →L[ℝ] Y) (ℓ : Y →L[ℝ] ℝ) (e : X) (v : ℝ)
    (h : ibpDir μ (ℓ.comp T) e v) : ibpDir (μ.map T) ℓ (T e) v := by
  intro G hG h1 h2 h3
  have hT : Measurable T := T.continuous.measurable
  have c1 : Continuous G := hG.continuous
  have c2 : Continuous (fun y : Y => ((ℓ y : ℝ) : ℂ) * G y) :=
    (Complex.continuous_ofReal.comp ℓ.continuous).mul c1
  have c3 : Continuous (fun y : Y => fderiv ℝ G y (T e)) :=
    (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [integrable_map_measure c1.aestronglyMeasurable hT.aemeasurable] at h1
  rw [integrable_map_measure c2.aestronglyMeasurable hT.aemeasurable] at h2
  rw [integrable_map_measure c3.aestronglyMeasurable hT.aemeasurable] at h3
  rw [integral_map hT.aemeasurable c2.aestronglyMeasurable,
    integral_map hT.aemeasurable c3.aestronglyMeasurable]
  have hGT : ContDiff ℝ 1 (G ∘ T) := hG.comp T.contDiff
  have hd : ∀ x, fderiv ℝ (G ∘ T) x e = fderiv ℝ G (T x) (T e) := by
    intro x
    rw [fderiv_comp x (hG.differentiable (by norm_num) (T x)) T.differentiableAt]
    simp
  have h3' : Integrable (fun x => fderiv ℝ (G ∘ T) x e) μ := by
    have : (fun x => fderiv ℝ (G ∘ T) x e) = (fun y => fderiv ℝ G y (T e)) ∘ T := funext hd
    rw [this]; exact h3
  have key := h (G ∘ T) hGT h1 h2 h3'
  simpa [hd] using key

end MapLift

/-- The map `(x, y) ↦ x + y i` as a continuous linear map. -/
private def realPairToC : ℝ × ℝ →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I

private lemma realPairToC_apply (p : ℝ × ℝ) :
    realPairToC p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
  simp [realPairToC, Complex.real_smul]

/-- `cGauss` is the image of `N(0, 1/2) ⊗ N(0, 1/2)` under `(x, y) ↦ x + y i`. -/
private lemma cGauss_eq_map : (cGauss : Measure ℂ) =
    ((gaussianReal 0 (1 / 2 : ℝ≥0)).prod (gaussianReal 0 (1 / 2 : ℝ≥0))).map realPairToC := by
  have : (realPairToC : ℝ × ℝ → ℂ) = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    funext p; exact realPairToC_apply p
  rw [this]
  rfl

/-- `cGauss` integrates by parts in the real direction with variance `1/2`. -/
private lemma ibpDir_cGauss_re : ibpDir (cGauss : Measure ℂ) Complex.reCLM 1 (1 / 2) := by
  have h := ibpDir_prod_left (gaussianReal 0 (1 / 2 : ℝ≥0)) (gaussianReal 0 (1 / 2 : ℝ≥0))
    (ContinuousLinearMap.id ℝ ℝ) 1 ((1 / 2 : ℝ≥0) : ℝ) (ibpDir_gaussianReal _ (by norm_num))
  have e1 : Complex.reCLM.comp realPairToC =
      (ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    ext <;> simp [realPairToC_apply]
  have e2 : realPairToC ((1 : ℝ), (0 : ℝ)) = 1 := by simp [realPairToC_apply]
  have := ibpDir_map _ realPairToC Complex.reCLM ((1 : ℝ), (0 : ℝ)) ((1 / 2 : ℝ≥0) : ℝ)
    (by rw [e1]; exact h)
  rw [e2] at this
  rw [cGauss_eq_map]
  simpa using this

/-- `cGauss` integrates by parts in the imaginary direction with variance `1/2`. -/
private lemma ibpDir_cGauss_im :
    ibpDir (cGauss : Measure ℂ) Complex.imCLM Complex.I (1 / 2) := by
  have h := ibpDir_prod_right (gaussianReal 0 (1 / 2 : ℝ≥0)) (gaussianReal 0 (1 / 2 : ℝ≥0))
    (ContinuousLinearMap.id ℝ ℝ) 1 ((1 / 2 : ℝ≥0) : ℝ) (ibpDir_gaussianReal _ (by norm_num))
  have e1 : Complex.imCLM.comp realPairToC =
      (ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    ext <;> simp [realPairToC_apply]
  have e2 : realPairToC ((0 : ℝ), (1 : ℝ)) = Complex.I := by simp [realPairToC_apply]
  have := ibpDir_map _ realPairToC Complex.imCLM ((0 : ℝ), (1 : ℝ)) ((1 / 2 : ℝ≥0) : ℝ)
    (by rw [e1]; exact h)
  rw [e2] at this
  rw [cGauss_eq_map]
  simpa using this

/-- A point of `Fin D → Coords N` is the sum of its coordinates times the unit vectors. -/
private lemma decomp_coords (D N : ℕ) (x : Fin D → Coords N) :
    x = (∑ a, ∑ i, ((x a).1 i) • bD a i) +
      ∑ a, ∑ i, ∑ j, ((((x a).2 i j).re) • bRe a i j + (((x a).2 i j).im) • bIm a i j) := by
  funext a
  rw [Pi.add_apply]
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single a]
  · refine Prod.ext ?_ ?_
    · funext i
      simp [bD, bRe, bIm, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · funext i j
      simp [bD, bRe, bIm, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk; simp [hk.symm]
        · simp
      · intro k _ hk; simp [hk.symm]
      · simp
  · intro b _ hb
    simp [bRe, bIm, hb.symm]
  · simp
  · intro b _ hb
    simp [bD, hb.symm]
  · simp

/-! ### Integration by parts for the GUE blocks -/

/-- The diagonal coordinate `x ↦ (x a).1 i`. -/
private def coordD {D N : ℕ} (a : Fin D) (i : Fin N) : (Fin D → Coords N) →L[ℝ] ℝ :=
  (((ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)).comp
    (ContinuousLinearMap.fst ℝ (Fin N → ℝ) (Fin N → Fin N → ℂ))).comp
      (ContinuousLinearMap.proj a : (Fin D → Coords N) →L[ℝ] Coords N)

/-- The real part of the array coordinate `x ↦ (x a).2 i j`. -/
private def coordRe {D N : ℕ} (a : Fin D) (i j : Fin N) : (Fin D → Coords N) →L[ℝ] ℝ :=
  ((((Complex.reCLM).comp (ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℝ] ℂ)).comp
    (ContinuousLinearMap.proj i : (Fin N → Fin N → ℂ) →L[ℝ] (Fin N → ℂ))).comp
    (ContinuousLinearMap.snd ℝ (Fin N → ℝ) (Fin N → Fin N → ℂ))).comp
      (ContinuousLinearMap.proj a : (Fin D → Coords N) →L[ℝ] Coords N)

/-- The imaginary part of the array coordinate `x ↦ (x a).2 i j`. -/
private def coordIm {D N : ℕ} (a : Fin D) (i j : Fin N) : (Fin D → Coords N) →L[ℝ] ℝ :=
  ((((Complex.imCLM).comp (ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℝ] ℂ)).comp
    (ContinuousLinearMap.proj i : (Fin N → Fin N → ℂ) →L[ℝ] (Fin N → ℂ))).comp
    (ContinuousLinearMap.snd ℝ (Fin N → ℝ) (Fin N → Fin N → ℂ))).comp
      (ContinuousLinearMap.proj a : (Fin D → Coords N) →L[ℝ] Coords N)

private lemma coordD_apply {D N : ℕ} (a : Fin D) (i : Fin N) (x : Fin D → Coords N) :
    coordD a i x = (x a).1 i := rfl

private lemma coordRe_apply {D N : ℕ} (a : Fin D) (i j : Fin N) (x : Fin D → Coords N) :
    coordRe a i j x = ((x a).2 i j).re := rfl

private lemma coordIm_apply {D N : ℕ} (a : Fin D) (i j : Fin N) (x : Fin D → Coords N) :
    coordIm a i j x = ((x a).2 i j).im := rfl

/-- `cGauss` is a Gaussian law. -/
private instance cGauss_isGaussian : IsGaussian (cGauss : Measure ℂ) := by
  rw [cGauss_eq_map]
  infer_instance

/-- The marginal of the blocks on block `a` is the GUE law. -/
private lemma gue_marg_eval (D N : ℕ) (a : Fin D) :
    MeasurePreserving (fun x : Fin D → Coords N => x a) (gueBlocks D N) (gueLaw N) :=
  measurePreserving_eval (fun _ : Fin D => gueLaw N) a

/-- The marginal of a diagonal coordinate is `N(0, 1)`. -/
private lemma gue_marg_D (D N : ℕ) (a : Fin D) (i : Fin N) :
    MeasurePreserving (fun x : Fin D → Coords N => (x a).1 i) (gueBlocks D N)
      (gaussianReal 0 1) := by
  have h2 : MeasurePreserving (Prod.fst : Coords N → Fin N → ℝ) (gueLaw N)
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) := measurePreserving_fst
  exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).comp
    (h2.comp (gue_marg_eval D N a))

/-- The marginal of an array coordinate is `cGauss`. -/
private lemma gue_marg_arr (D N : ℕ) (a : Fin D) (i j : Fin N) :
    MeasurePreserving (fun x : Fin D → Coords N => (x a).2 i j) (gueBlocks D N)
      (cGauss : Measure ℂ) := by
  have h2 : MeasurePreserving (Prod.snd : Coords N → Fin N → Fin N → ℂ) (gueLaw N)
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (cGauss : Measure ℂ)) :=
    measurePreserving_snd
  have h3 := measurePreserving_eval
    (fun _ : Fin N => Measure.pi fun _ : Fin N => (cGauss : Measure ℂ)) i
  have h4 := measurePreserving_eval (fun _ : Fin N => (cGauss : Measure ℂ)) j
  exact h4.comp (h3.comp (h2.comp (gue_marg_eval D N a)))

private lemma gue_integrable_D (D N : ℕ) (a : Fin D) (i : Fin N) :
    Integrable (fun x : Fin D → Coords N => (((coordD a i x : ℝ)) : ℂ)) (gueBlocks D N) := by
  have h : Integrable (fun x : Fin D → Coords N => (x a).1 i) (gueBlocks D N) :=
    (gue_marg_D D N a i).integrable_comp_of_integrable (g := id) IsGaussian.integrable_id
  exact h.ofReal

private lemma gue_integrable_Re (D N : ℕ) (a : Fin D) (i j : Fin N) :
    Integrable (fun x : Fin D → Coords N => (((coordRe a i j x : ℝ)) : ℂ)) (gueBlocks D N) := by
  have h : Integrable (fun x : Fin D → Coords N => ((x a).2 i j).re) (gueBlocks D N) :=
    (gue_marg_arr D N a i j).integrable_comp_of_integrable (g := Complex.re)
      (IsGaussian.integrable_dual (cGauss : Measure ℂ) Complex.reCLM)
  exact h.ofReal

private lemma gue_integrable_Im (D N : ℕ) (a : Fin D) (i j : Fin N) :
    Integrable (fun x : Fin D → Coords N => (((coordIm a i j x : ℝ)) : ℂ)) (gueBlocks D N) := by
  have h : Integrable (fun x : Fin D → Coords N => ((x a).2 i j).im) (gueBlocks D N) :=
    (gue_marg_arr D N a i j).integrable_comp_of_integrable (g := Complex.im)
      (IsGaussian.integrable_dual (cGauss : Measure ℂ) Complex.imCLM)
  exact h.ofReal

/-- The diagonal coordinate of the blocks integrates by parts with variance `1`. -/
private lemma gue_ibpDir_D (D N : ℕ) (a : Fin D) (i : Fin N) :
    ibpDir (gueBlocks D N) (coordD a i) (bD a i) 1 := by
  have h0 := ibpDir_gaussianReal 1 one_ne_zero
  rw [NNReal.coe_one] at h0
  have h1 := ibpDir_pi (gaussianReal 0 1) i (ContinuousLinearMap.id ℝ ℝ) 1 1 h0
  have h2 := ibpDir_prod_left _
    (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (cGauss : Measure ℂ)) _ _ _ h1
  exact ibpDir_pi (gueLaw N) a _ _ _ h2

/-- The real array coordinate of the blocks integrates by parts with variance `1/2`. -/
private lemma gue_ibpDir_Re (D N : ℕ) (a : Fin D) (i j : Fin N) :
    ibpDir (gueBlocks D N) (coordRe a i j) (bRe a i j) (1 / 2) := by
  have h1 := ibpDir_pi (cGauss : Measure ℂ) j Complex.reCLM 1 (1 / 2) ibpDir_cGauss_re
  have h2 := ibpDir_pi (Measure.pi fun _ : Fin N => (cGauss : Measure ℂ)) i _ _ _ h1
  have h3 := ibpDir_prod_right (Measure.pi fun _ : Fin N => gaussianReal 0 1) _ _ _ _ h2
  exact ibpDir_pi (gueLaw N) a _ _ _ h3

/-- The imaginary array coordinate of the blocks integrates by parts with variance `1/2`. -/
private lemma gue_ibpDir_Im (D N : ℕ) (a : Fin D) (i j : Fin N) :
    ibpDir (gueBlocks D N) (coordIm a i j) (bIm a i j) (1 / 2) := by
  have h1 := ibpDir_pi (cGauss : Measure ℂ) j Complex.imCLM Complex.I (1 / 2) ibpDir_cGauss_im
  have h2 := ibpDir_pi (Measure.pi fun _ : Fin N => (cGauss : Measure ℂ)) i _ _ _ h1
  have h3 := ibpDir_prod_right (Measure.pi fun _ : Fin N => gaussianReal 0 1) _ _ _ _ h2
  exact ibpDir_pi (gueLaw N) a _ _ _ h3

private lemma norm_bD_le {D N : ℕ} (a : Fin D) (i : Fin N) : ‖bD a i‖ ≤ 1 := by
  simp [bD, Pi.norm_single, Prod.norm_def]

private lemma norm_bRe_le {D N : ℕ} (a : Fin D) (i j : Fin N) : ‖bRe a i j‖ ≤ 1 := by
  simp [bRe, Pi.norm_single, Prod.norm_def]

private lemma norm_bIm_le {D N : ℕ} (a : Fin D) (i j : Fin N) : ‖bIm a i j‖ ≤ 1 := by
  simp [bIm, Pi.norm_single, Prod.norm_def]

/-- The first and second derivatives of `F` are bounded; the pointwise form of `hB` below. -/
private lemma gue_bounds {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → ℂ) (B : ℝ)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ v, ‖iteratedFDeriv ℝ j F v‖ ≤ B) :
    (∀ x, ‖fderiv ℝ F x‖ ≤ B) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ B) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have := hB 1 le_rfl (by norm_num) x
    rwa [norm_iteratedFDeriv_one] at this
  · have := hB 2 (by norm_num) le_rfl x
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this

/-- One coordinate direction of the blocks: integration by parts applied to `x ↦ DF(x)e`. -/
private lemma gue_term {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] (μ : Measure V) [IsProbabilityMeasure μ]
    (ℓ : V →L[ℝ] ℝ) (e : V) (v : ℝ) (he : ‖e‖ ≤ 1)
    (hℓ : Integrable (fun x => ((ℓ x : ℝ) : ℂ)) μ) (hμ : ibpDir μ ℓ e v)
    (F : V → ℂ) (hF : ContDiff ℝ 2 F) (B : ℝ) (h1 : ∀ x, ‖fderiv ℝ F x‖ ≤ B)
    (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ B) :
    Integrable (fun x => ((ℓ x : ℝ) : ℂ) * fderiv ℝ F x e) μ ∧
      Integrable (fun x => d2 F x e) μ ∧
      ∫ x, ((ℓ x : ℝ) : ℂ) * fderiv ℝ F x e ∂μ = (v : ℂ) * ∫ x, d2 F x e ∂μ := by
  have hFc : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hG : ContDiff ℝ 1 (fun y => fderiv ℝ F y e) := hFc.clm_apply contDiff_const
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (h1 0)
  have hGb : ∀ y, ‖fderiv ℝ F y e‖ ≤ B := fun y =>
    calc ‖fderiv ℝ F y e‖ ≤ ‖fderiv ℝ F y‖ * ‖e‖ := (fderiv ℝ F y).le_opNorm e
      _ ≤ B * 1 := mul_le_mul (h1 y) he (norm_nonneg _) hB0
      _ = B := mul_one B
  have hdG : ∀ y, fderiv ℝ (fun y => fderiv ℝ F y e) y e = fderiv ℝ (fderiv ℝ F) y e e := by
    intro y
    have := fderiv_clm_apply (c := fderiv ℝ F) (u := fun _ : V => e)
      (hFc.differentiable (by norm_num) y) (differentiableAt_const e)
    rw [this]
    simp
  have hdb : ∀ y, ‖fderiv ℝ (fun y => fderiv ℝ F y e) y e‖ ≤ B := fun y => by
    rw [hdG]
    calc ‖fderiv ℝ (fderiv ℝ F) y e e‖ ≤ ‖fderiv ℝ (fderiv ℝ F) y‖ * ‖e‖ * ‖e‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ B * 1 * 1 := by
          gcongr
          exact h2 y
      _ = B := by ring
  have hGi : Integrable (fun y => fderiv ℝ F y e) μ :=
    Integrable.of_bound hG.continuous.aestronglyMeasurable B (Filter.Eventually.of_forall hGb)
  have hGi2 : Integrable (fun x => ((ℓ x : ℝ) : ℂ) * fderiv ℝ F x e) μ :=
    hℓ.mul_bdd hG.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hGb)
  have hdi : Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ F y e) x e) μ :=
    Integrable.of_bound
      ((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable B
      (Filter.Eventually.of_forall hdb)
  exact ⟨hGi2, hdi, hμ _ hG hGi hGi2 hdi⟩

/-- The integral of a double sum of integrable functions is the double sum of the integrals. -/
private lemma integral_sum2 {α : Type*} [MeasurableSpace α] (μ : Measure α) {ι κ : Type*}
    [Fintype ι] [Fintype κ] (f : ι → κ → α → ℂ) (hf : ∀ a i, Integrable (f a i) μ) :
    ∫ x, ∑ a, ∑ i, f a i x ∂μ = ∑ a, ∑ i, ∫ x, f a i x ∂μ := by
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun i _ => hf a i))]
  exact Finset.sum_congr rfl fun a _ => integral_finsetSum _ (fun i _ => hf a i)

/-- The integral of a triple sum of integrable functions is the triple sum of the integrals. -/
private lemma integral_sum3 {α : Type*} [MeasurableSpace α] (μ : Measure α) {ι κ ρ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ρ] (f : ι → κ → ρ → α → ℂ)
    (hf : ∀ a i j, Integrable (f a i j) μ) :
    ∫ x, ∑ a, ∑ i, ∑ j, f a i j x ∂μ = ∑ a, ∑ i, ∑ j, ∫ x, f a i j x ∂μ := by
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun i _ => integrable_finsetSum _ (fun j _ => hf a i j)))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hf a i j))]
  exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hf a i j)

/-- Gaussian integration by parts for the GUE blocks, in terms of the pointwise bounds on the first
and second derivatives. -/
private lemma gueBlocks_ibp_aux (D N : ℕ) (F : (Fin D → Coords N) → ℂ) (B : ℝ)
    (hF : ContDiff ℝ 2 F) (h1 : ∀ x, ‖fderiv ℝ F x‖ ≤ B)
    (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ B) :
    ∫ x, fderiv ℝ F x x ∂(gueBlocks D N) = ∫ x, gLap F x ∂(gueBlocks D N) := by
  set μ := gueBlocks D N with hμ
  have tD := fun a i => gue_term μ (coordD a i) (bD a i) 1 (norm_bD_le a i)
    (gue_integrable_D D N a i) (gue_ibpDir_D D N a i) F hF B h1 h2
  have tR := fun a i j => gue_term μ (coordRe a i j) (bRe a i j) (1 / 2) (norm_bRe_le a i j)
    (gue_integrable_Re D N a i j) (gue_ibpDir_Re D N a i j) F hF B h1 h2
  have tI := fun a i j => gue_term μ (coordIm a i j) (bIm a i j) (1 / 2) (norm_bIm_le a i j)
    (gue_integrable_Im D N a i j) (gue_ibpDir_Im D N a i j) F hF B h1 h2
  simp only [coordD_apply, coordRe_apply, coordIm_apply] at tD tR tI
  -- pointwise decomposition of `DF(x) x`
  have hpt : ∀ x, fderiv ℝ F x x =
      (∑ a, ∑ i, (((x a).1 i : ℝ) : ℂ) * fderiv ℝ F x (bD a i)) +
        ∑ a, ∑ i, ∑ j, ((((x a).2 i j).re : ℝ) * fderiv ℝ F x (bRe a i j) +
          (((x a).2 i j).im : ℝ) * fderiv ℝ F x (bIm a i j)) := by
    intro x
    have := congrArg (fderiv ℝ F x) (decomp_coords D N x)
    rw [this]
    simp only [map_add, map_sum, map_smul, Complex.real_smul]
  have hLap : ∀ x, gLap F x = (∑ a, ∑ i, d2 F x (bD a i)) +
      (1 / 2 : ℂ) * ∑ a, ∑ i, ∑ j, (d2 F x (bRe a i j) + d2 F x (bIm a i j)) := fun x => rfl
  have iT : ∀ a i j, Integrable (fun x : Fin D → Coords N =>
      (((x a).2 i j).re : ℝ) * fderiv ℝ F x (bRe a i j) +
        (((x a).2 i j).im : ℝ) * fderiv ℝ F x (bIm a i j)) μ :=
    fun a i j => (tR a i j).1.add (tI a i j).1
  have iQ : ∀ a i j, Integrable (fun x : Fin D → Coords N =>
      d2 F x (bRe a i j) + d2 F x (bIm a i j)) μ :=
    fun a i j => (tR a i j).2.1.add (tI a i j).2.1
  have iTD : ∀ a i, Integrable (fun x : Fin D → Coords N =>
      (((x a).1 i : ℝ) : ℂ) * fderiv ℝ F x (bD a i)) μ := fun a i => (tD a i).1
  have iQD : ∀ a i, Integrable (fun x : Fin D → Coords N => d2 F x (bD a i)) μ :=
    fun a i => (tD a i).2.1
  simp only [hpt, hLap]
  rw [integral_add (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun i _ => iTD a i)
      (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => iT a i j),
    integral_add (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun i _ => iQD a i)
      ((integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => iQ a i j).const_mul _),
    integral_const_mul,
    integral_sum2 μ (fun a i x => (((x a).1 i : ℝ) : ℂ) * fderiv ℝ F x (bD a i)) iTD,
    integral_sum2 μ (fun a i x => d2 F x (bD a i)) iQD,
    integral_sum3 μ (fun a i j x => (((x a).2 i j).re : ℝ) * fderiv ℝ F x (bRe a i j) +
      (((x a).2 i j).im : ℝ) * fderiv ℝ F x (bIm a i j)) iT,
    integral_sum3 μ (fun a i j x => d2 F x (bRe a i j) + d2 F x (bIm a i j)) iQ]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [(tD a i).2.2]
    simp
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add (tR a i j).1 (tI a i j).1, integral_add (tR a i j).2.1 (tI a i j).2.1,
      (tR a i j).2.2, (tI a i j).2.2]
    push_cast
    ring

/-- Gaussian integration by parts for the GUE blocks: `E DF(X)·X = E gLap F(X)`. -/
theorem gueBlocks_ibp (D N : ℕ) (F : (Fin D → Coords N) → ℂ) (B : ℝ) (hF : ContDiff ℝ 2 F)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ v, ‖iteratedFDeriv ℝ j F v‖ ≤ B) :
    ∫ x, fderiv ℝ F x x ∂(gueBlocks D N) = ∫ x, gLap F x ∂(gueBlocks D N) := by
  obtain ⟨h1, h2⟩ := gue_bounds F B hB
  exact gueBlocks_ibp_aux D N F B hF h1 h2

/-! ### Integration by parts for the complex Gaussian -/

/-- `(1 + ‖z‖)^m` is integrable against `cGauss`. -/
private lemma cGauss_integrable_pow (m : ℕ) :
    Integrable (fun z : ℂ => (1 + ‖z‖) ^ m) (cGauss : Measure ℂ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : MemLp (fun z : ℂ => ‖z‖) (m : ℝ≥0∞) (cGauss : Measure ℂ) :=
      (IsGaussian.memLp_id (cGauss : Measure ℂ) (m : ℝ≥0∞) (by simp)).norm
    have h2 : MemLp (fun z : ℂ => 1 + ‖z‖) (m : ℝ≥0∞) (cGauss : Measure ℂ) :=
      (memLp_const (1 : ℝ)).add h1
    have := h2.integrable_norm_pow hm.ne'
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]

/-- Integration by parts for `cGauss` for `C¹` functions of polynomial growth. -/
private lemma cGauss_ibp_poly (F : ℂ → ℂ) (hF : ContDiff ℝ 1 F) (C : ℝ) (k : ℕ)
    (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ k) (hd : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ k) :
    ∫ z, starRingEnd ℂ z * F z ∂(cGauss : Measure ℂ) = ∫ z, dW F z ∂(cGauss : Measure ℂ) := by
  have hC : 0 ≤ C := by
    have := hb 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hw := (cGauss_integrable_pow (k + 1)).const_mul C
  have hpow : ∀ z : ℂ, (1 + ‖z‖) ^ k ≤ (1 + ‖z‖) ^ (k + 1) := fun z =>
    pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Nat.le_succ k)
  have hFc : Continuous F := hF.continuous
  have hDc : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  have i1 : Integrable F (cGauss : Measure ℂ) :=
    hw.mono' hFc.aestronglyMeasurable (Filter.Eventually.of_forall fun z =>
      (hb z).trans (mul_le_mul_of_nonneg_left (hpow z) hC))
  have hre : ∀ z : ℂ, ‖z.re‖ ≤ ‖z‖ := fun z => by
    simpa using Complex.abs_re_le_norm z
  have him : ∀ z : ℂ, ‖z.im‖ ≤ ‖z‖ := fun z => by
    simpa using Complex.abs_im_le_norm z
  have hmulb : ∀ z : ℂ, ∀ r : ℝ, ‖r‖ ≤ ‖z‖ → ‖(r : ℂ) * F z‖ ≤ C * (1 + ‖z‖) ^ (k + 1) := by
    intro z r hr
    calc ‖(r : ℂ) * F z‖ = ‖r‖ * ‖F z‖ := by rw [norm_mul, Complex.norm_real]
      _ ≤ ‖z‖ * (C * (1 + ‖z‖) ^ k) :=
          mul_le_mul hr (hb z) (norm_nonneg _) (norm_nonneg _)
      _ ≤ (1 + ‖z‖) * (C * (1 + ‖z‖) ^ k) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = C * (1 + ‖z‖) ^ (k + 1) := by ring
  have i2 : Integrable (fun z : ℂ => ((z.re : ℝ) : ℂ) * F z) (cGauss : Measure ℂ) :=
    hw.mono' ((Complex.continuous_ofReal.comp Complex.continuous_re).mul hFc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hmulb z _ (hre z))
  have i3 : Integrable (fun z : ℂ => ((z.im : ℝ) : ℂ) * F z) (cGauss : Measure ℂ) :=
    hw.mono' ((Complex.continuous_ofReal.comp Complex.continuous_im).mul hFc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hmulb z _ (him z))
  have hdb : ∀ (z h : ℂ), ‖h‖ ≤ 1 → ‖fderiv ℝ F z h‖ ≤ C * (1 + ‖z‖) ^ (k + 1) := fun z h hh =>
    calc ‖fderiv ℝ F z h‖ ≤ ‖fderiv ℝ F z‖ * ‖h‖ := (fderiv ℝ F z).le_opNorm h
      _ ≤ (C * (1 + ‖z‖) ^ k) * 1 := mul_le_mul (hd z) hh (norm_nonneg _) (by positivity)
      _ ≤ C * (1 + ‖z‖) ^ (k + 1) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left (hpow z) hC
  have i4 : Integrable (fun z : ℂ => fderiv ℝ F z 1) (cGauss : Measure ℂ) :=
    hw.mono' (hDc.clm_apply continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hdb z 1 (by simp))
  have i5 : Integrable (fun z : ℂ => fderiv ℝ F z Complex.I) (cGauss : Measure ℂ) :=
    hw.mono' (hDc.clm_apply continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hdb z Complex.I (by simp))
  have e1 := ibpDir_cGauss_re F hF i1 (by simpa using i2) (by simpa using i4)
  have e2 := ibpDir_cGauss_im F hF i1 (by simpa using i3) (by simpa using i5)
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at e1 e2
  have hconj : ∀ z : ℂ, starRingEnd ℂ z * F z =
      ((z.re : ℝ) : ℂ) * F z - Complex.I * (((z.im : ℝ) : ℂ) * F z) := fun z => by
    have : starRingEnd ℂ z = (z.re : ℂ) - Complex.I * (z.im : ℂ) := by
      apply Complex.ext <;> simp
    rw [this]; ring
  simp only [hconj, dW]
  rw [integral_sub i2 (i3.const_mul _), integral_const_mul, e1, e2,
    integral_div, integral_sub i4 (i5.const_mul _), integral_const_mul]
  push_cast
  ring

/-! ### The moments and cumulants of the complex Gaussian -/

/-- The mixed moment `E z^a z̄^b` of `cGauss`. -/
private def cMom (a b : ℕ) : ℂ := ∫ z, z ^ a * starRingEnd ℂ z ^ b ∂(cGauss : Measure ℂ)

/-- The derivative of the monomial `z ↦ z^a z̄^b` in the direction `h`. -/
private lemma fderiv_mono (a b : ℕ) (z h : ℂ) :
    fderiv ℝ (fun z : ℂ => z ^ a * starRingEnd ℂ z ^ b) z h =
      ((a : ℂ) * z ^ (a - 1) * starRingEnd ℂ z ^ b) * h +
        (z ^ a * ((b : ℂ) * starRingEnd ℂ z ^ (b - 1))) * starRingEnd ℂ h := by
  have h1 : ∀ n : ℕ, HasFDerivAt (fun z : ℂ => z ^ n)
      (((n : ℂ) * z ^ (n - 1)) • (ContinuousLinearMap.id ℝ ℂ)) z := fun n => by
    have := (hasDerivAt_pow n z).hasFDerivAt.restrictScalars ℝ
    convert this using 1
    ext
    simp [mul_comm]
  have h2 : HasFDerivAt (fun z : ℂ => starRingEnd ℂ z ^ b)
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (((b : ℂ) * z ^ (b - 1)) • (ContinuousLinearMap.id ℝ ℂ)))
      z := by
    have h2' : HasFDerivAt (fun z : ℂ => Complex.conjCLE (z ^ b))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
          (((b : ℂ) * z ^ (b - 1)) • (ContinuousLinearMap.id ℝ ℂ))) z :=
      (Complex.conjCLE.hasFDerivAt).comp z (h1 b)
    convert h2' using 1
    funext y
    simp
  have h3 := ((h1 a).mul h2).fderiv
  change (fderiv ℝ ((fun z : ℂ => z ^ a) * fun z : ℂ => starRingEnd ℂ z ^ b) z) h = _
  rw [h3]
  simp
  ring

private lemma norm_pow_le_pow_one_add (z : ℂ) {n m : ℕ} (h : n ≤ m) : ‖z‖ ^ n ≤ (1 + ‖z‖) ^ m :=
  (pow_le_pow_left₀ (norm_nonneg z) (by linarith) n).trans
    (pow_le_pow_right₀ (by linarith [norm_nonneg z]) h)

/-- `E z̄ · z^a z̄^b = a E z^{a-1} z̄^b`: (2.26) [5.16] for `cGauss` applied to a monomial. -/
private lemma cMom_succ (a b : ℕ) : cMom a (b + 1) = (a : ℂ) * cMom (a - 1) b := by
  set F : ℂ → ℂ := fun z => z ^ a * starRingEnd ℂ z ^ b with hF
  have hFd : ContDiff ℝ 1 F :=
    (contDiff_id.pow a).mul ((Complex.conjCLE.contDiff (n := 1)).pow b)
  have hb : ∀ z, ‖F z‖ ≤ ((a + b + 1 : ℕ) : ℝ) * (1 + ‖z‖) ^ (a + b) := fun z => by
    have h1 : ‖F z‖ = ‖z‖ ^ (a + b) := by
      simp [hF, norm_pow, pow_add]
    rw [h1]
    calc ‖z‖ ^ (a + b) ≤ (1 + ‖z‖) ^ (a + b) := norm_pow_le_pow_one_add z le_rfl
      _ ≤ ((a + b + 1 : ℕ) : ℝ) * (1 + ‖z‖) ^ (a + b) := by
          have : (1 : ℝ) ≤ ((a + b + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 (a + b)
          nlinarith [pow_nonneg (by linarith [norm_nonneg z] : (0 : ℝ) ≤ 1 + ‖z‖) (a + b)]
  have hd : ∀ z, ‖fderiv ℝ F z‖ ≤ ((a + b + 1 : ℕ) : ℝ) * (1 + ‖z‖) ^ (a + b) := fun z => by
    have hA : ‖(a : ℂ) * z ^ (a - 1) * starRingEnd ℂ z ^ b‖ ≤ a * (1 + ‖z‖) ^ (a + b) := by
      simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_conj]
      rw [mul_assoc, ← pow_add]
      exact mul_le_mul_of_nonneg_left (norm_pow_le_pow_one_add z (by omega)) (Nat.cast_nonneg a)
    have hBc : ‖z ^ a * ((b : ℂ) * starRingEnd ℂ z ^ (b - 1))‖ ≤ b * (1 + ‖z‖) ^ (a + b) := by
      simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_conj]
      rw [← mul_assoc, mul_comm (‖z‖ ^ a), mul_assoc, ← pow_add]
      exact mul_le_mul_of_nonneg_left (norm_pow_le_pow_one_add z (by omega)) (Nat.cast_nonneg b)
    have hP : (0 : ℝ) ≤ (1 + ‖z‖) ^ (a + b) := pow_nonneg (by linarith [norm_nonneg z]) _
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    rw [hF, fderiv_mono]
    calc ‖(a : ℂ) * z ^ (a - 1) * starRingEnd ℂ z ^ b * h +
          z ^ a * ((b : ℂ) * starRingEnd ℂ z ^ (b - 1)) * starRingEnd ℂ h‖
        ≤ ‖(a : ℂ) * z ^ (a - 1) * starRingEnd ℂ z ^ b‖ * ‖h‖ +
          ‖z ^ a * ((b : ℂ) * starRingEnd ℂ z ^ (b - 1))‖ * ‖h‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul (z ^ a * _), Complex.norm_conj]
      _ ≤ ((a + b + 1 : ℕ) : ℝ) * (1 + ‖z‖) ^ (a + b) * ‖h‖ := by
          push_cast
          nlinarith [norm_nonneg h, mul_le_mul_of_nonneg_right hA (norm_nonneg h),
            mul_le_mul_of_nonneg_right hBc (norm_nonneg h)]
  have key := cGauss_ibp_poly F hFd _ _ hb hd
  have e1 : ∀ z : ℂ, starRingEnd ℂ z * F z = z ^ a * starRingEnd ℂ z ^ (b + 1) := fun z => by
    simp only [hF]; ring
  have e2 : ∀ z : ℂ, dW F z = (a : ℂ) * (z ^ (a - 1) * starRingEnd ℂ z ^ b) := fun z => by
    have h1 := fderiv_mono a b z 1
    have h2 := fderiv_mono a b z Complex.I
    simp only [dW, hF, h1, h2, map_one, Complex.conj_I]
    linear_combination (((z ^ a * ((b : ℂ) * starRingEnd ℂ z ^ (b - 1))) -
      ((a : ℂ) * z ^ (a - 1) * starRingEnd ℂ z ^ b)) / 2) * Complex.I_sq
  simp only [e1, e2] at key
  rw [integral_const_mul] at key
  exact key

private lemma cMom_zero_zero : cMom 0 0 = 1 := by simp [cMom]

/-- `E z^{a+1} = 0` for `cGauss`. -/
private lemma cMom_succ_zero (a : ℕ) : cMom (a + 1) 0 = 0 := by
  have h0 : cMom 0 (a + 1) = 0 := by rw [cMom_succ]; simp
  have : cMom (a + 1) 0 = starRingEnd ℂ (cMom 0 (a + 1)) := by
    simp only [cMom, pow_zero, one_mul, mul_one]
    rw [← integral_conj]
    simp
  rw [this, h0, map_zero]

private lemma cGauss_integrable_norm_pow (p : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ p) (cGauss : Measure ℂ) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · exact (IsGaussian.memLp_id (cGauss : Measure ℂ) (p : ℝ≥0∞) (by simp)).integrable_norm_pow
      hp.ne'

/-- The cumulants `𝒞^{(p,0)}`, `p ≥ 1`, of `cGauss` vanish: every block of a partition has a
vanishing moment `E z^k`, `k ≥ 1`. -/
private lemma ccum_cGauss_q0 (p : ℕ) (hp : 1 ≤ p) : ccum (cGauss : Measure ℂ) p 0 = 0 := by
  unfold ccum jointCum
  refine Finset.sum_eq_zero fun π _ => ?_
  obtain ⟨B, hB, hi0⟩ := π.exists_mem (Finset.mem_univ (⟨0, by omega⟩ : Fin (p + 0)))
  have hne : B.card ≠ 0 := Finset.card_ne_zero.mpr ⟨_, hi0⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hB ?_)
  have hprod : ∀ z : ℂ, (∏ i ∈ B, (if (i : ℕ) < p then (fun z : ℂ => z)
      else (fun z => starRingEnd ℂ z)) z) = z ^ B.card := by
    intro z
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : (i : ℕ) < p := by simp
    simp [this]
  simp only [hprod, hk]
  have := cMom_succ_zero k
  simpa [cMom] using this

/-- The cumulants `𝒞^{(p,q)}`, `q ≥ 1`, of `cGauss`, by induction on `p + q` with the
moment–cumulant recursion and `E z̄ · z^a z̄^b = a E z^{a-1} z̄^b`. -/
private lemma ccum_cGauss_pos (n : ℕ) : ∀ p q : ℕ, p + q = n → 1 ≤ q →
    ccum (cGauss : Measure ℂ) p q = if p = 1 ∧ q = 1 then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a q hn hq
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    set ct : ℕ → ℕ → ℂ := fun p q => if p = 1 ∧ q = 1 then 1 else 0 with hct
    set T : (ℕ → ℕ → ℂ) → ℂ := fun f => ∑ p ∈ Finset.range (a + 1), ∑ q ∈ Finset.range (b + 1),
      ((a.choose p * b.choose q : ℕ) : ℂ) * f p (q + 1) * cMom (a - p) (b - q) with hT
    have R : cMom a (b + 1) = T (fun p q => ccum (cGauss : Measure ℂ) p q) := by
      have := moment_ccum_recursion (cGauss : Measure ℂ) cGauss_integrable_norm_pow a b
      simpa [hT, cMom] using this
    have hK : T ct = cMom a (b + 1) := by
      rw [cMom_succ]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp [hT, hct]
      · rw [hT]
        simp only
        rw [Finset.sum_eq_single 1]
        · rw [Finset.sum_eq_single 0]
          · simp [hct]
          · intro q _ hq
            simp [hct, hq]
          · intro h
            simp at h
        · intro p _ hp
          apply Finset.sum_eq_zero
          intro q _
          simp [hct, hp]
        · intro h
          simp only [Finset.mem_range] at h
          omega
    have hD : T (fun p q => ccum (cGauss : Measure ℂ) p q) - T ct =
        ccum (cGauss : Measure ℂ) a (b + 1) - ct a (b + 1) := by
      have h1 : T (fun p q => ccum (cGauss : Measure ℂ) p q) - T ct =
          ∑ p ∈ Finset.range (a + 1), ∑ q ∈ Finset.range (b + 1),
            ((a.choose p * b.choose q : ℕ) : ℂ) *
              (ccum (cGauss : Measure ℂ) p (q + 1) - ct p (q + 1)) * cMom (a - p) (b - q) := by
        simp only [hT, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        ring
      rw [h1, Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · simp [cMom_zero_zero]
        · intro q hq hqb
          have hq' : q < b := by
            simp only [Finset.mem_range] at hq
            omega
          have := ih (a + (q + 1)) (by omega) a (q + 1) rfl (by omega)
          simp [hct] at this ⊢
          simp [this]
        · intro h
          simp at h
      · intro p hp hpa
        apply Finset.sum_eq_zero
        intro q hq
        have hp' : p < a := by
          simp only [Finset.mem_range] at hp
          omega
        have hq' : q ≤ b := by
          simp only [Finset.mem_range] at hq
          omega
        have := ih (p + (q + 1)) (by omega) p (q + 1) rfl (by omega)
        simp [hct] at this ⊢
        simp [this]
      · intro h
        simp at h
    have := hD
    rw [← R, hK, sub_self] at this
    have h2 : ccum (cGauss : Measure ℂ) a (b + 1) = ct a (b + 1) := by
      have := this.symm
      exact sub_eq_zero.mp this
    simpa [hct] using h2

/-- The complex Gaussian has only `𝒞^{(1,1)} = 1` among the cumulants of order `≥ 1`. -/
theorem ccum_cGauss (p q : ℕ) (hpq : 1 ≤ p + q) :
    ccum (cGauss : Measure ℂ) p q = if p = 1 ∧ q = 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have := ccum_cGauss_q0 p (by omega)
    rw [this]
    simp
  · exact ccum_cGauss_pos (p + q) p q rfl hq

/-! ### The derivative of Ornstein–Uhlenbeck expectations -/

/-- A product of copies of a Gaussian law is Gaussian. -/
instance isGaussian_pi_const {ι X : Type*} [Fintype ι] [NormedAddCommGroup X]
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

/-- The GUE law of one block is Gaussian. -/
instance gueLaw_isGaussian (N : ℕ) : IsGaussian (gueLaw N) := by
  unfold gueLaw
  infer_instance

/-- The law of the GUE blocks is Gaussian. -/
private instance gueBlocks_isGaussian (D N : ℕ) : IsGaussian (gueBlocks D N) := by
  unfold gueBlocks
  infer_instance

/-- `‖x‖` is integrable under the GUE blocks. -/
private lemma gue_integrable_norm (D N : ℕ) :
    Integrable (fun x : Fin D → Coords N => ‖x‖) (gueBlocks D N) :=
  memLp_one_iff_integrable.1 ((IsGaussian.memLp_id (gueBlocks D N) 1 (by simp)).norm)

/-- `D²F(x)[v, v]` is the second Fréchet derivative applied to `(v, v)`. -/
private lemma d2_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → ℂ)
    (hF : ContDiff ℝ 2 F) (x v : V) : d2 F x v = fderiv ℝ (fderiv ℝ F) x v v := by
  have hFc : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  unfold d2
  have := fderiv_clm_apply (c := fderiv ℝ F) (u := fun _ : V => v)
    (hFc.differentiable (by norm_num) x) (differentiableAt_const v)
  rw [this]
  simp

/-- The derivative of `x ↦ H (c + σ x)`. -/
private lemma fderiv_affine_comp {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (H : V → W) (c : V) (σ : ℝ) (x : V)
    (hH : DifferentiableAt ℝ H (c + σ • x)) :
    fderiv ℝ (fun y => H (c + σ • y)) x = σ • fderiv ℝ H (c + σ • x) := by
  have hA : HasFDerivAt (fun y : V => c + σ • y) (σ • ContinuousLinearMap.id ℝ V) x :=
    ((hasFDerivAt_id x).const_smul σ).const_add c
  have h : HasFDerivAt (fun y : V => H (c + σ • y))
      ((fderiv ℝ H (c + σ • x)).comp (σ • ContinuousLinearMap.id ℝ V)) x := hH.hasFDerivAt.comp x hA
  rw [h.fderiv]
  ext v
  simp

/-- The affine pullback `G(x) = F(c + σ x)` of a `C²` function and its derivatives. -/
private lemma affine_pullback {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → ℂ)
    (hF : ContDiff ℝ 2 F) (c : V) (σ : ℝ) :
    ContDiff ℝ 2 (fun x => F (c + σ • x)) ∧
      (∀ x, fderiv ℝ (fun y => F (c + σ • y)) x = σ • fderiv ℝ F (c + σ • x)) ∧
      (∀ x, fderiv ℝ (fderiv ℝ (fun y => F (c + σ • y))) x =
        (σ * σ) • fderiv ℝ (fderiv ℝ F) (c + σ • x)) := by
  have hFc : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have h1 : ∀ x, fderiv ℝ (fun y => F (c + σ • y)) x = σ • fderiv ℝ F (c + σ • x) := fun x =>
    fderiv_affine_comp F c σ x (hF.differentiable (by norm_num) _)
  refine ⟨hF.comp (contDiff_const.add (contDiff_const.smul contDiff_id)), h1, fun x => ?_⟩
  have : fderiv ℝ (fun y => F (c + σ • y)) = fun x => σ • fderiv ℝ F (c + σ • x) := funext h1
  rw [this]
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ F (c + σ • y)) x :=
    (hFc.differentiable (by norm_num) _).comp x
      ((differentiableAt_const c).add ((differentiableAt_id).const_smul σ))
  have e := fderiv_const_smul hd σ
  change fderiv ℝ (σ • fun y => fderiv ℝ F (c + σ • y)) x = _
  rw [e, fderiv_affine_comp (fderiv ℝ F) c σ x (hFc.differentiable (by norm_num) _), smul_smul]

/-- `gLap` of the affine pullback: `gLap G (x) = σ² gLap F (c + σ x)`. -/
private lemma gLap_affine {D N : ℕ} (F : (Fin D → Coords N) → ℂ) (hF : ContDiff ℝ 2 F)
    (c : Fin D → Coords N) (σ : ℝ) (x : Fin D → Coords N) :
    gLap (fun y => F (c + σ • y)) x = ((σ * σ : ℝ) : ℂ) * gLap F (c + σ • x) := by
  obtain ⟨hG, -, hG2⟩ := affine_pullback F hF c σ
  have hd2 : ∀ v, d2 (fun y => F (c + σ • y)) x v = ((σ * σ : ℝ) : ℂ) * d2 F (c + σ • x) v := by
    intro v
    rw [d2_eq _ hG, d2_eq _ hF, hG2]
    simp [Complex.real_smul]
  simp only [gLap, hd2, ← mul_add, ← Finset.mul_sum]
  ring

/-- `gLap F` is integrable for the GUE blocks. -/
private lemma gLap_integrable_aux (D N : ℕ) (F : (Fin D → Coords N) → ℂ) (B : ℝ)
    (hF : ContDiff ℝ 2 F) (h1 : ∀ x, ‖fderiv ℝ F x‖ ≤ B)
    (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ B) : Integrable (gLap F) (gueBlocks D N) := by
  set μ := gueBlocks D N with hμ
  have tD := fun a i => gue_term μ (coordD a i) (bD a i) 1 (norm_bD_le a i)
    (gue_integrable_D D N a i) (gue_ibpDir_D D N a i) F hF B h1 h2
  have tR := fun a i j => gue_term μ (coordRe a i j) (bRe a i j) (1 / 2) (norm_bRe_le a i j)
    (gue_integrable_Re D N a i j) (gue_ibpDir_Re D N a i j) F hF B h1 h2
  have tI := fun a i j => gue_term μ (coordIm a i j) (bIm a i j) (1 / 2) (norm_bIm_le a i j)
    (gue_integrable_Im D N a i j) (gue_ibpDir_Im D N a i j) F hF B h1 h2
  have iQ : ∀ a i j, Integrable (fun x : Fin D → Coords N =>
      d2 F x (bRe a i j) + d2 F x (bIm a i j)) μ :=
    fun a i j => (tR a i j).2.1.add (tI a i j).2.1
  have iQD : ∀ a i, Integrable (fun x : Fin D → Coords N => d2 F x (bD a i)) μ :=
    fun a i => (tD a i).2.1
  have : Integrable (fun x : Fin D → Coords N => (∑ a, ∑ i, d2 F x (bD a i)) +
      (1 / 2 : ℂ) * ∑ a, ∑ i, ∑ j, (d2 F x (bRe a i j) + d2 F x (bIm a i j))) μ :=
    (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun i _ => iQD a i).add
      ((integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => iQ a i j).const_mul _)
  exact this

/-- The pointwise derivative bounds pass to the affine pullback `x ↦ F (c + σ x)`, `0 < σ ≤ 1`. -/
private lemma affine_bounds {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → ℂ)
    (B : ℝ) (hF : ContDiff ℝ 2 F) (h1 : ∀ x, ‖fderiv ℝ F x‖ ≤ B)
    (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ B) (c : V) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    (∀ x, ‖fderiv ℝ (fun y => F (c + σ • y)) x‖ ≤ B) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ (fun y => F (c + σ • y))) x‖ ≤ B) := by
  obtain ⟨-, hG1, hG2⟩ := affine_pullback F hF c σ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (h1 0)
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [hG1, norm_smul, Real.norm_eq_abs, abs_of_pos hσ0]
    calc σ * ‖fderiv ℝ F (c + σ • x)‖ ≤ 1 * B :=
          mul_le_mul hσ1 (h1 _) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  · rw [hG2]
    refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun v => ?_
    rw [_root_.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hσ0 hσ0)]
    have hA := ((fderiv ℝ (fderiv ℝ F) (c + σ • x)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (h2 (c + σ • x)) (norm_nonneg v))
    calc σ * σ * ‖fderiv ℝ (fderiv ℝ F) (c + σ • x) v‖ ≤ 1 * (B * ‖v‖) :=
          mul_le_mul (by nlinarith) hA (norm_nonneg _) zero_le_one
      _ = B * ‖v‖ := one_mul _

/-- `x ↦ gLap F (c + σ x)` is integrable for the GUE blocks, for `0 < σ ≤ 1`. -/
private lemma ou_integrable_gLap (D N : ℕ) (F : (Fin D → Coords N) → ℂ) (B : ℝ)
    (hF : ContDiff ℝ 2 F) (h1 : ∀ x, ‖fderiv ℝ F x‖ ≤ B)
    (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ B) (c : Fin D → Coords N) (σ : ℝ) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1) : Integrable (fun x => gLap F (c + σ • x)) (gueBlocks D N) := by
  obtain ⟨hG, -, -⟩ := affine_pullback F hF c σ
  obtain ⟨b1, b2⟩ := affine_bounds F B hF h1 h2 c σ hσ0 hσ1
  have h := gLap_integrable_aux D N (fun y => F (c + σ • y)) B hG b1 b2
  have hσ : ((σ * σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos hσ0 hσ0).ne'
  refine (h.const_mul (((σ * σ : ℝ) : ℂ))⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gLap_affine F hF c σ]
  rw [← mul_assoc, inv_mul_cancel₀ hσ, one_mul]

/-- Integration by parts for the rescaled blocks `x ↦ F (c + σ x)`:
`E DF(c + σX)·X = σ E gLap F(c + σX)`, for `0 < σ ≤ 1`. -/
private lemma ou_ibp (D N : ℕ) (F : (Fin D → Coords N) → ℂ) (B : ℝ) (hF : ContDiff ℝ 2 F)
    (h1 : ∀ x, ‖fderiv ℝ F x‖ ≤ B) (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ B)
    (c : Fin D → Coords N) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ∫ x, fderiv ℝ F (c + σ • x) x ∂(gueBlocks D N) =
      (σ : ℂ) * ∫ x, gLap F (c + σ • x) ∂(gueBlocks D N) := by
  obtain ⟨hG, hG1, hG2⟩ := affine_pullback F hF c σ
  obtain ⟨b1, b2⟩ := affine_bounds F B hF h1 h2 c σ hσ0 hσ1
  have e := gueBlocks_ibp_aux D N (fun y => F (c + σ • y)) B hG b1 b2
  have l1 : ∫ x, fderiv ℝ (fun y => F (c + σ • y)) x x ∂(gueBlocks D N) =
      (σ : ℂ) * ∫ x, fderiv ℝ F (c + σ • x) x ∂(gueBlocks D N) := by
    simp only [hG1, _root_.smul_apply, Complex.real_smul]
    exact integral_const_mul _ _
  have l2 : ∫ x, gLap (fun y => F (c + σ • y)) x ∂(gueBlocks D N) =
      ((σ * σ : ℝ) : ℂ) * ∫ x, gLap F (c + σ • x) ∂(gueBlocks D N) := by
    simp only [gLap_affine F hF c σ]
    exact integral_const_mul _ _
  rw [l1, l2] at e
  have hσ : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  have : (σ : ℂ) * (∫ x, fderiv ℝ F (c + σ • x) x ∂(gueBlocks D N) -
      (σ : ℂ) * ∫ x, gLap F (c + σ • x) ∂(gueBlocks D N)) = 0 := by
    push_cast at e
    linear_combination e
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hσ
  · exact sub_eq_zero.mp h

/-- The point `e^{-t/2} w + √(1 - e^{-t}) x`; with `x ∼ gueBlocks D N` its law is (3.13)
[eq:Gauss_div], and with one block of size `DN` and `w = fun _ => blockEmb D N H` it is (4.3)
[eq:eq_in_law_H]. -/
def ouPoint (D N : ℕ) (t : ℝ) (w x : Fin D → Coords N) : Fin D → Coords N :=
  Real.exp (-t / 2) • w + Real.sqrt (1 - Real.exp (-t)) • x

/-- The derivative in `s` of the path `s ↦ ouPoint D N s w x`, for `s > 0`. -/
private lemma hasDerivAt_ouPoint (D N : ℕ) (w x : Fin D → Coords N) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun r => ouPoint D N r w x)
      ((-(1 / 2 : ℝ) * Real.exp (-s / 2)) • w +
        (Real.exp (-s) / (2 * Real.sqrt (1 - Real.exp (-s)))) • x) s := by
  have hf : HasDerivAt (fun r : ℝ => -r / 2) (-(1 / 2)) s := by
    simpa [neg_div] using ((hasDerivAt_id s).neg).div_const 2
  have ha := hf.exp
  have hg : HasDerivAt (fun r : ℝ => 1 - Real.exp (-r)) (Real.exp (-s)) s := by
    simpa using ((hasDerivAt_id s).neg.exp).const_sub 1
  have hne : 1 - Real.exp (-s) ≠ 0 := by
    have : Real.exp (-s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hσ := hg.sqrt hne
  have := (ha.smul_const w).add (hσ.smul_const x)
  convert this using 1
  · funext r
    rfl
  · rw [mul_comm (-(1 / 2 : ℝ)) (Real.exp (-s / 2))]

/-- `∂_t E F(e^{-t/2} w + √(1-e^{-t}) W) = E(-½ e^{-t/2} DF·w + ½ e^{-t} gLap F)` for `t > 0`: the
Itô display before (4.9) [eq:prodnGt] as a statement about one-time laws. -/
theorem hasDerivAt_ouExpect (D N : ℕ) (F : (Fin D → Coords N) → ℂ) (B : ℝ) (hF : ContDiff ℝ 2 F)
    (hB : ∀ j : ℕ, j ≤ 2 → ∀ v, ‖iteratedFDeriv ℝ j F v‖ ≤ B) (w : Fin D → Coords N) (t : ℝ)
    (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, F (ouPoint D N s w x) ∂(gueBlocks D N))
      (∫ x, (-(1 / 2 : ℂ) * (Real.exp (-t / 2) : ℂ) * fderiv ℝ F (ouPoint D N t w x) w +
        (1 / 2 : ℂ) * (Real.exp (-t) : ℂ) * gLap F (ouPoint D N t w x)) ∂(gueBlocks D N)) t := by
  obtain ⟨h1, h2⟩ := gue_bounds F B (fun j hj1 hj2 => hB j hj2)
  have h0 : ∀ x, ‖F x‖ ≤ B := fun x => by
    have := hB 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (h0 0)
  have hFc : Continuous F := hF.continuous
  have hDc : Continuous (fderiv ℝ F) := hF.continuous_fderiv two_ne_zero
  -- the scalars at `t` and the bound on `S`
  have hexp1 : ∀ s : ℝ, 0 < s → Real.exp (-s) < 1 := fun s hs =>
    Real.exp_lt_one_iff.mpr (by linarith)
  have hexp0 : ∀ s : ℝ, 0 < Real.exp (-s) := fun s => Real.exp_pos _
  set σ : ℝ := Real.sqrt (1 - Real.exp (-t)) with hσdef
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr (by linarith [hexp1 t ht])
  have hσ1 : σ ≤ 1 := by
    rw [hσdef]
    calc Real.sqrt (1 - Real.exp (-t)) ≤ Real.sqrt 1 :=
          Real.sqrt_le_sqrt (by linarith [hexp0 t])
      _ = 1 := Real.sqrt_one
  set σ₀ : ℝ := Real.sqrt (1 - Real.exp (-(t / 2))) with hσ₀def
  have hσ₀ : 0 < σ₀ := Real.sqrt_pos.mpr (by linarith [hexp1 (t / 2) (by linarith)])
  set κ : ℝ := 1 / (2 * σ₀) with hκdef
  have hκ0 : 0 < κ := by positivity
  set S : Set ℝ := Set.Ioo (t / 2) (2 * t) with hSdef
  have hS : S ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
  have hcont : ∀ s : ℝ, Continuous fun x : Fin D → Coords N => ouPoint D N s w x := fun s => by
    unfold ouPoint
    fun_prop
  -- the derivative of the integrand in `s`
  set F' : ℝ → (Fin D → Coords N) → ℂ := fun s x => fderiv ℝ F (ouPoint D N s w x)
    ((-(1 / 2 : ℝ) * Real.exp (-s / 2)) • w +
      (Real.exp (-s) / (2 * Real.sqrt (1 - Real.exp (-s)))) • x) with hF'
  have hbound : ∀ s ∈ S, ∀ x : Fin D → Coords N,
      ‖F' s x‖ ≤ B * (‖w‖ / 2) + B * κ * ‖x‖ := by
    intro s hs x
    have hs0 : 0 < s := by
      have := hs.1
      linarith
    have ha : ‖(-(1 / 2 : ℝ) * Real.exp (-s / 2))‖ ≤ 1 / 2 := by
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        abs_of_pos (Real.exp_pos _)]
      have : Real.exp (-s / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith
    have hσs : σ₀ ≤ Real.sqrt (1 - Real.exp (-s)) := by
      refine Real.sqrt_le_sqrt ?_
      have : Real.exp (-s) ≤ Real.exp (-(t / 2)) := Real.exp_le_exp.mpr (by linarith [hs.1])
      linarith
    have hσ' : ‖Real.exp (-s) / (2 * Real.sqrt (1 - Real.exp (-s)))‖ ≤ κ := by
      have hpos : 0 < Real.sqrt (1 - Real.exp (-s)) := lt_of_lt_of_le hσ₀ hσs
      rw [Real.norm_eq_abs, abs_of_pos (div_pos (hexp0 s) (mul_pos two_pos hpos))]
      rw [hκdef, div_le_div_iff₀ (mul_pos two_pos hpos) (mul_pos two_pos hσ₀)]
      have : Real.exp (-s) ≤ 1 := (hexp1 s hs0).le
      nlinarith
    calc ‖F' s x‖ ≤ ‖fderiv ℝ F (ouPoint D N s w x)‖ * ‖(-(1 / 2 : ℝ) * Real.exp (-s / 2)) • w +
          (Real.exp (-s) / (2 * Real.sqrt (1 - Real.exp (-s)))) • x‖ :=
          (fderiv ℝ F _).le_opNorm _
      _ ≤ B * (‖w‖ / 2 + κ * ‖x‖) := by
          refine mul_le_mul (h1 _) ?_ (norm_nonneg _) hB0
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
          nlinarith [norm_nonneg w, norm_nonneg x, mul_le_mul_of_nonneg_right ha (norm_nonneg w),
            mul_le_mul_of_nonneg_right hσ' (norm_nonneg x)]
      _ = B * (‖w‖ / 2) + B * κ * ‖x‖ := by ring
  have hderiv : ∀ s ∈ S, ∀ x : Fin D → Coords N,
      HasDerivAt (fun r => F (ouPoint D N r w x)) (F' s x) s := by
    intro s hs x
    have hs0 : 0 < s := by
      have := hs.1
      linarith
    exact (hF.differentiable (by norm_num) (ouPoint D N s w x)).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_ouPoint D N w x s hs0)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gueBlocks D N)
    (F := fun s x => F (ouPoint D N s w x)) (F' := F') (x₀ := t) (s := S)
    (bound := fun x => B * (‖w‖ / 2) + B * κ * ‖x‖) hS
    (Filter.Eventually.of_forall fun s => (hFc.comp (hcont s)).aestronglyMeasurable)
    (Integrable.of_bound (hFc.comp (hcont t)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => h0 _))
    (by
      refine ((hDc.comp (hcont t)).clm_apply ?_).aestronglyMeasurable
      fun_prop)
    (Filter.Eventually.of_forall fun x s hs => hbound s hs x)
    ((integrable_const _).add ((gue_integrable_norm D N).const_mul (B * κ)))
    (Filter.Eventually.of_forall fun x s hs => hderiv s hs x)
  have iw : Integrable (fun x => fderiv ℝ F (ouPoint D N t w x) w) (gueBlocks D N) :=
    Integrable.of_bound ((hDc.comp (hcont t)).clm_apply continuous_const).aestronglyMeasurable
      (B * ‖w‖) (Filter.Eventually.of_forall fun x =>
        ((fderiv ℝ F _).le_opNorm w).trans (mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _)))
  have ix : Integrable (fun x => fderiv ℝ F (ouPoint D N t w x) x) (gueBlocks D N) :=
    ((gue_integrable_norm D N).const_mul B).mono'
      ((hDc.comp (hcont t)).clm_apply continuous_id).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x =>
        ((fderiv ℝ F _).le_opNorm x).trans (mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _)))
  have ig : Integrable (fun x => gLap F (ouPoint D N t w x)) (gueBlocks D N) :=
    ou_integrable_gLap D N F B hF h1 h2 (Real.exp (-t / 2) • w) σ hσ0 hσ1
  have ibp := ou_ibp D N F B hF h1 h2 (Real.exp (-t / 2) • w) σ hσ0 hσ1
  have hF'eq : ∀ x, F' t x =
      ((-(1 / 2 : ℝ) * Real.exp (-t / 2) : ℝ) : ℂ) * fderiv ℝ F (ouPoint D N t w x) w +
        ((Real.exp (-t) / (2 * σ) : ℝ) : ℂ) * fderiv ℝ F (ouPoint D N t w x) x := by
    intro x
    simp only [hF', map_add, map_smul, Complex.real_smul]
    rfl
  have hint : ∫ x, F' t x ∂(gueBlocks D N) =
      ((-(1 / 2 : ℝ) * Real.exp (-t / 2) : ℝ) : ℂ) *
          ∫ x, fderiv ℝ F (ouPoint D N t w x) w ∂(gueBlocks D N) +
        ((Real.exp (-t) / (2 * σ) : ℝ) : ℂ) *
          ∫ x, fderiv ℝ F (ouPoint D N t w x) x ∂(gueBlocks D N) := by
    simp only [hF'eq]
    rw [integral_add (iw.const_mul _) (ix.const_mul _), integral_const_mul, integral_const_mul]
  have hpin : ∫ x, (-(1 / 2 : ℂ) * (Real.exp (-t / 2) : ℂ) * fderiv ℝ F (ouPoint D N t w x) w +
        (1 / 2 : ℂ) * (Real.exp (-t) : ℂ) * gLap F (ouPoint D N t w x)) ∂(gueBlocks D N) =
      (-(1 / 2 : ℂ) * (Real.exp (-t / 2) : ℂ)) *
          ∫ x, fderiv ℝ F (ouPoint D N t w x) w ∂(gueBlocks D N) +
        ((1 / 2 : ℂ) * (Real.exp (-t) : ℂ)) *
          ∫ x, gLap F (ouPoint D N t w x) ∂(gueBlocks D N) := by
    have e : ∀ x, (-(1 / 2 : ℂ) * (Real.exp (-t / 2) : ℂ) * fderiv ℝ F (ouPoint D N t w x) w +
        (1 / 2 : ℂ) * (Real.exp (-t) : ℂ) * gLap F (ouPoint D N t w x)) =
        (-(1 / 2 : ℂ) * (Real.exp (-t / 2) : ℂ)) * fderiv ℝ F (ouPoint D N t w x) w +
          ((1 / 2 : ℂ) * (Real.exp (-t) : ℂ)) * gLap F (ouPoint D N t w x) := fun x => by ring
    rw [integral_congr_ae (μ := gueBlocks D N) (Filter.Eventually.of_forall e)]
    rw [integral_add (iw.const_mul _) (ig.const_mul _), integral_const_mul, integral_const_mul]
  convert key.2 using 1
  rw [hpin, hint, show ∫ x, fderiv ℝ F (ouPoint D N t w x) x ∂(gueBlocks D N) =
    (σ : ℂ) * ∫ x, gLap F (ouPoint D N t w x) ∂(gueBlocks D N) from ibp]
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  push_cast
  field_simp

end RBMTransitionEdge

end
