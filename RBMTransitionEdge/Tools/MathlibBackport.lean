/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Copyright (c) 2021 Patrick Massot. All rights reserved.
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Smoothness of parametric integrals (backport from Mathlib v4.37.0-rc1)

The declarations below are copied verbatim from Mathlib v4.37.0-rc1, because the pinned Mathlib
v4.36.0-rc1 does not have them:
* `Mathlib/Analysis/Calculus/ContDiff/Comp.lean`, lines 38, 40, 42, 44–47 and 708–728;
* `Mathlib/Analysis/Calculus/ParametricIntegral.lean`, lines 72–83 and 266–533;
* `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`, lines 22–30 and 116–182.

Mathlib's names are kept unchanged and no statement is changed. `RBMTransitionEdge/Edge/CountCalc.lean` uses
`intervalIntegral.hasFDerivAt_integral_of_contDiffOn` and `ContDiff.parametric_intervalIntegral`.
This file is deleted when the repository moves to Mathlib v4.37.0-rc1 or later.
-/

public section
section
open Set Filter Function

open scoped Topology ContDiff

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {s t : Set E} {f : E → F}
  {g : F → G} {x x₀ : E} {m n : ℕ∞ω}

/-- Continuous differentiability of the partial derivative of a function `E × F → G` (given by its
curried form `f : E → F → G`) with respect to the right factor `F`. If `f` is Cⁿ⁺¹ on `s ×ˢ u` and
`u` is open, `fun x : E × F ↦ fderiv 𝕜 (f x.1) x.2` is at least Cⁿ on `s ×ˢ u`. -/
lemma ContDiffOn.fderiv_right {f : E → F → G} {s : Set E} {u : Set F} (hu : IsOpen u) {n : ℕ∞ω}
    (hf : ContDiffOn 𝕜 (n + 1) f.uncurry (s ×ˢ u)) :
    ContDiffOn 𝕜 n (fun x : E × F ↦ fderiv 𝕜 (f x.1) x.2) (s ×ˢ u) := by
  refine .congr (fun x hx ↦ ?_) fun x hx ↦ (fderivWithin_of_isOpen hu hx.2).symm
  exact .fderivWithin (f := fun x y ↦ f x.1 y)
    ((hf x hx).comp (f := fun x ↦ (x.1.1, x.2)) (x, x.2) (by fun_prop) (by grind [MapsTo]))
      contDiffWithinAt_snd hu.uniqueDiffOn le_rfl hx (by grind)

/-- Continuous differentiability of the partial derivative of a function `E × F → G` (given by its
curried form `f : E → F → G`) with respect to the left factor `E`. If `f` is Cⁿ⁺¹ on `u ×ˢ s` and
`u` is open, `fun x : E × F ↦ fderiv 𝕜 (fun y ↦ f y x.2) x.1` is at least Cⁿ on `u ×ˢ s`. -/
lemma ContDiffOn.fderiv_left {f : E → F → G} {u : Set E} (hu : IsOpen u) {s : Set F} {n : ℕ∞ω}
    (hf : ContDiffOn 𝕜 (n + 1) f.uncurry (u ×ˢ s)) :
    ContDiffOn 𝕜 n (fun x : E × F ↦ fderiv 𝕜 (fun y ↦ f y x.2) x.1) (u ×ˢ s) := by
  have hf' : ContDiffOn 𝕜 (n + 1) (fun x y ↦ f y x).uncurry (s ×ˢ u) := by
    exact hf.comp (ContinuousLinearEquiv.prodComm _ _ _).contDiff.contDiffOn <| mapsTo_swap_prod _ _
  exact (hf'.fderiv_right hu).comp (ContinuousLinearEquiv.prodComm _ _ _).contDiff.contDiffOn <|
    mapsTo_swap_prod _ _

end

section
open TopologicalSpace MeasureTheory Filter Metric Set

open scoped Topology Filter ContDiff

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {H' : Type*} [NormedAddCommGroup H'] [NormedSpace 𝕜 H'] [MeasurableSpace H']
  [OpensMeasurableSpace H']

variable {F : H → α → E} {x₀ : H} {bound : α → ℝ} {s : Set H}

/-- A convenient special case of `hasFDerivAt_integral_of_dominated_of_fderiv_le`:
if there exist a neighbourhood `u` of `x₀` and a compact set `k` such that `F.uncurry : H × α → E`
is continuous and continuously differentiable in the first argument on `u ×ˢ k`, then for any
finite-measure set `s ⊆ k` a derivative of `fun x => ∫ a in s, F x a ∂μ` in `x₀` can be computed as
`∫ a in s, fderiv 𝕜 (fun x ↦ F x a) x₀ ∂μ`. -/
theorem hasFDerivAt_integral_of_continuousOn_fderiv [TopologicalSpace α]
    [OpensMeasurableSpace α] {F : H → α → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀) {k s : Set α}
    (hk : IsCompact k) (hs : MeasurableSet s) (hs' : μ s ≠ ⊤) (hsk : s ⊆ k)
    (hF₁ : ContinuousOn F.uncurry (u ×ˢ k))
    (hF₂ : ∀ a ∈ k, DifferentiableOn 𝕜 (fun x ↦ F x a) u)
    (hF₃ : ContinuousOn (fun x ↦ fderiv 𝕜 (fun y ↦ F y x.2) x.1) (u ×ˢ k)) :
    HasFDerivAt (fun x => ∫ a in s, F x a ∂μ)
      (∫ a in s, fderiv 𝕜 (fun x ↦ F x a) x₀ ∂μ) x₀ := by
  have hxu := mem_of_mem_nhds hu
  let F' := fun x : H × α ↦ ‖fderiv 𝕜 (fun y ↦ F y x.2) x.1‖
  have hF' : ContinuousOn F' _ := continuous_norm.comp_continuousOn hF₃
  -- via a compactness argument, find an `ε > 0` such that `F'` is bounded on `ball x₀ ε × k`
  let ⟨v, hxv, hvu, hv, B, hB⟩ :
      ∃ v : Set H, x₀ ∈ v ∧ v ⊆ u ∧ IsOpen v ∧ ∃ B, ∀ x ∈ v ×ˢ k, F' x < B := by
    let ⟨B, hB⟩ := (isCompact_singleton.prod hk).bddAbove_image <|
      hF'.mono <| prod_mono_left <| singleton_subset_iff.2 hxu
    have ⟨v, hv, hv'⟩ := generalized_tube_lemma_left (s := {x₀}) isCompact_singleton
      hk (s' := u) (n := F' ⁻¹' (Iio (B + 1))) (by
        refine nhdsSetWithin_mono_left ?_ <| hF'.preimage_mem_nhdsSetWithin_of_mem_nhdsSet
          (t := Iic B) (u := Iio (B + 1)) <| isOpen_Iio.mem_nhdsSet.2 (by simp)
        intro x hx
        exact ⟨prod_mono_left (by simp [hxu]) hx, mem_upperBounds.1 hB _ <| mem_image_of_mem _ hx⟩)
    rw [nhdsSetWithin_singleton, nhdsWithin_eq_nhds.mpr hu] at hv
    obtain ⟨w, hwuv, hw, hxw⟩ := _root_.mem_nhds_iff.mp <| Filter.inter_mem hu hv
    exact ⟨w, hxw, hwuv.trans inter_subset_left, hw, B + 1,
      fun x hx ↦ hv' <| prod_mono_left (hwuv.trans inter_subset_right) hx⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ B)
    (F' := fun x a ↦ fderiv 𝕜 (fun x ↦ F x a) x) (hv.mem_nhds hxv)
  · refine eventually_of_mem hu fun x hx ↦ ?_
    apply (hF₁.uncurry_left _ hx).aestronglyMeasurable_of_subset_isCompact hk hs hsk
  · apply (hF₁.uncurry_left _ hxu).integrableOn_of_subset_isCompact hk hs hsk hs'
  · apply (hF₃.uncurry_left _ hxu).aestronglyMeasurable_of_subset_isCompact hk hs hsk
  · filter_upwards [ae_restrict_mem hs] with a ha x hx using (hB (x, a) ⟨hx, hsk ha⟩).le
  · apply integrableOn_const hs'
  · filter_upwards [ae_restrict_mem hs] with a ha x hx
    apply DifferentiableAt.hasFDerivAt
    exact (hF₂ a (hsk ha) x (hvu hx)).differentiableAt (mem_nhds_iff.mpr ⟨_, hvu, hv, hx⟩)

/-- A version of `hasFDerivAt_integral_of_continuousOn_fderiv` where `α` is required to be Hausdorff
but `s` is not required to be measurable. -/
theorem hasFDerivAt_integral_of_continuousOn_fderiv_of_t2Space [TopologicalSpace α] [T2Space α]
    [OpensMeasurableSpace α] {F : H → α → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀) {k s : Set α}
    (hk : IsCompact k) (hs' : μ s ≠ ⊤) (hsk : s ⊆ k)
    (hF₁ : ContinuousOn F.uncurry (u ×ˢ k))
    (hF₂ : ∀ a ∈ k, DifferentiableOn 𝕜 (fun x ↦ F x a) u)
    (hF₃ : ContinuousOn (fun x ↦ fderiv 𝕜 (fun y ↦ F y x.2) x.1) (u ×ˢ k)) :
    HasFDerivAt (fun x => ∫ a in s, F x a ∂μ)
      (∫ a in s, fderiv 𝕜 (fun x ↦ F x a) x₀ ∂μ) x₀ := by
  have : μ.restrict (k ∩ toMeasurable μ s) = μ.restrict s :=
    Measure.restrict_inter_toMeasurable hs' hk.measurableSet hsk
  simp only [← this]
  apply hasFDerivAt_integral_of_continuousOn_fderiv hu hk
    (hk.measurableSet.inter (measurableSet_toMeasurable _ _)) ?_ inter_subset_left hF₁ hF₂ hF₃
  apply ((measure_mono inter_subset_right).trans_lt ?_).ne
  rw [measure_toMeasurable]
  exact hs'.lt_top

/-- A convenient special case of `hasFDerivAt_integral_of_continuousOn_fderiv`:
if `f.uncurry : H × H' → E` is continuously differentiable on `u ×ˢ k` for a neighbourhood `u`
of `x₀` and a compact set `k`, then for any finite-measure set `s ⊆ k` a derivative of
`fun x => ∫ a in s, f x a ∂μ` in `x₀` can be computed as
`∫ a in s, fderiv 𝕜 (fun x ↦ f x a) x₀ ∂μ`. -/
theorem hasFDerivAt_integral_of_contDiffOn {μ : Measure H'} {f : H → H' → E} {x₀ : H}
    {u : Set H} (hu : u ∈ 𝓝 x₀) {k s : Set H'}
    (hk : IsCompact k) (hs' : μ s ≠ ⊤) (hsk : s ⊆ k)
    (hF : ContDiffOn 𝕜 1 f.uncurry (u ×ˢ k)) :
    HasFDerivAt (fun x => ∫ a in s, f x a ∂μ) (∫ a in s, fderiv 𝕜 (fun x ↦ f x a) x₀ ∂μ) x₀ := by
  wlog hu' : IsOpen u with h
  · have ⟨u', hu'⟩ := _root_.mem_nhds_iff.1 hu
    exact h (hu'.2.1.mem_nhds hu'.2.2) hk hs' hsk (hF.mono <| prod_mono_left hu'.1) hu'.2.1
  refine hasFDerivAt_integral_of_continuousOn_fderiv_of_t2Space hu hk hs' hsk hF.continuousOn
    (fun a ha ↦ hF.differentiableOn_one.comp (by fun_prop)
      fun x hx ↦ (⟨hx, ha⟩ : (x, a) ∈ _ ×ˢ _)) ?_
  exact (hF.fderiv_left hu' (n := 0)).continuousOn

/-- Iterated differentiation under integral of `x ↦ ∫ F x a` on an open set `s`, assuming that each
function `x ↦ F x a` has a Taylor series of order `n`, with uniform integrability conditions on
the successive derivatives. -/
theorem hasFTaylorSeriesUpToOn_integral_of_le_bound {n : ℕ∞ω} {bound : ℕ → α → ℝ}
    {p : H → α → FormalMultilinearSeries 𝕜 H E} (hs : IsOpen s)
    (hF_meas : ∀ x ∈ s, ∀ (i : ℕ), i ≤ n → AEStronglyMeasurable (p x · i) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ∀ (i : ℕ), i ≤ n → ‖p x a i‖ ≤ bound i a)
    (bound_integrable : ∀ (i : ℕ), i ≤ n → Integrable (bound i) μ)
    (h_diff : ∀ᵐ a ∂μ, HasFTaylorSeriesUpToOn n (F · a) (p · a) s) :
    HasFTaylorSeriesUpToOn n (fun x ↦ ∫ a, F x a ∂μ) (fun x i ↦ ∫ a, p x a i ∂μ) s := by
  constructor
  · intro x hx
    simp only [ContinuousMultilinearMap.curry0_apply, Matrix.zero_empty]
    rw [ContinuousMultilinearMap.integral_apply]
    · apply integral_congr_ae
      filter_upwards [h_diff] with a ha
      simp [← ha.zero_eq x hx]
    · apply Integrable.mono' (bound_integrable 0 (by simp)) (hF_meas x hx 0 (by simp))
      filter_upwards [h_bound] with a ha using ha x hx 0 (by simp)
  · intro i hi x hx
    have h'i : (i + 1 : ℕ) ≤ n := ENat.add_one_natCast_le_withTop_of_lt hi
    apply HasFDerivAt.hasFDerivWithinAt
    change HasFDerivAt (fun x ↦ ∫ a, p x a i ∂μ)
      ((continuousMultilinearCurryLeftEquiv 𝕜 (fun i ↦ H) E).toContinuousLinearEquiv
        (∫ a, p x a i.succ ∂μ)) x
    rw [← ContinuousLinearEquiv.integral_comp_comm]
    have s_mem : s ∈ 𝓝 x := hs.mem_nhds hx
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := s) (bound := bound (i + 1)) s_mem
    · filter_upwards [s_mem] with y hy using hF_meas _ hy _ hi.le
    · apply Integrable.mono' (bound_integrable i hi.le) (hF_meas _ hx _ hi.le)
      filter_upwards [h_bound] with a ha using ha x hx i hi.le
    · apply Continuous.comp_aestronglyMeasurable (by fun_prop)
      exact hF_meas x hx i.succ h'i
    · filter_upwards [h_bound] with a ha y hy
      simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
      exact ha _ hy _ h'i
    · apply bound_integrable _ h'i
    · filter_upwards [h_diff] with a ha y hy
      exact (ha.fderivWithin i hi y hy).hasFDerivAt (hs.mem_nhds hy)
  · intro i hi
    apply continuousOn_of_dominated (bound := bound i)
    · intro y hy
      exact hF_meas y hy i hi
    · intro y hy
      filter_upwards [h_bound] with a ha using ha y hy i hi
    · apply bound_integrable i hi
    · filter_upwards [h_diff] with a ha using ha.cont i hi

open ContinuousMultilinearMap in
theorem hasFTaylorSeriesUpToOn_setIntegral_of_le_const
    {n : ℕ∞ω} {C : ℕ → ℝ} {μ : Measure H'}
    {p : H × H' → FormalMultilinearSeries 𝕜 (H × H') E} (hs : IsOpen s)
    {t : Set H'} {F : H → H' → E} (ht : IsSeparable t) (tmeas : MeasurableSet t) (hmut : μ t ≠ ⊤)
    (hF : HasFTaylorSeriesUpToOn n F.uncurry p (s ×ˢ t))
    (h_bound : ∀ x ∈ s, ∀ a ∈ t, ∀ (i : ℕ), i ≤ n → ‖p (x, a) i‖ ≤ C i) :
    HasFTaylorSeriesUpToOn n (fun x ↦ ∫ a in t, F x a ∂μ)
      (fun x i ↦ ∫ a in t, (p (x, a) i).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inl 𝕜 H H') ∂μ) s := by
  apply hasFTaylorSeriesUpToOn_integral_of_le_bound hs (bound := fun i a ↦ C i * ∏ (j : Fin i), 1)
  · intro x hx i hi
    apply ContinuousOn.aestronglyMeasurable_of_isSeparable ?_ tmeas ht
    apply Continuous.comp_continuousOn (g := compContinuousLinearMapL _) (by fun_prop)
      (f := fun y ↦ p (x, y) i)
    apply (hF.cont i hi).comp (by fun_prop)
    intro w hw
    exact ⟨hx, hw⟩
  · apply ae_restrict_of_forall_mem tmeas (fun w hw ↦ ?_)
    intro x hx i hi
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    have : ‖p (x, w) i‖ ≤ C i := h_bound x hx w hw i hi
    gcongr
    · exact le_trans (by positivity) this
    · exact ContinuousLinearMap.norm_inl_le_one 𝕜 H H'
  · intro i hi
    exact integrableOn_const hmut
  · apply ae_restrict_of_forall_mem tmeas (fun w hw ↦ ?_)
    let g : H →ᴬ[𝕜] H × H' :=
    { toFun := fun x ↦ (x, w)
      linear := LinearMap.inl 𝕜 H H'
      map_vadd' p v := by simp
      cont := by fun_prop }
    apply (hF.comp_continuousAffineMap g).mono
    simp only [ContinuousAffineMap.coe_mk, AffineMap.coe_mk, g]
    grind

open ContinuousMultilinearMap in
/-- If `f.uncurry : H × H' → E` is `Cⁿ` on `u ×ˢ k` for an open set `u` and a compact set `k`, then
given any finite-measure subset `s₀` of `k` the parametric integral `fun x ↦ ∫ a in s₀, f x a ∂μ`
is `Cⁿ` on `u` too. -/
lemma ContDiffOn.parametric_integral
    {μ : Measure H'} {f : H → H' → E} {u : Set H} (hu : IsOpen u)
    {s₀ k : Set H'} (hk : IsCompact k) {n : ℕ∞} (hs₀ : s₀ ⊆ k)
    (hf : ContDiffOn 𝕜 n f.uncurry (u ×ˢ k)) (mus₀ : μ s₀ ≠ ⊤) :
    ContDiffOn 𝕜 n (fun x ↦ ∫ a in s₀, f x a ∂μ) u := by
  /- Locally, this is already proved in `hasFTaylorSeriesOn_setIntegral_of_le_const` (which moreover
  gives a formula for the successive derivatives). To globalize, one covers the compact set `k`
  with finitely many sets on which the local property holds. Technically, this is more conveniently
  done using the induction principle `IsCompact.induction_on` in which one only needs to check
  the property locally, and invariance under binary union. -/
  intro x hx
  apply contDiffWithinAt_iff_forall_nat_le.2 (fun m hm ↦ ?_)
  suffices ∃ s, k ∩ k ⊆ s ∧ s ⊆ k ∧ MeasurableSet s ∧ ∀ t ⊆ s, MeasurableSet t → μ t ≠ ⊤ →
      ContDiffWithinAt 𝕜 m (fun x ↦ ∫ a in t, f x a ∂μ) u x by
    rcases this with ⟨s, ks, sk, -, hs⟩
    rw [show s = k by grind] at hs
    have : ContDiffWithinAt 𝕜 m (fun x ↦ ∫ a in k ∩ toMeasurable μ s₀, f x a ∂μ) u x := by
      apply hs _ inter_subset_left (hk.measurableSet.inter (measurableSet_toMeasurable _ _))
      apply ((measure_mono inter_subset_right).trans_lt ?_).ne
      rw [measure_toMeasurable]
      exact mus₀.lt_top
    convert this using 3
    exact (Measure.restrict_inter_toMeasurable mus₀ hk.measurableSet hs₀).symm
  apply hk.induction_on
    (p := fun s₀ ↦ ∃ s, k ∩ s₀ ⊆ s ∧ s ⊆ k ∧ MeasurableSet s ∧ ∀ t ⊆ s, MeasurableSet t →
      μ t ≠ ⊤ → ContDiffWithinAt 𝕜 m (fun x ↦ ∫ a in t, f x a ∂μ) u x)
  · simp only [inter_empty, empty_subset, true_and]
    exact ⟨∅, by simpa using contDiffWithinAt_const⟩
  · grind
  · -- check invariance of the property under binary union
    rintro s s' ⟨t, kt, tk, tmeas, ht⟩ ⟨t', kt', t'k, t'meas, ht'⟩
    refine ⟨t ∪ t', by grind, by grind, tmeas.union t'meas, fun v hv vmeas muv ↦ ?_⟩
    let v₁ := v ∩ t
    let v₂ := v \ v₁
    have v₁meas : MeasurableSet v₁ := vmeas.inter tmeas
    have v₂meas : MeasurableSet v₂ := vmeas.diff v₁meas
    have muv₁ : μ v₁ ≠ ⊤ := ((measure_mono inter_subset_left).trans_lt muv.lt_top).ne
    have muv₂ : μ v₂ ≠ ⊤ := ((measure_mono sdiff_subset).trans_lt muv.lt_top).ne
    have : ContDiffWithinAt 𝕜 m (fun x ↦ ∫ a in v₁, f x a ∂μ + ∫ a in v₂, f x a ∂μ) u x :=
      (ht v₁ inter_subset_right v₁meas muv₁).add (ht' v₂ (by grind) v₂meas muv₂)
    apply this.congr_of_mem (fun y hy ↦ ?_) hx
    rw [show v = v₁ ∪ v₂ by grind, setIntegral_union disjoint_sdiff_left.symm v₂meas]
    · exact (hf.continuousOn.uncurry_left _ hy).integrableOn_of_subset_isCompact
        hk v₁meas (inter_subset_right.trans tk) muv₁
    · exact (hf.continuousOn.uncurry_left _ hy).integrableOn_of_subset_isCompact
        hk v₂meas (by grind only [= subset_def, = Set.mem_sdiff, = mem_union]) muv₂
  -- check the property locally using `hasFTaylorSeriesOn_setIntegral_of_le_const`
  intro y hy
  obtain ⟨v, v_mem, p, hp⟩ : ∃ v ∈ 𝓝[insert (x, y) (u ×ˢ k)] (x, y), ∃ p,
    HasFTaylorSeriesUpToOn m (Function.uncurry f) p v := hf (x, y) ⟨hx, hy⟩ m hm
  obtain ⟨u', u'_mem, k', k'_mem, u'_open,  k'meas, k'k, hk'v, hk'_bound⟩ :
      ∃ u' ∈ 𝓝 x, ∃ k' ∈ 𝓝[k] y, IsOpen u' ∧ MeasurableSet k' ∧ k' ⊆ k ∧ u' ×ˢ k' ⊆ v
      ∧ ∀ N ≤ m, ∀ z ∈ u' ×ˢ k', ‖p z N‖ < 1 + ‖p (x, y) N‖ := by
    rw [show insert (x, y) (u ×ˢ k) = u ×ˢ k from insert_eq_of_mem (by exact ⟨hx, hy⟩)] at v_mem
    let v'' := ⋂ N ∈ Finset.Iic m, {z | ‖p z N‖ < 1 + ‖p (x, y) N‖}
    have : v'' ∈ 𝓝[u ×ˢ k] (x, y) := by
      apply (Filter.biInter_finset_mem _).2 (fun i hi ↦ ?_)
      apply nhdsWithin_le_of_mem v_mem
      have xyv : (x, y) ∈ v := mem_of_mem_nhdsWithin (by exact ⟨hx, hy⟩) v_mem
      have : ContinuousWithinAt (fun z ↦ ‖p z i‖) v (x, y) :=
        (hp.cont i (by simpa using hi) (x, y) xyv).norm
      exact this.preimage_mem_nhdsWithin (Iio_mem_nhds (by linarith))
    have v'_mem : v ∩ v'' ∈ 𝓝[u ×ˢ k] (x, y) := by
      apply Filter.inter_mem v_mem this
    rw [nhdsWithin_prod_eq, Filter.mem_prod_iff, IsOpen.nhdsWithin_eq hu hx] at v'_mem
    rcases v'_mem with ⟨u', u'_mem, t', t'_mem, ht'⟩
    rw [mem_nhdsWithin] at t'_mem
    rcases t'_mem with ⟨t'', t''_open, t''_mem, ht''⟩
    rcases _root_.mem_nhds_iff.1 u'_mem with ⟨u'', hu'', u''_open, xu''⟩
    refine ⟨u'', u''_open.mem_nhds xu'', t'' ∩ k, ?_, u''_open,
      t''_open.measurableSet.inter hk.measurableSet, inter_subset_right, ?_, ?_⟩
    · rw [inter_comm]
      exact inter_mem_nhdsWithin _ (t''_open.mem_nhds t''_mem)
    · exact Subset.trans (by gcongr) (ht'.trans inter_subset_left)
    · intro i hi z z_mem
      have : z ∈ v'' := by
        have : u'' ×ˢ (t'' ∩ k) ⊆ v'' := Subset.trans (by gcongr) (ht'.trans inter_subset_right)
        exact this z_mem
      simp only [Finset.mem_Iic, mem_iInter, mem_ofPred_eq, v''] at this
      exact this i hi
  refine ⟨k', k'_mem, k', inter_subset_right, k'k, k'meas, fun t tk' tmeas hmut ↦ ?_⟩
  have : HasFTaylorSeriesUpToOn m (fun x ↦ ∫ a in t, f x a ∂μ)
      (fun x i ↦ ∫ a in t, (p (x, a) i).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inl 𝕜 H H') ∂μ) u' := by
    apply hasFTaylorSeriesUpToOn_setIntegral_of_le_const u'_open
      (hk.isSeparable.mono (tk'.trans k'k)) tmeas hmut (hp.mono (by grind))
        (C := fun i ↦ 1 + ‖p (x, y) i‖)
    intro x' hx' a ha i hi
    exact (hk'_bound i (mod_cast hi) (x', a) ⟨hx', tk' ha⟩).le
  apply ContDiffWithinAt.mono_of_mem_nhdsWithin ?_ (nhdsWithin_le_nhds u'_mem)
  exact contDiffWithinAt_nat.2 ⟨u', nhdsWithin_le_nhds u'_mem, _, this⟩

/-- If `f.uncurry : H × H' → E` is `Cⁿ`, the parametric integral `fun x ↦ ∫ a in s₀, f x a ∂μ`
over a finite-measure set `s₀` contained in a compact set `k` is `Cⁿ` too. -/
lemma ContDiff.parametric_integral {μ : Measure H'} {f : H → H' → E}
    {k s₀ : Set H'} (hk : IsCompact k) (hs₀ : s₀ ⊆ k) (mus₀ : μ s₀ ≠ ⊤) {n : ℕ∞}
    (hf : ContDiff 𝕜 n f.uncurry) :
    ContDiff 𝕜 n (fun x ↦ ∫ a in s₀, f x a ∂μ) :=
  contDiffOn_univ.1 <| hf.contDiffOn.parametric_integral isOpen_univ hk hs₀ mus₀

end

section
open TopologicalSpace MeasureTheory Filter Set

open scoped Topology Filter Interval

variable {𝕜 : Type*} [RCLike 𝕜] {μ : Measure ℝ} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace 𝕜 E] {H : Type*} [NormedAddCommGroup H]
  [NormedSpace 𝕜 H] {s : Set H} {a b : ℝ} {bound : ℝ → ℝ}

namespace intervalIntegral

/-- A convenient special case of `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`:
if there exists a neighbourhood `u` of `x₀` such that `f.uncurry : H × ℝ → E` is continuous on
`u ×ˢ [[a, b]]` and differentiable on `u` in the first argument for every `t ∈ [[a, b]]` and that
derivative is continuous on `u ×ˢ [[a, b]]`, then a derivative of
`fun x => ∫ t in a..b, f x t ∂μ` in `x₀` can be computed as
`∫ t in a..b, fderiv 𝕜 (fun x ↦ f x t) x₀ ∂μ`. -/
theorem hasFDerivAt_integral_of_continuousOn_fderiv [IsLocallyFiniteMeasure μ]
    {f : H → ℝ → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀) {a b : ℝ}
    (hF₁ : ContinuousOn f.uncurry (u ×ˢ [[a, b]]))
    (hF₂ : ∀ t ∈ [[a, b]], DifferentiableOn 𝕜 (fun x ↦ f x t) u)
    (hF₃ : ContinuousOn (fun x ↦ fderiv 𝕜 (fun y ↦ f y x.2) x.1) (u ×ˢ [[a, b]])) :
    HasFDerivAt (fun x => ∫ t in a..b, f x t ∂μ)
      (∫ t in a..b, fderiv 𝕜 (fun x ↦ f x t) x₀ ∂μ) x₀ := by
  wlog hab : a ≤ b with h
  · simp_rw [integral_symm b a]
    exact (h hu (uIcc_comm a b ▸ hF₁) (uIcc_comm a b ▸ hF₂) (uIcc_comm a b ▸ hF₃)
      (le_of_not_ge hab)).neg
  simp_rw [integral_of_le hab, ← uIoc_of_le hab]
  apply _root_.hasFDerivAt_integral_of_continuousOn_fderiv_of_t2Space
    hu isCompact_uIcc ?_ uIoc_subset_uIcc hF₁ hF₂ hF₃
  exact ((measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne

/-- A convenient special case of `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`:
if `f.uncurry : H × ℝ → E` is continuously differentiable on `u ×ˢ [[a, b]]` for a neighbourhood `u`
of `x₀`, then a derivative of `fun x => ∫ t in a..b, f x t ∂μ` in `x₀` can be computed as
`∫ t in a..b, fderiv ℝ (fun x ↦ f x t) x₀ ∂μ`. -/
theorem hasFDerivAt_integral_of_contDiffOn [IsLocallyFiniteMeasure μ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : H → ℝ → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀) {a b : ℝ}
    (hF : ContDiffOn ℝ 1 f.uncurry (u ×ˢ [[a, b]])) :
    HasFDerivAt (fun x => ∫ t in a..b, f x t ∂μ)
      (∫ t in a..b, fderiv ℝ (fun x ↦ f x t) x₀ ∂μ) x₀ := by
  wlog hab : a < b with h
  · obtain hab | hab := lt_or_eq_of_le <| le_of_not_gt hab
    · simp only [integral_symm b a]
      exact (h hu (μ := μ) (uIcc_comm a b ▸ hF) hab).neg
    · simp [hab, hasFDerivAt_const]
  simp_rw [integral_of_le hab.le, ← uIoc_of_le hab.le]
  apply _root_.hasFDerivAt_integral_of_contDiffOn hu isCompact_uIcc ?_ uIoc_subset_uIcc hF
  exact ((measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne

end intervalIntegral

/-- If `f.uncurry : H × ℝ → E` is Cⁿ on `u ×ˢ [[a, b]]`, the parametric integral
`fun x ↦ ∫ t in a..b, f x t ∂μ` is Cⁿ on `u` too. -/
lemma ContDiffOn.parametric_intervalIntegral {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : H → ℝ → E} {u : Set H} (hu : IsOpen u) {a b : ℝ} {n : ℕ∞}
    (hf : ContDiffOn ℝ n f.uncurry (u ×ˢ [[a, b]])) :
    ContDiffOn ℝ n (fun x ↦ ∫ t in a..b, f x t ∂μ) u := by
  wlog hab : a < b with h
  · obtain hab | hab := lt_or_eq_of_le <| le_of_not_gt hab
    · simp_rw [intervalIntegral.integral_symm b a]
      exact (h hu (uIcc_comm a b ▸ hf) hab).neg
    · simp [hab, contDiffOn_const]
  simp_rw [intervalIntegral.integral_of_le hab.le]
  apply hf.parametric_integral hu isCompact_Icc
  · simpa [hab.le] using Ioc_subset_Icc_self
  · exact ((measure_mono Ioc_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne

/-- If `f : H × ℝ → E` is Cⁿ, the parametric integral
`fun x ↦ ∫ t in a..b, f (x, t) ∂μ` is Cⁿ too. -/
lemma ContDiff.parametric_intervalIntegral {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : H × ℝ → E} {a b : ℝ} {n : ℕ∞}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (fun x ↦ ∫ t in a..b, f (x, t) ∂μ) :=
  contDiffOn_univ.1 <| hf.contDiffOn.parametric_intervalIntegral isOpen_univ

end

end
