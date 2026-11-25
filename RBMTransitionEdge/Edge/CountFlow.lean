module

public import RBMTransitionEdge.Edge.CountCalc
public import RBMTransitionEdge.Prob.GaussianIBP

@[expose] public section

/-!
# The single-time derivative of the edge count along `H_t`

The terms of the display before (4.9) [eq:prodnGt] written entry by entry, the law (4.3)
[eq:eq_in_law_H] of `H_t` through one block of size `DN`, the Gaussian Laplacian and the drift of a
function of the array entry by entry, the derivative of `t ↦ E_{H_t} F(A)` for `t > 0`, and the
fundamental theorem of calculus on `[0, T]` (proof of Lemma 4.3 [rescomY]).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `E Σ_{x,y} h_{xy} ∂_{xy} G(h)` under `μ`, written entry by entry as
`Σ_{i,j} κ_{ij} E h̄_{ij} ∂_{w̄} G(setEntry h i j w)|_{w = h_{ij}}` (display before
(4.9) [eq:prodnGt]). -/
def entryDrift {D N : ℕ} (G : (Idx D N → Idx D N → ℂ) → ℝ)
    (μ : Measure (Idx D N → Idx D N → ℂ)) : ℂ :=
  ∑ i, ∑ j, driftWt i j *
    ∫ h, starRingEnd ℂ (h i j) * wirt 0 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ

/-- `E Σ_{x,y} ∂_{xy} ∂_{yx} G(h)` under `μ`, entry by entry (display before
(4.9) [eq:prodnGt]). -/
def entryGen {D N : ℕ} (G : (Idx D N → Idx D N → ℂ) → ℝ)
    (μ : Measure (Idx D N → Idx D N → ℂ)) : ℂ :=
  ∑ i, ∑ j, genWt i j * ∫ h, wirt 1 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ

/-- The right side of the display before (4.9) [eq:prodnGt] under `μ`:
`(2DN)⁻¹ E Σ ∂_{xy} ∂_{yx} G - ½ E Σ h_{xy} ∂_{xy} G`. -/
def entryDeriv {D N : ℕ} (G : (Idx D N → Idx D N → ℂ) → ℝ)
    (μ : Measure (Idx D N → Idx D N → ℂ)) : ℂ :=
  -(1 / 2 : ℂ) * entryDrift G μ + (1 / 2 : ℂ) * (((D * N : ℕ) : ℂ))⁻¹ * entryGen G μ

/-- `E Σ_{x,y} ((DN)⁻¹ - s_{xy}) ∂_{xy} ∂_{yx} G(h)` under `μ`, `s_{xy}` of (2.14) [eq:sij]: the
first term of (4.9) [eq:prodnGt] without the factor `e^{-t}/2`, that is `E ℱ₂`. -/
def entryF2 {D N : ℕ} (G : (Idx D N → Idx D N → ℂ) → ℝ)
    (μ : Measure (Idx D N → Idx D N → ℂ)) : ℂ :=
  ∑ i, ∑ j, genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
    ∫ h, wirt 1 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) ∂μ


/-- The array of the coordinates of one block of size `DN`. -/
private def CF_arrLin (D N : ℕ) : (Fin 1 → Coords (D * N)) →ₗ[ℝ] (Idx D N → Idx D N → ℂ) where
  toFun x := Matrix.of.symm (gueIdx D N (x 0))
  map_add' x y := by
    funext p q
    simp only [gueIdx, Pi.add_apply, wig_add]
    rfl
  map_smul' c x := by
    funext p q
    simp only [gueIdx, Pi.smul_apply, wig_smul, RingHom.id_apply, Complex.real_smul]
    rfl

private def CF_arr (D N : ℕ) : (Fin 1 → Coords (D * N)) →L[ℝ] (Idx D N → Idx D N → ℂ) :=
  LinearMap.toContinuousLinearMap (CF_arrLin D N)

private lemma CF_arr_apply (D N : ℕ) (x : Fin 1 → Coords (D * N)) :
    CF_arr D N x = Matrix.of.symm (gueIdx D N (x 0)) := rfl

private lemma CF_wig_herm (n : ℕ) (c : Coords n) : (wig n c).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [wig, star_mul', Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.not_gt, h.ne']
  · subst h
    simp
  · simp [h, h.ne, h.not_gt, h.ne']

private lemma CF_arr_herm (D N : ℕ) (x : Fin 1 → Coords (D * N)) :
    (Matrix.of (CF_arr D N x)).IsHermitian := by
  rw [CF_arr_apply, Equiv.apply_symm_apply]
  exact (CF_wig_herm _ _).submatrix _

private lemma CF_symArr_arr (D N : ℕ) (x : Fin 1 → Coords (D * N)) :
    symArr (CF_arr D N x) = CF_arr D N x :=
  symArr_of_isHermitian _ (CF_arr_herm D N x)

private lemma CF_continuous_blockEmb (D N : ℕ) : Continuous (blockEmb D N) := by
  unfold blockEmb
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun k => ?_
    exact continuous_const.mul ((continuous_apply _).comp
      ((continuous_fst).comp (continuous_apply _)))
  · refine continuous_pi fun k => continuous_pi fun l => ?_
    by_cases h : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1
    · simp only [h, ↓reduceIte]
      exact continuous_const.mul ((continuous_apply _).comp ((continuous_apply _).comp
        ((continuous_snd).comp (continuous_apply _))))
    · simp only [h, ↓reduceIte]
      exact continuous_const

private instance CF_instOMS1 (D N : ℕ) :
    OpensMeasurableSpace ((Fin D → Coords N) × Coords (D * N)) :=
  @Prod.opensMeasurableSpace _ _ _ _ _ _ _ _ inferInstance

private instance CF_instOMS2 (D N : ℕ) :
    OpensMeasurableSpace ((Fin D → Coords N) × (Fin 1 → Coords (D * N))) :=
  @Prod.opensMeasurableSpace _ _ _ _ _ _ _ _ inferInstance

private abbrev CF_Om (D N : ℕ) := (Fin D → Coords N) × (Fin 1 → Coords (D * N))

private def CF_Psi (D N : ℕ) (t : ℝ) (q : CF_Om D N) : Idx D N → Idx D N → ℂ :=
  CF_arr D N (ouPoint 1 (D * N) t (fun _ => blockEmb D N q.1) q.2)

private lemma CF_continuous_Psi (D N : ℕ) (t : ℝ) : Continuous (CF_Psi D N t) := by
  unfold CF_Psi ouPoint
  have h1 : Continuous fun q : CF_Om D N => (fun _ : Fin 1 => blockEmb D N q.1) :=
    continuous_pi fun _ => (CF_continuous_blockEmb D N).comp continuous_fst
  exact (CF_arr D N).continuous.comp
    ((h1.const_smul (Real.exp (-t / 2))).add
      ((continuous_snd (X := Fin D → Coords N) (Y := Fin 1 → Coords (D * N))).const_smul
        (Real.sqrt (1 - Real.exp (-t)))))

private def CF_psi (D N : ℕ) (c : Coords (D * N)) : Idx D N → Idx D N → ℂ :=
  Matrix.of.symm (gueIdx D N c)

private def CF_phi (D N : ℕ) (t : ℝ) (p : (Fin D → Coords N) × Coords (D * N)) :
    Coords (D * N) :=
  Real.exp (-t / 2) • blockEmb D N p.1 + Real.sqrt (1 - Real.exp (-t)) • p.2

private lemma CF_continuous_psi (D N : ℕ) : Continuous (CF_psi D N) := by
  have : CF_psi D N = fun c => CF_arr D N (fun _ => c) := rfl
  rw [this]
  exact (CF_arr D N).continuous.comp (continuous_pi fun _ => continuous_id)

private lemma CF_continuous_phi (D N : ℕ) (t : ℝ) : Continuous (CF_phi D N t) := by
  unfold CF_phi
  exact (((CF_continuous_blockEmb D N).comp continuous_fst).const_smul
    (Real.exp (-t / 2))).add (continuous_snd.const_smul (Real.sqrt (1 - Real.exp (-t))))

private lemma CF_ouMatLaw_eq (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) :
    ouMatLaw D N L t = ((blockLaw D N L).prod (gueBlocks 1 (D * N))).map (CF_Psi D N t) := by
  have hmp : MeasurePreserving
      (Prod.map (id : (Fin D → Coords N) → (Fin D → Coords N))
        (MeasurableEquiv.funUnique (Fin 1) (Coords (D * N))))
      ((blockLaw D N L).prod (gueBlocks 1 (D * N)))
      ((blockLaw D N L).prod (gueLaw (D * N))) :=
    (MeasurePreserving.id _).prod (measurePreserving_funUnique (gueLaw (D * N)) (Fin 1))
  have h1 : ouMatLaw D N L t = (((blockLaw D N L).prod (gueLaw (D * N))).map (CF_phi D N t)).map
      (CF_psi D N) := rfl
  rw [h1, Measure.map_map (CF_continuous_psi D N).measurable (CF_continuous_phi D N t).measurable,
    ← hmp.map_eq, Measure.map_map ((CF_continuous_psi D N).measurable.comp
      (CF_continuous_phi D N t).measurable) hmp.measurable]
  rfl


private lemma CF_integral_ou (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ)
    (f : (Idx D N → Idx D N → ℂ) → ℂ) (hf : Measurable f) :
    ∫ h, f h ∂(ouMatLaw D N L t) =
      ∫ p, f (CF_Psi D N t p) ∂((blockLaw D N L).prod (gueBlocks 1 (D * N))) := by
  rw [CF_ouMatLaw_eq]
  exact integral_map (CF_continuous_Psi D N t).measurable.aemeasurable hf.aestronglyMeasurable

/-- (4.3) [eq:eq_in_law_H] through one block of size `DN`: for bounded measurable `f`,
`E_{H_t} f = E_H E_W f(e^{-t/2} H + √(1 - e^{-t}) W)`, with `W` the coordinates of
`gueBlocks 1 (DN)` and `H` embedded by `blockEmb`. -/
theorem ouMatLaw_integral_ouPoint (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ)
    (f : (Idx D N → Idx D N → ℂ) → ℂ) (hf : Measurable f) (B : ℝ) (hB : ∀ h, ‖f h‖ ≤ B) :
    ∫ h, f h ∂(ouMatLaw D N L t) =
      ∫ w, (∫ x, f (Matrix.of.symm (gueIdx D N
          (ouPoint 1 (D * N) t (fun _ => blockEmb D N w) x 0))) ∂(gueBlocks 1 (D * N)))
        ∂(blockLaw D N L)  := by
  rw [CF_integral_ou D N L t f hf]
  have hint : Integrable (fun p => f (CF_Psi D N t p))
      ((blockLaw D N L).prod (gueBlocks 1 (D * N))) :=
    Integrable.of_bound (hf.comp (CF_continuous_Psi D N t).measurable).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun p => hB _)
  rw [integral_prod _ hint]
  rfl

/-! ### Calculus of the second derivative `d2` and of the Wirtinger derivatives -/

section Calc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `D²Φ(x)[v, v]` is the second Fréchet derivative applied to `(v, v)`. -/
private lemma CF_d2_eq (Φ : E → ℂ) (hΦ : ContDiff ℝ 2 Φ) (x v : E) :
    d2 Φ x v = fderiv ℝ (fderiv ℝ Φ) x v v := by
  have hFc : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  unfold d2
  have := fderiv_clm_apply (c := fderiv ℝ Φ) (u := fun _ : E => v)
    (hFc.differentiable (by norm_num) x) (differentiableAt_const v)
  rw [this]
  simp

/-- The derivative of `y ↦ Φ (c + M y)` for a continuous linear `M`. -/
private lemma CF_fderiv_affine (Φ : E → ℂ) (hΦ : ContDiff ℝ 1 Φ) (c : E) (M : F →L[ℝ] E)
    (y u : F) : fderiv ℝ (fun y => Φ (c + M y)) y u = fderiv ℝ Φ (c + M y) (M u) := by
  have hA : HasFDerivAt (fun y : F => c + M y) M y := M.hasFDerivAt.const_add c
  have h : HasFDerivAt (fun y : F => Φ (c + M y)) ((fderiv ℝ Φ (c + M y)).comp M) y :=
    (hΦ.differentiable (by norm_num) (c + M y)).hasFDerivAt.comp y hA
  rw [h.fderiv]
  rfl

/-- `d2` of `y ↦ Φ (c + M y)`. -/
private lemma CF_d2_affine (Φ : E → ℂ) (hΦ : ContDiff ℝ 2 Φ) (c : E) (M : F →L[ℝ] E)
    (y u : F) : d2 (fun y => Φ (c + M y)) y u = d2 Φ (c + M y) (M u) := by
  have hH : ContDiff ℝ 1 (fun z => fderiv ℝ Φ z (M u)) :=
    (hΦ.fderiv_right (by norm_num)).clm_apply contDiff_const
  have e : (fun y' => fderiv ℝ (fun y => Φ (c + M y)) y' u) =
      fun y' => (fun z => fderiv ℝ Φ z (M u)) (c + M y') := by
    funext y'
    exact CF_fderiv_affine Φ (hΦ.of_le (by norm_num)) c M y' u
  unfold d2
  rw [e, CF_fderiv_affine (fun z => fderiv ℝ Φ z (M u)) hH c M y u]

/-- `d2` is quadratic in the direction. -/
private lemma CF_d2_smul (Φ : E → ℂ) (hΦ : ContDiff ℝ 2 Φ) (s : ℝ) (x v : E) :
    d2 Φ x (s • v) = ((s * s : ℝ) : ℂ) * d2 Φ x v := by
  rw [CF_d2_eq Φ hΦ, CF_d2_eq Φ hΦ]
  simp only [map_smul, Complex.real_smul, _root_.smul_apply]
  push_cast
  ring

/-- `d2` vanishes in the direction `0`. -/
private lemma CF_d2_zero (Φ : E → ℂ) (x : E) : d2 Φ x 0 = 0 := by
  simp [d2]

end Calc

/-- The derivative of a real-differentiable `g : ℂ → ℂ` in the Wirtinger form
`Dg(z) u = u ∂_w g + ū ∂_{w̄} g`. -/
private lemma CF_fderiv_wirt (g : ℂ → ℂ) (z u : ℂ) :
    fderiv ℝ g z u = u * dW g z + starRingEnd ℂ u * dWbar g z := by
  have hu : u = (u.re : ℝ) • (1 : ℂ) + (u.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have e : fderiv ℝ g z u = (u.re : ℂ) * fderiv ℝ g z 1 + (u.im : ℂ) * fderiv ℝ g z Complex.I := by
    conv_lhs => rw [hu]
    rw [map_add, map_smul, map_smul]
    simp only [Complex.real_smul]
  rw [e]
  unfold dW dWbar
  have hc : starRingEnd ℂ u = (u.re : ℂ) - (u.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hu' : u = (u.re : ℂ) + (u.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  generalize (u.re : ℝ) = r at *
  generalize (u.im : ℝ) = m at *
  linear_combination (-(1 / 2) * (fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I)) * hu' +
    (-(1 / 2) * (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I)) * hc +
    ((m : ℂ) * fderiv ℝ g z Complex.I) * Complex.I_sq

/-- `∂_w ∂_{w̄} g = ¼ (D²g[1, 1] + D²g[i, i])` for `g` of class `C²`. -/
private lemma CF_wirt11 (g : ℂ → ℂ) (hg : ContDiff ℝ 2 g) (z : ℂ) :
    wirt 1 1 g z = (1 / 4 : ℂ) * (d2 g z 1 + d2 g z Complex.I) := by
  have hgc : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have ha : Differentiable ℝ (fun y => fderiv ℝ g y 1) :=
    (hgc.clm_apply contDiff_const).differentiable (by norm_num)
  have hb : Differentiable ℝ (fun y => fderiv ℝ g y Complex.I) :=
    (hgc.clm_apply contDiff_const).differentiable (by norm_num)
  have hdef : dWbar g = fun y => (1 / 2 : ℂ) *
      (fderiv ℝ g y 1 + Complex.I * fderiv ℝ g y Complex.I) := by
    funext y; unfold dWbar; ring
  have hd : ∀ u : ℂ, fderiv ℝ (dWbar g) z u =
      (1 / 2 : ℂ) * (fderiv ℝ (fun y => fderiv ℝ g y 1) z u + Complex.I *
        fderiv ℝ (fun y => fderiv ℝ g y Complex.I) z u) := by
    intro u
    rw [hdef]
    have h := (((ha z).hasFDerivAt.add ((hb z).hasFDerivAt.const_mul Complex.I)).const_mul
      (1 / 2 : ℂ))
    exact congrArg (fun L => L u) h.fderiv
  have hsym := (hg.contDiffAt (x := z)).isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]) 1 Complex.I
  have e1 : fderiv ℝ (fun y => fderiv ℝ g y 1) z Complex.I =
      fderiv ℝ (fderiv ℝ g) z Complex.I 1 := by
    have := fderiv_clm_apply (c := fderiv ℝ g) (u := fun _ : ℂ => (1 : ℂ))
      (hgc.differentiable (by norm_num) z) (differentiableAt_const 1)
    rw [this]; simp
  have e2 : fderiv ℝ (fun y => fderiv ℝ g y Complex.I) z 1 =
      fderiv ℝ (fderiv ℝ g) z 1 Complex.I := by
    have := fderiv_clm_apply (c := fderiv ℝ g) (u := fun _ : ℂ => Complex.I)
      (hgc.differentiable (by norm_num) z) (differentiableAt_const Complex.I)
    rw [this]; simp
  have hw : wirt 1 1 g = dW (dWbar g) := by simp [wirt]
  rw [hw]
  unfold dW
  rw [hd 1, hd Complex.I]
  unfold d2
  rw [e1, e2, ← hsym]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(1 / 4 : ℂ) * fderiv ℝ (fun y => fderiv ℝ g y Complex.I) z Complex.I) * hI


/-- `d2` of `y ↦ Φ (M y)` for a continuous linear `M`. -/
private lemma CF_d2_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : E → ℂ) (hΦ : ContDiff ℝ 2 Φ)
    (M : F →L[ℝ] E) (y u : F) : d2 (fun y => Φ (M y)) y u = d2 Φ (M y) (M u) := by
  simpa using CF_d2_affine Φ hΦ 0 M y u

/-! ### The one-entry substitution as an affine map -/

section Slice

variable {D N : ℕ}

/-- The substitution `w ↦ setEntry 0 i j w` is real-linear in `w`. -/
private def CF_setL (D N : ℕ) (i j : Idx D N) : ℂ →L[ℝ] (Idx D N → Idx D N → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => setEntry 0 i j w
      map_add' := fun a b => by
        funext k l
        simp only [setEntry, Pi.add_apply]
        split_ifs <;> simp [Complex.ofReal_add]
      map_smul' := fun c w => by
        funext k l
        simp only [setEntry, Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp [Complex.real_smul] }

private lemma CF_setL_apply (i j : Idx D N) (w : ℂ) : CF_setL D N i j w = setEntry 0 i j w := rfl

/-- `setEntry h i j w = setEntry h i j 0 + setEntry 0 i j w`. -/
private lemma CF_setEntry_split (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (w : ℂ) :
    setEntry h i j w = setEntry h i j 0 + setEntry 0 i j w := by
  funext k l
  simp only [setEntry, Pi.add_apply, Pi.zero_apply]
  split_ifs <;> simp

/-- A Hermitian array is unchanged by writing its own entry `(i, j)` back. -/
private lemma CF_setEntry_self (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) : setEntry h i j (h i j) = h := by
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

/-- Swapping the two indices conjugates the substituted value. -/
private lemma CF_setEntry_swap (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (w : ℂ) :
    setEntry h j i w = setEntry h i j (starRingEnd ℂ w) := by
  funext k l
  by_cases hd : i = j
  · subst hd
    simp [setEntry]
  · by_cases h1 : k = j ∧ l = i
    · simp [setEntry, hd, Ne.symm hd, h1]
    · by_cases h2 : k = i ∧ l = j
      · simp [setEntry, hd, Ne.symm hd, h2]
      · simp [setEntry, hd, Ne.symm hd, h1, h2]

/-- `setEntry` of a Hermitian array is Hermitian. -/
private lemma CF_setEntry_herm (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (w : ℂ) : (Matrix.of (setEntry h i j w)).IsHermitian := by
  have e : symArr (setEntry h i j w) = setEntry h i j w := by
    rw [symArr_setEntry, symArr_of_isHermitian h hh]
  rw [← e]
  exact symArr_isHermitian _

/-- For `Φ` of class `C¹`, `∂_{w̄}` of the slice `w ↦ Φ(setEntry h i j w)`. -/
private lemma CF_slice_wirt01 (Φ : (Idx D N → Idx D N → ℂ) → ℂ) (hΦ : ContDiff ℝ 1 Φ)
    (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (z : ℂ) :
    wirt 0 1 (fun w => Φ (setEntry h i j w)) z =
      (1 / 2 : ℂ) * (fderiv ℝ Φ (setEntry h i j z) (setEntry 0 i j 1) +
        Complex.I * fderiv ℝ Φ (setEntry h i j z) (setEntry 0 i j Complex.I)) := by
  have e : (fun w => Φ (setEntry h i j w)) =
      fun w => Φ (setEntry h i j 0 + CF_setL D N i j w) := by
    funext w; rw [CF_setL_apply, ← CF_setEntry_split]
  have hw : wirt 0 1 (fun w => Φ (setEntry h i j w)) =
      dWbar (fun w => Φ (setEntry h i j w)) := by simp [wirt]
  rw [hw, e]
  unfold dWbar
  rw [CF_fderiv_affine Φ hΦ _ _ z 1, CF_fderiv_affine Φ hΦ _ _ z Complex.I]
  simp only [CF_setL_apply]
  rw [← CF_setEntry_split]
  ring

/-- For `Φ` of class `C²`, `∂_w ∂_{w̄}` of the slice `w ↦ Φ(setEntry h i j w)`. -/
private lemma CF_slice_wirt11 (Φ : (Idx D N → Idx D N → ℂ) → ℂ) (hΦ : ContDiff ℝ 2 Φ)
    (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (z : ℂ) :
    wirt 1 1 (fun w => Φ (setEntry h i j w)) z =
      (1 / 4 : ℂ) * (d2 Φ (setEntry h i j z) (setEntry 0 i j 1) +
        d2 Φ (setEntry h i j z) (setEntry 0 i j Complex.I)) := by
  have e : (fun w => Φ (setEntry h i j w)) =
      fun w => Φ (setEntry h i j 0 + CF_setL D N i j w) := by
    funext w; rw [CF_setL_apply, ← CF_setEntry_split]
  have hg : ContDiff ℝ 2 (fun w => Φ (setEntry h i j 0 + CF_setL D N i j w)) :=
    hΦ.comp (contDiff_const.add (CF_setL D N i j).contDiff)
  rw [e, CF_wirt11 _ hg, CF_d2_affine Φ hΦ, CF_d2_affine Φ hΦ]
  simp only [CF_setL_apply]
  rw [← CF_setEntry_split]

/-- The slice of `g` at the swapped indices is the slice at `(i, j)` composed with conjugation;
the first Wirtinger derivatives are exchanged. -/
private lemma CF_dWbar_swap (Φ : (Idx D N → Idx D N → ℂ) → ℂ) (hΦ : ContDiff ℝ 1 Φ)
    (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (z : ℂ) :
    dW (fun w => Φ (setEntry h j i w)) (starRingEnd ℂ z) =
      dWbar (fun w => Φ (setEntry h i j w)) z := by
  have e : (fun w => Φ (setEntry h j i w)) =
      fun w => (fun w' => Φ (setEntry h i j w')) (Complex.conjCLE w) := by
    funext w; rw [CF_setEntry_swap]; rfl
  have hd : DifferentiableAt ℝ (fun w => Φ (setEntry h i j w)) z := by
    have : ContDiff ℝ 1 (fun w => Φ (setEntry h i j 0 + CF_setL D N i j w)) :=
      hΦ.comp (contDiff_const.add (CF_setL D N i j).contDiff)
    have e0 : (fun w => Φ (setEntry h i j w)) =
        fun w => Φ (setEntry h i j 0 + CF_setL D N i j w) := by
      funext w; rw [CF_setL_apply, ← CF_setEntry_split]
    rw [e0]
    exact this.differentiable (by norm_num) z
  rw [e]
  set g : ℂ → ℂ := fun w' => Φ (setEntry h i j w') with hg
  have hconj : ∀ u : ℂ, fderiv ℝ (fun w => g (Complex.conjCLE w)) (starRingEnd ℂ z) u =
      fderiv ℝ g z (starRingEnd ℂ u) := by
    intro u
    have hA : HasFDerivAt (fun w : ℂ => Complex.conjCLE w)
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ)) (starRingEnd ℂ z) := Complex.conjCLE.hasFDerivAt
    have hz : Complex.conjCLE (starRingEnd ℂ z) = z := by simp
    have hd' : DifferentiableAt ℝ g (Complex.conjCLE (starRingEnd ℂ z)) := by rw [hz]; exact hd
    have h1 : HasFDerivAt (fun w => g (Complex.conjCLE w))
        ((fderiv ℝ g (Complex.conjCLE (starRingEnd ℂ z))).comp
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)) (starRingEnd ℂ z) :=
      hd'.hasFDerivAt.comp (starRingEnd ℂ z) hA
    rw [h1.fderiv]
    simp only [ContinuousLinearMap.comp_apply, hz]
    rfl
  unfold dW dWbar
  rw [hconj, hconj]
  simp only [map_one, Complex.conj_I]
  have : fderiv ℝ g z (-Complex.I) = -fderiv ℝ g z Complex.I := map_neg _ _
  rw [this]
  ring

end Slice

/-! ### The drift entry by entry -/

section Drift

variable {D N : ℕ}

/-- The weight `1` on the diagonal and `1/2` off it of the Hermitian decomposition of an array. -/
private def CF_cc (i j : Idx D N) : ℝ := if i = j then 1 else 1 / 2

/-- A double sum with a single nonzero term. -/
private lemma CF_sum_pair (a b : Idx D N) (F : Idx D N → Idx D N → ℂ) :
    ∑ p, ∑ m, (if p = a ∧ m = b then F p m else 0) = F a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro m _ hm; simp [hm]
    · simp
  · intro p _ hp; simp [hp]
  · simp

/-- One term of the decomposition of a Hermitian array into one-entry substitutions. -/
private lemma CF_cc_entry (Y : Idx D N → Idx D N → ℂ) (hY : (Matrix.of Y).IsHermitian)
    (i j k l : Idx D N) :
    (CF_cc i j : ℂ) * setEntry 0 i j (Y i j) k l =
      (if i = k ∧ j = l then (1 / 2 : ℂ) * Y k l else 0) +
        (if i = l ∧ j = k then (1 / 2 : ℂ) * Y k l else 0) := by
  have h1 : ∀ a b, starRingEnd ℂ (Y b a) = Y a b := fun a b => by
    simpa [Complex.star_def] using hY.apply a b
  have h2 : ∀ a, (((Y a a).re : ℝ) : ℂ) = Y a a := fun a => Complex.conj_eq_iff_re.mp (h1 a a)
  unfold CF_cc setEntry
  by_cases hij : i = j
  · subst hij
    by_cases hk : k = i
    · subst hk
      by_cases hl : l = k
      · subst hl
        simp [h2]
        ring
      · have : ¬ (k = l) := fun h => hl h.symm
        simp [hl, this]
    · by_cases hl : l = i
      · subst hl
        simp [hk, Ne.symm hk]
      · simp [hk, hl, Ne.symm hk, Ne.symm hl]
  · by_cases hc1 : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := hc1
      simp [hij, Ne.symm hij]
    · by_cases hc2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := hc2
        simp [hij, Ne.symm hij, h1]
      · have n1 : ¬ (i = k ∧ j = l) := fun h => hc1 ⟨h.1.symm, h.2.symm⟩
        have n2 : ¬ (i = l ∧ j = k) := fun h => hc2 ⟨h.2.symm, h.1.symm⟩
        simp [hij, hc1, hc2, n1, n2]

/-- A Hermitian array is the sum of its one-entry substitutions, with the weights `CF_cc`. -/
private lemma CF_decomp (Y : Idx D N → Idx D N → ℂ) (hY : (Matrix.of Y).IsHermitian) :
    Y = ∑ i, ∑ j, CF_cc i j • setEntry 0 i j (Y i j) := by
  funext k l
  simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul]
  simp_rw [CF_cc_entry Y hY, Finset.sum_add_distrib]
  rw [CF_sum_pair k l (fun _ _ => (1 / 2 : ℂ) * Y k l),
    CF_sum_pair l k (fun _ _ => (1 / 2 : ℂ) * Y k l)]
  ring

/-- The derivative of `Φ` at a Hermitian array in the direction `setEntry 0 i j u`, in Wirtinger
form. -/
private lemma CF_fderiv_slice (Φ : (Idx D N → Idx D N → ℂ) → ℂ) (hΦ : ContDiff ℝ 1 Φ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (u : ℂ) :
    fderiv ℝ Φ h (setEntry 0 i j u) =
      u * dW (fun w => Φ (setEntry h i j w)) (h i j) +
        starRingEnd ℂ u * dWbar (fun w => Φ (setEntry h i j w)) (h i j) := by
  rw [← CF_fderiv_wirt]
  have e : (fun w => Φ (setEntry h i j w)) =
      fun w => Φ (setEntry h i j 0 + CF_setL D N i j w) := by
    funext w; rw [CF_setL_apply, ← CF_setEntry_split]
  rw [e, CF_fderiv_affine Φ hΦ]
  simp only [CF_setL_apply]
  rw [← CF_setEntry_split, CF_setEntry_self h hh]

/-- `G ∘ symArr` and `G` agree on the one-entry substitutions of a Hermitian array. -/
private lemma CF_symArr_setEntry_herm (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (w : ℂ) : symArr (setEntry h i j w) = setEntry h i j w := by
  rw [symArr_setEntry, symArr_of_isHermitian h hh]

end Drift

/-- The drift `Σ h_{xy} ∂_{xy}` entry by entry: for Hermitian `h`, `Y` and `G ∘ symArr` of class
`C¹`, `DG(h)·Y = Σ_{i,j} κ_{ij} Ȳ_{ij} ∂_{w̄} G(setEntry h i j w)|_{w = h_{ij}}` (display before
(4.9) [eq:prodnGt]). -/
theorem fderiv_symArr_entry (D N : ℕ) (G : (Idx D N → Idx D N → ℂ) → ℝ)
    (hG : ContDiff ℝ 1 (fun h => G (symArr h))) (h Y : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hY : (Matrix.of Y).IsHermitian) :
    ((fderiv ℝ (fun h => G (symArr h)) h Y : ℝ) : ℂ) =
      ∑ i, ∑ j, driftWt i j * starRingEnd ℂ (Y i j) *
        wirt 0 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j)  := by
  set Φc : (Idx D N → Idx D N → ℂ) → ℂ := fun h => ((G (symArr h) : ℝ) : ℂ) with hΦc
  have hΦ1 : ContDiff ℝ 1 Φc := Complex.ofRealCLM.contDiff.comp hG
  have hL : ((fderiv ℝ (fun h => G (symArr h)) h Y : ℝ) : ℂ) = fderiv ℝ Φc h Y := by
    have h1 : HasFDerivAt Φc (Complex.ofRealCLM.comp (fderiv ℝ (fun h => G (symArr h)) h)) h :=
      Complex.ofRealCLM.hasFDerivAt.comp h (hG.differentiable (by norm_num) h).hasFDerivAt
    rw [h1.fderiv]
    rfl
  have hg : ∀ i j : Idx D N,
      (fun w => (G (setEntry h i j w) : ℂ)) = fun w => Φc (setEntry h i j w) := by
    intro i j; funext w; simp only [hΦc, CF_symArr_setEntry_herm h hh]
  -- the Wirtinger derivatives of the slices
  set a : Idx D N → Idx D N → ℂ := fun i j => dW (fun w => Φc (setEntry h i j w)) (h i j) with ha
  set b : Idx D N → Idx D N → ℂ := fun i j => dWbar (fun w => Φc (setEntry h i j w)) (h i j) with hb
  have hw : ∀ i j : Idx D N, wirt 0 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) = b i j := by
    intro i j; rw [hg]; simp [wirt, hb]
  have hab : ∀ i j : Idx D N, a j i = b i j := by
    intro i j
    have hji : h j i = starRingEnd ℂ (h i j) := by
      have := hh.apply j i
      simpa [Complex.star_def] using this.symm
    simp only [ha, hb, hji]
    exact CF_dWbar_swap Φc hΦ1 h i j (h i j)
  have hY1 : ∀ i j : Idx D N, Y j i = starRingEnd ℂ (Y i j) := fun i j => by
    have := hY.apply j i
    simpa [Complex.star_def] using this.symm
  have hcc : ∀ i j : Idx D N, CF_cc j i = CF_cc i j := fun i j => by
    unfold CF_cc
    by_cases hij : i = j
    · subst hij; rfl
    · simp [hij, Ne.symm hij]
  have hdw : ∀ i j : Idx D N, driftWt i j = 2 * (CF_cc i j : ℂ) := fun i j => by
    unfold driftWt CF_cc
    by_cases hij : i = j <;> simp [hij]
  rw [hL]
  conv_lhs => rw [CF_decomp Y hY]
  simp only [map_sum, map_smul, Complex.real_smul]
  have hs : ∀ i j : Idx D N, fderiv ℝ Φc h (setEntry 0 i j (Y i j)) =
      Y i j * a i j + starRingEnd ℂ (Y i j) * b i j :=
    fun i j => CF_fderiv_slice Φc hΦ1 h hh i j (Y i j)
  simp_rw [hs, hw, mul_add, Finset.sum_add_distrib]
  have hswap : ∑ i, ∑ j, (CF_cc i j : ℂ) * (Y i j * a i j) =
      ∑ i, ∑ j, (CF_cc i j : ℂ) * (starRingEnd ℂ (Y i j) * b i j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hcc, hY1, hab]
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hdw]
  ring

/-! ### The Gaussian Laplacian entry by entry -/

section Gen

variable {D N : ℕ}

/-- The coordinate-to-entry factor `(DN)^{-1/2}` of `wig (DN)`. -/
private def CF_s (D N : ℕ) : ℝ := ((D * N : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

private lemma CF_s_sq (D N : ℕ) (h : D * N ≠ 0) : CF_s D N * CF_s D N = (((D * N : ℕ) : ℝ))⁻¹ := by
  unfold CF_s
  have hpos : (0 : ℝ) < ((D * N : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
  rw [← Real.rpow_add hpos, show (-(1 / 2 : ℝ) + -(1 / 2)) = -1 by norm_num, Real.rpow_neg_one]

/-- The array of the coordinate `bD 0 (e i)` is `(DN)^{-1/2} E_{ii}`. -/
private lemma CF_arr_bD (D N : ℕ) (i : Idx D N) :
    CF_arr D N (bD (0 : Fin 1) (finProdFinEquiv i)) = CF_s D N • setEntry 0 i i 1 := by
  funext p q
  have h1 : CF_arr D N (bD (0 : Fin 1) (finProdFinEquiv i)) p q =
      wig (D * N) ((bD (0 : Fin 1) (finProdFinEquiv i)) 0) (finProdFinEquiv p)
        (finProdFinEquiv q) := rfl
  rw [h1]
  simp only [bD, Pi.single_eq_same, wig]
  simp only [Pi.smul_apply, setEntry, CF_s, Complex.real_smul, ite_true]
  congr 1
  by_cases hpq : p = q
  · subst hpq
    simp [Pi.single_apply]
    split_ifs <;> simp
  · have hne : finProdFinEquiv p ≠ finProdFinEquiv q := fun h => hpq (finProdFinEquiv.injective h)
    by_cases hp : p = i
    · subst hp
      simp [hne, Ne.symm hpq]
    · simp [hne, hp]

/-- The array of an off-diagonal coordinate vector `u e_{ij}` is `(DN)^{-1/2} (u E_{ij} + ū E_{ji})`
for `e i < e j`, and `0` otherwise. -/
private lemma CF_arr_off (D N : ℕ) (i j : Idx D N) (u : ℂ) :
    CF_arr D N (Pi.single (0 : Fin 1) ((0 : Fin (D * N) → ℝ),
        Pi.single (finProdFinEquiv i) (Pi.single (finProdFinEquiv j) u))) =
      if finProdFinEquiv i < finProdFinEquiv j then CF_s D N • setEntry 0 i j u else 0 := by
  funext p q
  have h1 : CF_arr D N (Pi.single (0 : Fin 1) ((0 : Fin (D * N) → ℝ),
        Pi.single (finProdFinEquiv i) (Pi.single (finProdFinEquiv j) u))) p q =
      wig (D * N) ((Pi.single (0 : Fin 1) ((0 : Fin (D * N) → ℝ),
        Pi.single (finProdFinEquiv i) (Pi.single (finProdFinEquiv j) u)) :
          Fin 1 → Coords (D * N)) 0)
        (finProdFinEquiv p) (finProdFinEquiv q) := rfl
  rw [h1]
  simp only [Pi.single_eq_same, wig]
  have hinj : ∀ x y : Idx D N, finProdFinEquiv x = finProdFinEquiv y ↔ x = y :=
    fun x y => finProdFinEquiv.apply_eq_iff_eq
  by_cases hlt : finProdFinEquiv i < finProdFinEquiv j
  · have hij : i ≠ j := fun h => by subst h; exact lt_irrefl _ hlt
    have hji : ¬ finProdFinEquiv j < finProdFinEquiv i := lt_asymm hlt
    simp only [hlt, ite_true, Pi.smul_apply, CF_s, Complex.real_smul]
    congr 1
    simp only [setEntry, hij, ite_false, Pi.single_apply, Pi.zero_apply, Equiv.apply_eq_iff_eq]
    split_ifs <;> simp_all
    exfalso
    omega
  · simp only [hlt, ite_false, Pi.zero_apply, mul_eq_zero, Pi.single_apply]
    right
    split_ifs <;> simp_all [Pi.single_apply]
    all_goals (intro hq; subst hq; first
      | (exfalso; omega)
      | (exfalso; apply ‹¬ _ = _›; apply finProdFinEquiv.injective
         apply le_antisymm <;> assumption))


/-- The array of `bRe 0 (e i) (e j)`. -/
private lemma CF_arr_bRe (D N : ℕ) (i j : Idx D N) :
    CF_arr D N (bRe (0 : Fin 1) (finProdFinEquiv i) (finProdFinEquiv j)) =
      if finProdFinEquiv i < finProdFinEquiv j then CF_s D N • setEntry 0 i j 1 else 0 :=
  CF_arr_off D N i j 1

/-- The array of `bIm 0 (e i) (e j)`. -/
private lemma CF_arr_bIm (D N : ℕ) (i j : Idx D N) :
    CF_arr D N (bIm (0 : Fin 1) (finProdFinEquiv i) (finProdFinEquiv j)) =
      if finProdFinEquiv i < finProdFinEquiv j then CF_s D N • setEntry 0 i j Complex.I else 0 :=
  CF_arr_off D N i j Complex.I

/-- The weights `genWt` and the sum over the pairs `e i < e j` for a symmetric `Q`. -/
private lemma CF_gen_sum (Q : Idx D N → Idx D N → ℂ) (hQ : ∀ i j, Q j i = Q i j) :
    ∑ i, ∑ j, genWt i j * ((1 / 4 : ℂ) * Q i j) =
      (∑ i, Q i i) +
        (1 / 2 : ℂ) * (∑ i, ∑ j, (if finProdFinEquiv i < finProdFinEquiv j then Q i j else 0)) := by
  have e1 : ∀ i j : Idx D N, genWt i j * ((1 / 4 : ℂ) * Q i j) =
      (if i = j then Q i j else 0) + (1 / 4 : ℂ) *
        ((if finProdFinEquiv i < finProdFinEquiv j then Q i j else 0) +
          (if finProdFinEquiv j < finProdFinEquiv i then Q i j else 0)) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [genWt]
    · have hne : finProdFinEquiv i ≠ finProdFinEquiv j := fun h => hij (finProdFinEquiv.injective h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp [genWt, hij, hlt, not_lt.mpr hlt.le]
      · simp [genWt, hij, hgt, not_lt.mpr hgt.le]
  have e2 : ∑ i, ∑ j, (if finProdFinEquiv j < finProdFinEquiv i then Q i j else 0) =
      ∑ i, ∑ j, (if finProdFinEquiv i < finProdFinEquiv j then Q i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hQ]
  have e3 : ∑ i, ∑ j, (if i = j then Q i j else 0) = ∑ i, Q i i := by simp
  simp_rw [e1]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e3, e2]
  ring


end Gen

/-- The Gaussian Laplacian of one block of size `DN` read on the array: for `G` with
`G ∘ symArr` of class `C²`, `gLap (G ∘ W) = (DN)⁻¹ Σ_{i,j} κ'_{ij} ∂_w ∂_{w̄} G(setEntry W i j w)`,
the term `(2DN)⁻¹ Σ ∂_{xy} ∂_{yx}` of the display before (4.9) [eq:prodnGt] (up to `½`). -/
theorem gLap_gueIdx (D N : ℕ) (G : (Idx D N → Idx D N → ℂ) → ℝ)
    (hG : ContDiff ℝ 2 (fun h => G (symArr h))) (x : Fin 1 → Coords (D * N)) :
    gLap (fun y => (G (Matrix.of.symm (gueIdx D N (y 0))) : ℂ)) x =
      (((D * N : ℕ) : ℂ))⁻¹ * ∑ i, ∑ j, genWt i j *
        wirt 1 1 (fun w => (G (setEntry (Matrix.of.symm (gueIdx D N (x 0))) i j w) : ℂ))
          (Matrix.of.symm (gueIdx D N (x 0)) i j)  := by
  set Φc : (Idx D N → Idx D N → ℂ) → ℂ := fun h => ((G (symArr h) : ℝ) : ℂ) with hΦc
  have hΦ2 : ContDiff ℝ 2 Φc := Complex.ofRealCLM.contDiff.comp hG
  set h : Idx D N → Idx D N → ℂ := CF_arr D N x with hh_def
  have hhh : Matrix.of.symm (gueIdx D N (x 0)) = h := rfl
  have hh : (Matrix.of h).IsHermitian := CF_arr_herm D N x
  have hF : (fun y : Fin 1 → Coords (D * N) => (G (Matrix.of.symm (gueIdx D N (y 0))) : ℂ)) =
      fun y => Φc (CF_arr D N y) := by
    funext y
    simp only [hΦc]
    rw [CF_symArr_arr]
    rfl
  have hd2 : ∀ v, d2 (fun y : Fin 1 → Coords (D * N) =>
      (G (Matrix.of.symm (gueIdx D N (y 0))) : ℂ)) x v = d2 Φc h (CF_arr D N v) := by
    intro v
    rw [hF]
    exact CF_d2_comp Φc hΦ2 (CF_arr D N) x v
  set Q : Idx D N → Idx D N → ℂ := fun i j =>
    d2 Φc h (setEntry 0 i j 1) + d2 Φc h (setEntry 0 i j Complex.I) with hQ
  have hw : ∀ i j : Idx D N, wirt 1 1 (fun w => (G (setEntry h i j w) : ℂ)) (h i j) =
      (1 / 4 : ℂ) * Q i j := by
    intro i j
    have hg : (fun w => (G (setEntry h i j w) : ℂ)) = fun w => Φc (setEntry h i j w) := by
      funext w; simp only [hΦc, CF_symArr_setEntry_herm h hh]
    rw [hg, CF_slice_wirt11 Φc hΦ2, CF_setEntry_self h hh]
  have hQsym : ∀ i j : Idx D N, Q j i = Q i j := by
    intro i j
    have e1 : setEntry (0 : Idx D N → Idx D N → ℂ) j i 1 = setEntry 0 i j 1 := by
      rw [CF_setEntry_swap]; simp
    have e2 : setEntry (0 : Idx D N → Idx D N → ℂ) j i Complex.I =
        (-1 : ℝ) • setEntry 0 i j Complex.I := by
      rw [CF_setEntry_swap, Complex.conj_I, ← CF_setL_apply, ← CF_setL_apply,
        show (-Complex.I) = ((-1 : ℝ) • Complex.I) by simp, map_smul]
    simp only [hQ]
    rw [e1, e2, CF_d2_smul Φc hΦ2]
    simp
  have hQdiag : ∀ i : Idx D N, d2 Φc h (setEntry 0 i i 1) = Q i i := by
    intro i
    have : setEntry (0 : Idx D N → Idx D N → ℂ) i i Complex.I = 0 := by
      funext k l; simp [setEntry]
    simp only [hQ, this, CF_d2_zero, add_zero]
  unfold gLap
  simp only [Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
  simp only [hd2]
  have hbD : ∀ i : Idx D N, d2 Φc h (CF_arr D N (bD (0 : Fin 1) (finProdFinEquiv i))) =
      ((CF_s D N * CF_s D N : ℝ) : ℂ) * Q i i := by
    intro i
    rw [CF_arr_bD, CF_d2_smul Φc hΦ2, hQdiag]
  have hbR : ∀ i j : Idx D N,
      d2 Φc h (CF_arr D N (bRe (0 : Fin 1) (finProdFinEquiv i) (finProdFinEquiv j))) +
        d2 Φc h (CF_arr D N (bIm (0 : Fin 1) (finProdFinEquiv i) (finProdFinEquiv j))) =
      ((CF_s D N * CF_s D N : ℝ) : ℂ) *
        (if finProdFinEquiv i < finProdFinEquiv j then Q i j else 0) := by
    intro i j
    rw [CF_arr_bRe, CF_arr_bIm]
    by_cases hlt : finProdFinEquiv i < finProdFinEquiv j
    · simp only [hlt, ite_true, CF_d2_smul Φc hΦ2, hQ]
      ring
    · simp [hlt, CF_d2_zero]
  have s1 : ∑ k : Fin (D * N), d2 Φc h (CF_arr D N (bD (0 : Fin 1) k)) =
      ∑ i : Idx D N, d2 Φc h (CF_arr D N (bD (0 : Fin 1) (finProdFinEquiv i))) :=
    (Equiv.sum_comp finProdFinEquiv (fun k => d2 Φc h (CF_arr D N (bD (0 : Fin 1) k)))).symm
  have s2 : ∑ k : Fin (D * N), ∑ l : Fin (D * N),
      (d2 Φc h (CF_arr D N (bRe (0 : Fin 1) k l)) + d2 Φc h (CF_arr D N (bIm (0 : Fin 1) k l))) =
      ∑ i : Idx D N, ∑ j : Idx D N,
      (d2 Φc h (CF_arr D N (bRe (0 : Fin 1) (finProdFinEquiv i) (finProdFinEquiv j))) +
        d2 Φc h (CF_arr D N (bIm (0 : Fin 1) (finProdFinEquiv i) (finProdFinEquiv j)))) :=
    (Equiv.sum_comp finProdFinEquiv (fun k => ∑ l : Fin (D * N),
      (d2 Φc h (CF_arr D N (bRe (0 : Fin 1) k l)) +
        d2 Φc h (CF_arr D N (bIm (0 : Fin 1) k l))))).symm.trans
      (Finset.sum_congr rfl fun i _ => (Equiv.sum_comp finProdFinEquiv (fun l =>
        (d2 Φc h (CF_arr D N (bRe (0 : Fin 1) (finProdFinEquiv i) l)) +
          d2 Φc h (CF_arr D N (bIm (0 : Fin 1) (finProdFinEquiv i) l))))).symm)
  rw [s1, s2]
  simp_rw [hbD, hbR]
  simp only [hhh, hw]
  rw [CF_gen_sum Q hQsym]
  by_cases hDN : D * N = 0
  · have hE : IsEmpty (Idx D N) := by
      rw [← Fintype.card_eq_zero_iff]; simp [hDN]
    simp [Finset.univ_eq_empty]
  · rw [CF_s_sq D N hDN]
    push_cast
    simp_rw [← Finset.mul_sum]
    ring

/-! ### Entrywise bounds on the resolvent and the first two derivatives of `A` -/

section Bounds

/-- `Im G` has the entries `(G_{ab} - conj G_{ba}) / (2i)`. -/
private lemma CF_imRes_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (z : ℂ)
    (a b : ι) :
    imRes X z a b = (2 * Complex.I)⁻¹ * (res X z a b - starRingEnd ℂ (res X z b a)) := by
  simp [imRes, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply]

/-- The entries of `G` and `Im G` are at most `η⁻¹` for Hermitian `X` and `Im z = η > 0`. -/
private lemma CF_entries_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (η : ℝ) (hη : 0 < η) (hz : z.im = η) (a b : ι) :
    ‖res X z a b‖ ≤ η⁻¹ ∧ ‖imRes X z a b‖ ≤ η⁻¹ := by
  have hz0 : 0 < z.im := by rw [hz]; exact hη
  have hG : ∀ a b, ‖res X z a b‖ ≤ η⁻¹ := fun a b =>
    (norm_apply_le_opNorm _ a b).trans (by have := opNorm_res_le X hX z hz0; rwa [hz] at this)
  refine ⟨hG a b, ?_⟩
  rw [CF_imRes_apply, norm_mul, norm_inv, norm_mul, Complex.norm_I]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have h3 := norm_sub_le (res X z a b) (starRingEnd ℂ (res X z b a))
  rw [Complex.norm_conj] at h3
  have h4 := hG a b
  have h5 := hG b a
  have h6 : (0 : ℝ) ≤ η⁻¹ := inv_nonneg.mpr hη.le
  calc ((2 : ℝ) * 1)⁻¹ * ‖res X z a b - starRingEnd ℂ (res X z b a)‖
      ≤ ((2 : ℝ) * 1)⁻¹ * (η⁻¹ + η⁻¹) := by
        refine mul_le_mul_of_nonneg_left (h3.trans (by linarith)) (by positivity)
    _ = η⁻¹ := by ring

/-- The sum of the absolute values of the entries of an array. -/
private def CF_S {D N : ℕ} (V : Idx D N → Idx D N → ℂ) : ℝ := ∑ a, ∑ b, ‖V a b‖

private lemma CF_S_nonneg {D N : ℕ} (V : Idx D N → Idx D N → ℂ) : 0 ≤ CF_S V :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- `|tr(M V)| ≤ μ Σ |V_{ab}|` when all entries of `M` are at most `μ`. -/
private lemma CF_trace_le {D N : ℕ} (M : Matrix (Idx D N) (Idx D N) ℂ)
    (V : Idx D N → Idx D N → ℂ) (μ : ℝ) (hμ : ∀ a b, ‖M a b‖ ≤ μ) :
    ‖(M * Matrix.of V).trace‖ ≤ μ * CF_S V := by
  have h1 : (M * Matrix.of V).trace = ∑ a, ∑ b, M a b * V b a := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [h1]
  calc ‖∑ a, ∑ b, M a b * V b a‖ ≤ ∑ a, ‖∑ b, M a b * V b a‖ := norm_sum_le _ _
    _ ≤ ∑ a, ∑ b, ‖M a b * V b a‖ := Finset.sum_le_sum fun a _ => norm_sum_le _ _
    _ ≤ ∑ a, ∑ b, μ * ‖V b a‖ := Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hμ a b) (norm_nonneg _)
    _ = μ * CF_S V := by
        simp only [CF_S, ← Finset.mul_sum]
        rw [Finset.sum_comm]

/-- The matrix `Δ = Im G(E₂ + iη) - Im G(E₁ + iη)` of (4.10) [partial_xy_F_A_t] at the array `h`. -/
private def CF_Delta (D N : ℕ) (Ac : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ)
    (h : Idx D N → Idx D N → ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  imRes (Matrix.of h + lam D N Ac) ((E₂ : ℂ) + (η : ℂ) * Complex.I) -
    imRes (Matrix.of h + lam D N Ac) ((E₁ : ℂ) + (η : ℂ) * Complex.I)

private lemma CF_Delta_entry_le (D N : ℕ) (Ac : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ)
    (hη : 0 < η) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (a b : Idx D N) : ‖CF_Delta D N Ac η E₁ E₂ h a b‖ ≤ 2 * η⁻¹ := by
  have hX : (Matrix.of h + lam D N Ac).IsHermitian := hh.add (lam_isHermitian D N Ac)
  have h1 := (CF_entries_le _ hX ((E₂ : ℂ) + (η : ℂ) * Complex.I) η hη (by simp) a b).2
  have h2 := (CF_entries_le _ hX ((E₁ : ℂ) + (η : ℂ) * Complex.I) η hη (by simp) a b).2
  unfold CF_Delta
  rw [Matrix.sub_apply]
  calc ‖_ - _‖ ≤ _ + _ := norm_sub_le _ _
    _ ≤ η⁻¹ + η⁻¹ := add_le_add h1 h2
    _ = 2 * η⁻¹ := by ring

/-- The resolvent identity in the matrix: `G' - G = -G'(X' - X)G`, entrywise bound. -/
private lemma CF_res_perturb {ι : Type*} [Fintype ι] [DecidableEq ι] (X X' : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hX' : X'.IsHermitian) (z : ℂ) (η : ℝ) (hη : 0 < η) (hz : z.im = η)
    (a b : ι) :
    ‖(res X' z - res X z) a b‖ ≤ η⁻¹ * η⁻¹ * ∑ c, ∑ d, ‖(X' - X) c d‖ := by
  have hz0 : 0 < z.im := by rw [hz]; exact hη
  obtain ⟨hX1, hX2⟩ := res_mul_sub X hX z hz0
  obtain ⟨hX1', hX2'⟩ := res_mul_sub X' hX' z hz0
  have e : res X' z - res X z = -(res X' z * (X' - X) * res X z) := by
    have : (X' - X) = (X' - z • (1 : Matrix ι ι ℂ)) - (X - z • (1 : Matrix ι ι ℂ)) := by abel
    have e1 : res X' z * (X' - z • (1 : Matrix ι ι ℂ)) * res X z = res X z := by
      rw [hX2', one_mul]
    have e2 : res X' z * (X - z • (1 : Matrix ι ι ℂ)) * res X z = res X' z := by
      rw [mul_assoc, hX1, mul_one]
    rw [this, mul_sub, sub_mul, e1, e2]
    abel
  rw [e, Matrix.neg_apply, norm_neg, Matrix.mul_apply]
  have hb : ∀ c d : ι, ‖res X' z a c‖ * ‖res X z d b‖ ≤ η⁻¹ * η⁻¹ := fun c d =>
    mul_le_mul (CF_entries_le X' hX' z η hη hz a c).1 (CF_entries_le X hX z η hη hz d b).1
      (norm_nonneg _) (inv_nonneg.mpr hη.le)
  calc ‖∑ d, (res X' z * (X' - X)) a d * res X z d b‖
      ≤ ∑ d, ‖(res X' z * (X' - X)) a d * res X z d b‖ := norm_sum_le _ _
    _ ≤ ∑ d, ∑ c, η⁻¹ * η⁻¹ * ‖(X' - X) c d‖ := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [norm_mul, Matrix.mul_apply]
        calc ‖∑ c, res X' z a c * (X' - X) c d‖ * ‖res X z d b‖
            ≤ (∑ c, ‖res X' z a c‖ * ‖(X' - X) c d‖) * ‖res X z d b‖ := by
              refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans ?_) (norm_nonneg _)
              exact Finset.sum_le_sum fun c _ => (norm_mul _ _).le
          _ = ∑ c, ‖res X' z a c‖ * ‖res X z d b‖ * ‖(X' - X) c d‖ := by
              rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun c _ => by ring
          _ ≤ ∑ c, η⁻¹ * η⁻¹ * ‖(X' - X) c d‖ :=
              Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (hb c d) (norm_nonneg _)
    _ = η⁻¹ * η⁻¹ * ∑ c, ∑ d, ‖(X' - X) c d‖ := by
        rw [Finset.mul_sum, Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]

/-- The same bound for `Im G`. -/
private lemma CF_imRes_perturb {ι : Type*} [Fintype ι] [DecidableEq ι] (X X' : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hX' : X'.IsHermitian) (z : ℂ) (η : ℝ) (hη : 0 < η) (hz : z.im = η)
    (a b : ι) :
    ‖(imRes X' z - imRes X z) a b‖ ≤ η⁻¹ * η⁻¹ * ∑ c, ∑ d, ‖(X' - X) c d‖ := by
  have h1 := CF_res_perturb X X' hX hX' z η hη hz a b
  have h2 := CF_res_perturb X X' hX hX' z η hη hz b a
  have e : (imRes X' z - imRes X z) a b =
      (2 * Complex.I)⁻¹ *
        ((res X' z - res X z) a b - starRingEnd ℂ ((res X' z - res X z) b a)) := by
    rw [Matrix.sub_apply, CF_imRes_apply, CF_imRes_apply, Matrix.sub_apply, Matrix.sub_apply,
      map_sub]
    ring
  rw [e, norm_mul, norm_inv, norm_mul, Complex.norm_I, show ‖(2 : ℂ)‖ = 2 by simp]
  have h3 := norm_sub_le ((res X' z - res X z) a b) (starRingEnd ℂ ((res X' z - res X z) b a))
  rw [Complex.norm_conj] at h3
  have h0 : 0 ≤ η⁻¹ * η⁻¹ * ∑ c, ∑ d, ‖(X' - X) c d‖ :=
    (norm_nonneg _).trans h1
  calc ((2 : ℝ) * 1)⁻¹ * ‖(res X' z - res X z) a b - starRingEnd ℂ ((res X' z - res X z) b a)‖
      ≤ ((2 : ℝ) * 1)⁻¹ * (2 * (η⁻¹ * η⁻¹ * ∑ c, ∑ d, ‖(X' - X) c d‖)) :=
        mul_le_mul_of_nonneg_left (h3.trans (by linarith)) (by positivity)
    _ = _ := by ring

end Bounds

/-! ### The first and second derivatives of one edge count along the coordinates -/

section Count

/-- `Matrix.of (h + s • V) = Matrix.of h + s • Matrix.of V` for real `s`. -/
private lemma CF_of_line {D N : ℕ} (h V : Idx D N → Idx D N → ℂ) (s : ℝ) :
    Matrix.of (h + s • V) = Matrix.of h + (s : ℂ) • Matrix.of V := by
  ext a b
  simp [Complex.real_smul]

/-- `h + s V` is Hermitian for Hermitian `h`, `V` and real `s`. -/
private lemma CF_line_herm {D N : ℕ} (h V : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (hV : (Matrix.of V).IsHermitian) (s : ℝ) :
    (Matrix.of (h + s • V)).IsHermitian := by
  rw [CF_of_line]
  exact hh.add (hV.smul (Complex.conj_ofReal s))

variable (D N : ℕ) (Ac : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ)

/-- The edge count `A` of (4.7) [2comVVt] as a function of the coordinates of one block of size
`DN`. -/
private def CF_A (v : Fin 1 → Coords (D * N)) : ℝ :=
  edgeCount D N Ac η E₁ E₂ (CF_arr D N v)

private lemma CF_A_contDiff (hη : 0 < η) : ContDiff ℝ ∞ (CF_A D N Ac η E₁ E₂) := by
  have : CF_A D N Ac η E₁ E₂ =
      fun v => edgeCount D N Ac η E₁ E₂ (symArr (CF_arr D N v)) := by
    funext v; simp only [CF_A, CF_symArr_arr]
  rw [this]
  exact (edgeCount_contDiff D N Ac η E₁ E₂ hη).comp (CF_arr D N).contDiff

/-- The derivative of `A` along `u` at `v`: `-tr(Δ(h) V)` for the arrays `h`, `V` of `v`, `u`
(4.10) [partial_xy_F_A_t]. -/
private lemma CF_fderiv_A (hη : 0 < η) (v u : Fin 1 → Coords (D * N)) :
    fderiv ℝ (CF_A D N Ac η E₁ E₂) v u =
      -(CF_Delta D N Ac η E₁ E₂ (CF_arr D N v) * Matrix.of (CF_arr D N u)).trace.re := by
  have hA := CF_A_contDiff D N Ac η E₁ E₂ hη
  have hline : HasDerivAt (fun s : ℝ => v + s • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add v
  have h1 : HasDerivAt (fun s : ℝ => CF_A D N Ac η E₁ E₂ (v + s • u))
      (fderiv ℝ (CF_A D N Ac η E₁ E₂) v u) 0 := by
    have : HasFDerivAt (CF_A D N Ac η E₁ E₂) (fderiv ℝ (CF_A D N Ac η E₁ E₂) v)
        (v + (0 : ℝ) • u) := by
      simpa using (hA.differentiable (by simp) v).hasFDerivAt
    exact this.comp_hasDerivAt (0 : ℝ) hline
  have h2 := edgeCount_hasDerivAt D N Ac η E₁ E₂ hη (CF_arr D N v) (CF_arr D N u)
    (CF_arr_herm D N v) (CF_arr_herm D N u)
  have e : (fun s : ℝ => CF_A D N Ac η E₁ E₂ (v + s • u)) =
      fun s : ℝ => edgeCount D N Ac η E₁ E₂ (CF_arr D N v + s • CF_arr D N u) := by
    funext s; simp [CF_A, map_add, map_smul]
  rw [e] at h1
  exact h1.unique h2

/-- `|DA(v)·u| ≤ (2/η) Σ |V_{ab}|`, `V` the array of `u`. -/
private lemma CF_fderiv_A_le (hη : 0 < η) (v u : Fin 1 → Coords (D * N)) :
    ‖fderiv ℝ (CF_A D N Ac η E₁ E₂) v u‖ ≤ 2 * η⁻¹ * CF_S (CF_arr D N u) := by
  rw [CF_fderiv_A D N Ac η E₁ E₂ hη, Real.norm_eq_abs, abs_neg]
  refine (Complex.abs_re_le_norm _).trans (CF_trace_le _ _ _ fun a b => ?_)
  exact CF_Delta_entry_le D N Ac η E₁ E₂ hη _ (CF_arr_herm D N v) a b

/-- The second derivative of `A`: `|D²A(v)[u₀, u₁]| ≤ 2 η⁻² (Σ|V₀|)(Σ|V₁|)`. -/
private lemma CF_fderiv2_A_le (hη : 0 < η) (v u₀ u₁ : Fin 1 → Coords (D * N)) :
    ‖fderiv ℝ (fderiv ℝ (CF_A D N Ac η E₁ E₂)) v u₀ u₁‖ ≤
      2 * η⁻¹ * η⁻¹ * CF_S (CF_arr D N u₀) * CF_S (CF_arr D N u₁) := by
  have hA := CF_A_contDiff D N Ac η E₁ E₂ hη
  set A := CF_A D N Ac η E₁ E₂ with hAdef
  have hA2 : ContDiff ℝ 2 A := hA.of_le (by simp)
  have hA1 : ContDiff ℝ 1 (fderiv ℝ A) := hA2.fderiv_right (by norm_num)
  have hc : HasFDerivAt (fderiv ℝ A) (fderiv ℝ (fderiv ℝ A) v) v :=
    (hA1.differentiable (by norm_num) v).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => v + s • u₀) u₀ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u₀).const_add v
  have hc1 : HasFDerivAt (fun y => fderiv ℝ A y u₁) ((fderiv ℝ (fderiv ℝ A) v).flip u₁) v := by
    have := hc.clm_apply (hasFDerivAt_const u₁ v)
    simpa using this
  have hc2 : HasFDerivAt (fun y => fderiv ℝ A y u₁) ((fderiv ℝ (fderiv ℝ A) v).flip u₁)
      (v + (0 : ℝ) • u₀) := by simpa using hc1
  have h4 : HasDerivAt (fun s : ℝ => fderiv ℝ A (v + s • u₀) u₁)
      (fderiv ℝ (fderiv ℝ A) v u₀ u₁) 0 := by
    have h4' := hc2.comp_hasDerivAt (0 : ℝ) hline
    exact h4'
  refine h4.le_of_lip' (by positivity [CF_S_nonneg (CF_arr D N u₀), CF_S_nonneg (CF_arr D N u₁)])
    (Filter.Eventually.of_forall fun s => ?_)
  -- the Lipschitz estimate
  set h := CF_arr D N v with hh
  set V₀ := CF_arr D N u₀ with hV₀
  set V₁ := CF_arr D N u₁ with hV₁
  have hs : ∀ s : ℝ, fderiv ℝ A (v + s • u₀) u₁ =
      -(CF_Delta D N Ac η E₁ E₂ (h + s • V₀) * Matrix.of V₁).trace.re := by
    intro s
    rw [hAdef, CF_fderiv_A D N Ac η E₁ E₂ hη]
    simp [hh, hV₀, hV₁, map_add, map_smul]
  simp only [hs, zero_smul, add_zero, Real.norm_eq_abs, sub_zero]
  have hX0 : (Matrix.of h + lam D N Ac).IsHermitian :=
    (CF_arr_herm D N v).add (lam_isHermitian D N Ac)
  have hHs : (Matrix.of (h + s • V₀) + lam D N Ac).IsHermitian :=
    (CF_line_herm h V₀ (CF_arr_herm D N v) (CF_arr_herm D N u₀) s).add (lam_isHermitian D N Ac)
  have hdiff : (Matrix.of (h + s • V₀) + lam D N Ac) - (Matrix.of h + lam D N Ac) =
      (s : ℂ) • Matrix.of V₀ := by
    ext a b; simp [Complex.real_smul]
  have hSd : ∑ c, ∑ d, ‖((Matrix.of (h + s • V₀) + lam D N Ac) - (Matrix.of h + lam D N Ac)) c d‖ =
      |s| * CF_S V₀ := by
    rw [hdiff]
    simp only [CF_S, Matrix.smul_apply, smul_eq_mul, norm_mul, ← Finset.mul_sum]
    simp [Complex.norm_real]
  have hent : ∀ a b : Idx D N, ‖(CF_Delta D N Ac η E₁ E₂ (h + s • V₀) -
      CF_Delta D N Ac η E₁ E₂ h) a b‖ ≤ 2 * (η⁻¹ * η⁻¹ * (|s| * CF_S V₀)) := by
    intro a b
    have him : ∀ e : ℝ, ‖(imRes (Matrix.of (h + s • V₀) + lam D N Ac)
        ((e : ℂ) + (η : ℂ) * Complex.I) - imRes (Matrix.of h + lam D N Ac)
        ((e : ℂ) + (η : ℂ) * Complex.I)) a b‖ ≤ η⁻¹ * η⁻¹ * (|s| * CF_S V₀) := by
      intro e
      have hz : (((e : ℂ) + (η : ℂ) * Complex.I)).im = η := by simp
      have hp := CF_imRes_perturb (Matrix.of h + lam D N Ac)
        (Matrix.of (h + s • V₀) + lam D N Ac) hX0 hHs _ η hη hz a b
      rwa [hSd] at hp
    have e2 := him E₂
    have e1 := him E₁
    have : (CF_Delta D N Ac η E₁ E₂ (h + s • V₀) - CF_Delta D N Ac η E₁ E₂ h) a b =
        (imRes (Matrix.of (h + s • V₀) + lam D N Ac) ((E₂ : ℂ) + (η : ℂ) * Complex.I) -
          imRes (Matrix.of h + lam D N Ac) ((E₂ : ℂ) + (η : ℂ) * Complex.I)) a b -
        (imRes (Matrix.of (h + s • V₀) + lam D N Ac) ((E₁ : ℂ) + (η : ℂ) * Complex.I) -
          imRes (Matrix.of h + lam D N Ac) ((E₁ : ℂ) + (η : ℂ) * Complex.I)) a b := by
      simp only [CF_Delta, Matrix.sub_apply]
      ring
    rw [this]
    calc ‖_ - _‖ ≤ _ + _ := norm_sub_le _ _
      _ ≤ _ := add_le_add e2 e1
      _ = _ := by ring
  have htr := CF_trace_le (CF_Delta D N Ac η E₁ E₂ (h + s • V₀) - CF_Delta D N Ac η E₁ E₂ h) V₁ _
    hent
  have hsub : -(CF_Delta D N Ac η E₁ E₂ (h + s • V₀) * Matrix.of V₁).trace.re -
      -(CF_Delta D N Ac η E₁ E₂ h * Matrix.of V₁).trace.re =
      -((CF_Delta D N Ac η E₁ E₂ (h + s • V₀) - CF_Delta D N Ac η E₁ E₂ h) *
        Matrix.of V₁).trace.re := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]; ring
  have h0 : fderiv ℝ A v u₁ = -(CF_Delta D N Ac η E₁ E₂ h * Matrix.of V₁).trace.re := by
    rw [hAdef, CF_fderiv_A D N Ac η E₁ E₂ hη]
  rw [h0, hsub, abs_neg]
  refine (Complex.abs_re_le_norm _).trans (htr.trans ?_)
  have : |s| = ‖s‖ := (Real.norm_eq_abs s).symm
  rw [mul_comm] at htr ⊢
  nlinarith [CF_S_nonneg V₀, CF_S_nonneg V₁, abs_nonneg s]

end Count

/-! ### The function `F(A)` on the coordinates and its derivative bounds -/

section Func

variable (D N : ℕ) (Ac : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) {n : ℕ} (F : (Fin n → ℝ) → ℝ)
  (E₁ E₂ : Fin n → ℝ)

/-- The vector `(A_k)_k` of edge counts of (4.7) [2comVVt] on the coordinates of one block. -/
private def CF_Avec (v : Fin 1 → Coords (D * N)) : Fin n → ℝ :=
  fun k => CF_A D N Ac η (E₁ k) (E₂ k) v

/-- `F(A)` on the coordinates of one block. -/
private def CF_Fc (v : Fin 1 → Coords (D * N)) : ℂ :=
  ((F (CF_Avec D N Ac η E₁ E₂ v) : ℝ) : ℂ)

private lemma CF_Fc_eq (v : Fin 1 → Coords (D * N)) :
    CF_Fc D N Ac η F E₁ E₂ v = ((edgeFn D N Ac η F E₁ E₂ (CF_arr D N v) : ℝ) : ℂ) := rfl

private lemma CF_Avec_contDiff (hη : 0 < η) : ContDiff ℝ ∞ (CF_Avec D N Ac η E₁ E₂) :=
  contDiff_pi.mpr fun k => CF_A_contDiff D N Ac η (E₁ k) (E₂ k) hη

private lemma CF_Fc_contDiff (hη : 0 < η) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (CF_Fc D N Ac η F E₁ E₂) :=
  (Complex.ofRealCLM.contDiff.comp hF).comp (CF_Avec_contDiff D N Ac η E₁ E₂ hη)

/-- The edge counts are bounded by `Σ_k DN |E₂(k) - E₁(k)| / η` (proof of Lemma 4.3 [rescomY]). -/
private lemma CF_Avec_norm_le (hη : 0 < η) (v : Fin 1 → Coords (D * N)) :
    ‖CF_Avec D N Ac η E₁ E₂ v‖ ≤ ∑ k, ((D * N : ℕ) : ℝ) * |E₂ k - E₁ k| / η := by
  have h0 : 0 ≤ ∑ k, ((D * N : ℕ) : ℝ) * |E₂ k - E₁ k| / η :=
    Finset.sum_nonneg fun k _ => by positivity
  refine (pi_norm_le_iff_of_nonneg h0).mpr fun k => ?_
  have := edgeCount_abs_le D N Ac η (E₁ k) (E₂ k) hη (CF_arr D N v) (CF_arr_herm D N v)
  rw [Real.norm_eq_abs]
  exact this.trans (Finset.single_le_sum (f := fun k => ((D * N : ℕ) : ℝ) * |E₂ k - E₁ k| / η)
    (fun k _ => by positivity) (Finset.mem_univ k))

/-- The sum of the entries of the array of `u` is at most `(DN)² ‖arr‖ ‖u‖`. -/
private lemma CF_S_arr_le (u : Fin 1 → Coords (D * N)) :
    CF_S (CF_arr D N u) ≤ ((D * N : ℕ) : ℝ) ^ 2 * ‖CF_arr D N‖ * ‖u‖ := by
  have h1 : ∀ a b : Idx D N, ‖(CF_arr D N u) a b‖ ≤ ‖CF_arr D N‖ * ‖u‖ := fun a b =>
    ((norm_le_pi_norm ((CF_arr D N u) a) b).trans (norm_le_pi_norm (CF_arr D N u) a)).trans
      ((CF_arr D N).le_opNorm u)
  calc CF_S (CF_arr D N u) ≤ ∑ a : Idx D N, ∑ b : Idx D N, ‖CF_arr D N‖ * ‖u‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h1 a b
    _ = ((D * N : ℕ) : ℝ) ^ 2 * ‖CF_arr D N‖ * ‖u‖ := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod]
        ring

/-- The coordinates of the iterated derivative of a vector-valued function. -/
private lemma CF_pi_iter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (f : E → (Fin m → ℝ)) (hf : ContDiff ℝ ∞ f) (i : ℕ) (x : E) (u : Fin i → E) (k : Fin m) :
    iteratedFDeriv ℝ i f x u k = iteratedFDeriv ℝ i (fun y => f y k) x u := by
  have := ContinuousLinearMap.iteratedFDeriv_comp_left
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k) (hf.contDiffAt (x := x))
    (i := i) (by simp)
  exact (congrArg (fun L => L u) this).symm

/-- The first derivative of `(A_k)_k` is bounded. -/
private lemma CF_Avec_iter1_le (hη : 0 < η) (v : Fin 1 → Coords (D * N)) :
    ‖iteratedFDeriv ℝ 1 (CF_Avec D N Ac η E₁ E₂) v‖ ≤
      2 * η⁻¹ * (((D * N : ℕ) : ℝ) ^ 2 * ‖CF_arr D N‖) := by
  have hM : 0 ≤ ((D * N : ℕ) : ℝ) ^ 2 * ‖CF_arr D N‖ := by positivity
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  rw [CF_pi_iter _ (CF_Avec_contDiff D N Ac η E₁ E₂ hη), iteratedFDeriv_one_apply]
  simp only [Fin.prod_univ_one]
  have h1 := CF_fderiv_A_le D N Ac η (E₁ k) (E₂ k) hη v (m 0)
  have h2 := CF_S_arr_le D N (m 0)
  rw [Real.norm_eq_abs]
  change ‖fderiv ℝ (CF_A D N Ac η (E₁ k) (E₂ k)) v (m 0)‖ ≤ _
  calc _ ≤ 2 * η⁻¹ * CF_S (CF_arr D N (m 0)) := h1
    _ ≤ 2 * η⁻¹ * (((D * N : ℕ) : ℝ) ^ 2 * ‖CF_arr D N‖ * ‖m 0‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- The second derivative of `(A_k)_k` is bounded. -/
private lemma CF_Avec_iter2_le (hη : 0 < η) (v : Fin 1 → Coords (D * N)) :
    ‖iteratedFDeriv ℝ 2 (CF_Avec D N Ac η E₁ E₂) v‖ ≤
      2 * η⁻¹ * η⁻¹ * (((D * N : ℕ) : ℝ) ^ 2 * ‖CF_arr D N‖) ^ 2 := by
  have hM : 0 ≤ ((D * N : ℕ) : ℝ) ^ 2 * ‖CF_arr D N‖ := by positivity
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  rw [CF_pi_iter _ (CF_Avec_contDiff D N Ac η E₁ E₂ hη), iteratedFDeriv_two_apply]
  simp only [Fin.prod_univ_two]
  have h1 := CF_fderiv2_A_le D N Ac η (E₁ k) (E₂ k) hη v (m 0) (m 1)
  have h2 := CF_S_arr_le D N (m 0)
  have h3 := CF_S_arr_le D N (m 1)
  rw [Real.norm_eq_abs]
  change ‖fderiv ℝ (fderiv ℝ (CF_A D N Ac η (E₁ k) (E₂ k))) v (m 0) (m 1)‖ ≤ _
  have hS0 := CF_S_nonneg (CF_arr D N (m 0))
  have hS1 := CF_S_nonneg (CF_arr D N (m 1))
  calc _ ≤ 2 * η⁻¹ * η⁻¹ * CF_S (CF_arr D N (m 0)) * CF_S (CF_arr D N (m 1)) := h1
    _ ≤ 2 * η⁻¹ * η⁻¹ * (((D * N : ℕ) : ℝ) ^ 2 * ‖CF_arr D N‖ * ‖m 0‖) *
          (((D * N : ℕ) : ℝ) ^ 2 * ‖CF_arr D N‖ * ‖m 1‖) := by
        have hη' : 0 ≤ 2 * η⁻¹ * η⁻¹ := by positivity
        gcongr
    _ = _ := by ring

end Func

/-! ### Uniform bounds on `F(A)` and its first two derivatives -/

section FcBound

/-- The derivatives of orders `≤ 2` of a smooth function are bounded on a ball. -/
private lemma CF_deriv_bound {m : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : (Fin m → ℝ) → G) (hg : ContDiff ℝ ∞ g) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Fin m → ℝ, ‖y‖ ≤ R → ∀ i : ℕ, i ≤ 2 →
      ‖iteratedFDeriv ℝ i g y‖ ≤ C := by
  have hK : IsCompact (Metric.closedBall (0 : Fin m → ℝ) R) := isCompact_closedBall _ _
  have hb : ∀ i : ℕ, ∃ C : ℝ, ∀ y ∈ Metric.closedBall (0 : Fin m → ℝ) R,
      ‖iteratedFDeriv ℝ i g y‖ ≤ C := fun i =>
    hK.exists_bound_of_continuousOn (hg.continuous_iteratedFDeriv (by simp)).continuousOn
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range 3, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun y hy i hi => ?_⟩
  have hy' : y ∈ Metric.closedBall (0 : Fin m → ℝ) R := by simpa using hy
  have : |C i| ≤ ∑ i ∈ Finset.range 3, |C i| :=
    Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  linarith [hC i y hy', le_abs_self (C i)]

variable (D N : ℕ) (Ac : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) {n : ℕ} (F : (Fin n → ℝ) → ℝ)
  (E₁ E₂ : Fin n → ℝ)

/-- The derivatives of orders `0, 1, 2` of `F(A)` are bounded uniformly in the coordinates: the
hypothesis `hB` of `hasDerivAt_ouExpect` and `gueBlocks_ibp`. -/
private lemma CF_Fc_bound (hη : 0 < η) (hF : ContDiff ℝ ∞ F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (v : Fin 1 → Coords (D * N)) (j : ℕ), j ≤ 2 →
      ‖iteratedFDeriv ℝ j (CF_Fc D N Ac η F E₁ E₂) v‖ ≤ B := by
  set g : (Fin n → ℝ) → ℂ := fun y => ((F y : ℝ) : ℂ) with hg
  have hgs : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hF
  obtain ⟨C, hC0, hC⟩ := CF_deriv_bound g hgs (∑ k, ((D * N : ℕ) : ℝ) * |E₂ k - E₁ k| / η)
  set a₁ := 2 * η⁻¹ * (((D * N : ℕ) : ℝ) ^ 2 * ‖CF_arr D N‖) with ha₁
  set a₂ := 2 * η⁻¹ * η⁻¹ * (((D * N : ℕ) : ℝ) ^ 2 * ‖CF_arr D N‖) ^ 2 with ha₂
  set D' : ℝ := max 1 (max a₁ a₂) with hD'
  have hD1 : 1 ≤ D' := le_max_left _ _
  refine ⟨2 * C * D' ^ 2, by positivity, fun v j hj => ?_⟩
  have hF' : CF_Fc D N Ac η F E₁ E₂ = g ∘ CF_Avec D N Ac η E₁ E₂ := rfl
  rw [hF']
  have hAs := CF_Avec_contDiff D N Ac η E₁ E₂ hη
  have h := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := j) (N := ∞) hgs hAs
    (by exact_mod_cast le_top) v (C := C) (D := D')
    (fun i hi => hC _ (CF_Avec_norm_le D N Ac η E₁ E₂ hη v) i (hi.trans hj))
    (fun i hi1 hi2 => by
      have hi2' : i ≤ 2 := hi2.trans hj
      interval_cases i
      · exact (CF_Avec_iter1_le D N Ac η E₁ E₂ hη v).trans (by
          calc a₁ ≤ D' := (le_max_left _ _).trans (le_max_right _ _)
            _ = D' ^ 1 := (pow_one _).symm)
      · exact (CF_Avec_iter2_le D N Ac η E₁ E₂ hη v).trans (by
          calc a₂ ≤ D' := (le_max_right _ _).trans (le_max_right _ _)
            _ ≤ D' ^ 2 := by nlinarith))
  refine h.trans ?_
  have hfac : (j.factorial : ℝ) ≤ 2 := by
    interval_cases j <;> norm_num [Nat.factorial]
  have hpow : D' ^ j ≤ D' ^ 2 := pow_le_pow_right₀ hD1 hj
  calc (j.factorial : ℝ) * C * D' ^ j ≤ 2 * C * D' ^ 2 := by
        gcongr

/-- The first derivative of `F(A)` in the direction `u` is at most `K Σ |V_{ab}|`, `V` the array of
`u`: the dominating function of the `w`-integral in the proof of `CF_hasDerivAt`. -/
private lemma CF_Fc_fderiv_le (hη : 0 < η) (hF : ContDiff ℝ ∞ F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v u : Fin 1 → Coords (D * N),
      ‖fderiv ℝ (CF_Fc D N Ac η F E₁ E₂) v u‖ ≤ K * CF_S (CF_arr D N u) := by
  set g : (Fin n → ℝ) → ℂ := fun y => ((F y : ℝ) : ℂ) with hg
  have hgs : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hF
  obtain ⟨C, hC0, hC⟩ := CF_deriv_bound g hgs (∑ k, ((D * N : ℕ) : ℝ) * |E₂ k - E₁ k| / η)
  refine ⟨C * (2 * η⁻¹), by positivity, fun v u => ?_⟩
  have hAs := CF_Avec_contDiff D N Ac η E₁ E₂ hη
  have hF' : CF_Fc D N Ac η F E₁ E₂ = g ∘ CF_Avec D N Ac η E₁ E₂ := rfl
  have hcomp : fderiv ℝ (CF_Fc D N Ac η F E₁ E₂) v =
      (fderiv ℝ g (CF_Avec D N Ac η E₁ E₂ v)).comp (fderiv ℝ (CF_Avec D N Ac η E₁ E₂) v) := by
    rw [hF']
    exact fderiv_comp v (hgs.differentiable (by simp) _) (hAs.differentiable (by simp) v)
  rw [hcomp, ContinuousLinearMap.comp_apply]
  have h1 : ‖fderiv ℝ g (CF_Avec D N Ac η E₁ E₂ v)‖ ≤ C := by
    have := hC _ (CF_Avec_norm_le D N Ac η E₁ E₂ hη v) 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at this
  have hS := CF_S_nonneg (CF_arr D N u)
  have h2 : ‖fderiv ℝ (CF_Avec D N Ac η E₁ E₂) v u‖ ≤ 2 * η⁻¹ * CF_S (CF_arr D N u) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
    have : fderiv ℝ (CF_Avec D N Ac η E₁ E₂) v u k =
        fderiv ℝ (CF_A D N Ac η (E₁ k) (E₂ k)) v u := by
      have := CF_pi_iter (CF_Avec D N Ac η E₁ E₂) hAs 1 v (fun _ => u) k
      rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply] at this
      exact this
    rw [this]
    exact CF_fderiv_A_le D N Ac η (E₁ k) (E₂ k) hη v u
  calc ‖(fderiv ℝ g (CF_Avec D N Ac η E₁ E₂ v)) (fderiv ℝ (CF_Avec D N Ac η E₁ E₂) v u)‖
      ≤ ‖fderiv ℝ g (CF_Avec D N Ac η E₁ E₂ v)‖ * ‖fderiv ℝ (CF_Avec D N Ac η E₁ E₂) v u‖ :=
        (fderiv ℝ g _).le_opNorm _
    _ ≤ C * (2 * η⁻¹ * CF_S (CF_arr D N u)) := mul_le_mul h1 h2 (norm_nonneg _) hC0
    _ = C * (2 * η⁻¹) * CF_S (CF_arr D N u) := by ring

/-- The bounds on the derivatives of orders `0, 1, 2` in the pointwise form. -/
private lemma CF_bnd_of_iter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℂ)
    (B : ℝ)
    (h : ∀ v (j : ℕ), j ≤ 2 → ‖iteratedFDeriv ℝ j f v‖ ≤ B) :
    (∀ x, ‖f x‖ ≤ B) ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ B) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · have := h x 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero] at this
  · have := h x 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at this
  · have := h x 2 (by norm_num)
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this

end FcBound

/-! ### Integration by parts for the rescaled blocks and the derivative at one `w` -/

section IBP

variable {m : ℕ}

/-- `x ↦ ‖x‖` is integrable under the GUE blocks. -/
private lemma CF_integrable_norm (m : ℕ) :
    Integrable (fun x : Fin 1 → Coords m => ‖x‖) (gueBlocks 1 m) := by
  have : IsGaussian (gueBlocks 1 m) := by unfold gueBlocks; infer_instance
  exact memLp_one_iff_integrable.1 ((IsGaussian.memLp_id (gueBlocks 1 m) 1 (by simp)).norm)

private lemma CF_norm_bD (i : Fin m) : ‖bD (0 : Fin 1) i‖ ≤ 1 := by
  simp [bD, Pi.norm_single, Prod.norm_def]

private lemma CF_norm_bRe (i j : Fin m) : ‖bRe (0 : Fin 1) i j‖ ≤ 1 := by
  simp [bRe, Pi.norm_single, Prod.norm_def]

private lemma CF_norm_bIm (i j : Fin m) : ‖bIm (0 : Fin 1) i j‖ ≤ 1 := by
  simp [bIm, Pi.norm_single, Prod.norm_def]

/-- `gLap F` is bounded by `(m + m²) B` when the second derivative is bounded by `B`. -/
private lemma CF_gLap_le (F : (Fin 1 → Coords m) → ℂ) (hF : ContDiff ℝ 2 F) (B : ℝ)
    (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ B) (y : Fin 1 → Coords m) :
    ‖gLap F y‖ ≤ ((m : ℝ) + (m : ℝ) ^ 2) * B := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ F) 0)) (h2 0)
  have hd : ∀ v : Fin 1 → Coords m, ‖v‖ ≤ 1 → ‖d2 F y v‖ ≤ B := by
    intro v hv
    rw [CF_d2_eq F hF]
    calc ‖fderiv ℝ (fderiv ℝ F) y v v‖ ≤ ‖fderiv ℝ (fderiv ℝ F) y v‖ * ‖v‖ :=
          (fderiv ℝ (fderiv ℝ F) y v).le_opNorm v
      _ ≤ (‖fderiv ℝ (fderiv ℝ F) y‖ * ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ F) y).le_opNorm v) (norm_nonneg _)
      _ ≤ (B * 1) * 1 := by
          have h3 : ‖fderiv ℝ (fderiv ℝ F) y‖ * ‖v‖ ≤ B * 1 :=
            mul_le_mul (h2 y) hv (norm_nonneg _) hB0
          exact mul_le_mul h3 hv (norm_nonneg _) (by positivity)
      _ = B := by ring
  unfold gLap
  have t1 : ‖∑ a : Fin 1, ∑ i : Fin m, d2 F y (bD a i)‖ ≤ (m : ℝ) * B := by
    simp only [Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
    calc ‖∑ i : Fin m, d2 F y (bD (0 : Fin 1) i)‖ ≤ ∑ i : Fin m, ‖d2 F y (bD (0 : Fin 1) i)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _i : Fin m, B := Finset.sum_le_sum fun i _ => hd _ (CF_norm_bD i)
      _ = (m : ℝ) * B := by simp
  have t2 : ‖∑ a : Fin 1, ∑ i : Fin m, ∑ j : Fin m,
      (d2 F y (bRe a i j) + d2 F y (bIm a i j))‖ ≤ (m : ℝ) ^ 2 * (2 * B) := by
    simp only [Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
    calc ‖∑ i : Fin m, ∑ j : Fin m,
          (d2 F y (bRe (0 : Fin 1) i j) + d2 F y (bIm (0 : Fin 1) i j))‖
        ≤ ∑ i : Fin m, ‖∑ j : Fin m,
          (d2 F y (bRe (0 : Fin 1) i j) + d2 F y (bIm (0 : Fin 1) i j))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin m, ∑ j : Fin m, ‖d2 F y (bRe (0 : Fin 1) i j) + d2 F y (bIm (0 : Fin 1) i j)‖ :=
          Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, (B + B) := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => (norm_add_le _ _).trans
            (add_le_add (hd _ (CF_norm_bRe i j)) (hd _ (CF_norm_bIm i j)))
      _ = (m : ℝ) ^ 2 * (2 * B) := by simp; ring
  calc ‖(∑ a : Fin 1, ∑ i : Fin m, d2 F y (bD a i)) + (1 / 2 : ℂ) * ∑ a : Fin 1, ∑ i : Fin m,
        ∑ j : Fin m, (d2 F y (bRe a i j) + d2 F y (bIm a i j))‖
      ≤ ‖∑ a : Fin 1, ∑ i : Fin m, d2 F y (bD a i)‖ + ‖(1 / 2 : ℂ) * ∑ a : Fin 1, ∑ i : Fin m,
        ∑ j : Fin m, (d2 F y (bRe a i j) + d2 F y (bIm a i j))‖ := norm_add_le _ _
    _ ≤ (m : ℝ) * B + (1 / 2) * ((m : ℝ) ^ 2 * (2 * B)) := by
        gcongr
        rw [norm_mul]
        gcongr
        · norm_num
    _ = ((m : ℝ) + (m : ℝ) ^ 2) * B := by ring

/-- `gLap F` is continuous for `F` of class `C²`. -/
private lemma CF_continuous_gLap (F : (Fin 1 → Coords m) → ℂ) (hF : ContDiff ℝ 2 F) :
    Continuous (gLap F) := by
  have hc : ∀ v : Fin 1 → Coords m, Continuous fun y => d2 F y v := by
    intro v
    simp_rw [CF_d2_eq F hF]
    exact (((hF.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const
  unfold gLap
  exact (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => hc _).add
    (continuous_const.mul (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => (hc _).add (hc _)))

end IBP

/-! ### The rescaled blocks `x ↦ F (c + σ x)` -/

section Pull

variable {m : ℕ}

/-- The derivative of `x ↦ F (c + σ x)`. -/
private lemma CF_fderiv_pull (F : (Fin 1 → Coords m) → ℂ) (hF : ContDiff ℝ 1 F)
    (c : Fin 1 → Coords m) (σ : ℝ) (y u : Fin 1 → Coords m) :
    fderiv ℝ (fun y => F (c + σ • y)) y u = σ • fderiv ℝ F (c + σ • y) u := by
  have := CF_fderiv_affine F hF c (σ • ContinuousLinearMap.id ℝ (Fin 1 → Coords m)) y u
  simpa using this

/-- `gLap` of `x ↦ F (c + σ x)`. -/
private lemma CF_gLap_pull (F : (Fin 1 → Coords m) → ℂ) (hF : ContDiff ℝ 2 F)
    (c : Fin 1 → Coords m) (σ : ℝ) (y : Fin 1 → Coords m) :
    gLap (fun y => F (c + σ • y)) y = ((σ * σ : ℝ) : ℂ) * gLap F (c + σ • y) := by
  have hd2 : ∀ v, d2 (fun y => F (c + σ • y)) y v = ((σ * σ : ℝ) : ℂ) * d2 F (c + σ • y) v := by
    intro v
    have := CF_d2_affine F hF c (σ • ContinuousLinearMap.id ℝ (Fin 1 → Coords m)) y v
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply] at this
    rw [this, CF_d2_smul F hF]
  simp only [gLap, hd2, ← mul_add, ← Finset.mul_sum]
  ring

/-- The bounds on the orders `≤ 2` pass to `x ↦ F (c + σ x)` for `0 ≤ σ ≤ 1`. -/
private lemma CF_iter_pull (F : (Fin 1 → Coords m) → ℂ) (hF : ContDiff ℝ 2 F)
    (c : Fin 1 → Coords m) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (B : ℝ)
    (h : ∀ v (j : ℕ), j ≤ 2 → ‖iteratedFDeriv ℝ j F v‖ ≤ B) :
    ∀ v (j : ℕ), j ≤ 2 → ‖iteratedFDeriv ℝ j (fun y => F (c + σ • y)) v‖ ≤ B := by
  intro v j hj
  have hG : ContDiff ℝ 2 (fun z => F (c + z)) := hF.comp (contDiff_const.add contDiff_id)
  have hGj : ContDiff ℝ (j : ℕ) (fun z => F (c + z)) := hG.of_le (by exact_mod_cast hj)
  have e := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := j) σ hGj
  have e2 : (fun y => F (c + σ • y)) = fun z => (fun z => F (c + z)) (σ • z) := rfl
  rw [e2, e]
  simp only
  rw [iteratedFDeriv_comp_add_left, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hσ0]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (h 0 0 (by norm_num))
  calc σ ^ j * ‖iteratedFDeriv ℝ j F (c + σ • v)‖ ≤ 1 * B :=
        mul_le_mul (pow_le_one₀ hσ0 hσ1) (h _ j hj) (norm_nonneg _) zero_le_one
    _ = B := one_mul B

/-- Integration by parts for the rescaled blocks: `E DF(c + σX)·X = σ E gLap F(c + σX)` for
`0 < σ ≤ 1` (Gaussian integration by parts `gueBlocks_ibp`). -/
private lemma CF_ou_ibp (F : (Fin 1 → Coords m) → ℂ) (hF : ContDiff ℝ 2 F) (B : ℝ)
    (h : ∀ v (j : ℕ), j ≤ 2 → ‖iteratedFDeriv ℝ j F v‖ ≤ B)
    (c : Fin 1 → Coords m) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ∫ x, fderiv ℝ F (c + σ • x) x ∂(gueBlocks 1 m) =
      (σ : ℂ) * ∫ x, gLap F (c + σ • x) ∂(gueBlocks 1 m) := by
  have hG : ContDiff ℝ 2 (fun y => F (c + σ • y)) :=
    hF.comp (contDiff_const.add (contDiff_id.const_smul σ))
  have e := gueBlocks_ibp 1 m (fun y => F (c + σ • y)) B hG
    (fun j _ hj2 v => CF_iter_pull F hF c σ hσ0.le hσ1 B h v j hj2)
  have l1 : ∫ x, fderiv ℝ (fun y => F (c + σ • y)) x x ∂(gueBlocks 1 m) =
      (σ : ℂ) * ∫ x, fderiv ℝ F (c + σ • x) x ∂(gueBlocks 1 m) := by
    simp only [CF_fderiv_pull F (hF.of_le (by norm_num)) c σ, Complex.real_smul]
    exact integral_const_mul _ _
  have l2 : ∫ x, gLap (fun y => F (c + σ • y)) x ∂(gueBlocks 1 m) =
      ((σ * σ : ℝ) : ℂ) * ∫ x, gLap F (c + σ • x) ∂(gueBlocks 1 m) := by
    simp only [CF_gLap_pull F hF c σ]
    exact integral_const_mul _ _
  rw [l1, l2] at e
  have hσ : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  have : (σ : ℂ) * (∫ x, fderiv ℝ F (c + σ • x) x ∂(gueBlocks 1 m) -
      (σ : ℂ) * ∫ x, gLap F (c + σ • x) ∂(gueBlocks 1 m)) = 0 := by
    push_cast at e
    linear_combination e
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hσ
  · exact sub_eq_zero.mp h'

end Pull

/-! ### The derivative at one `w` -/

section DerivW

variable {m : ℕ}

/-- The point `ouPoint 1 m t c x` depends continuously on `x`. -/
private lemma CF_continuous_ouPoint (t : ℝ) (c : Fin 1 → Coords m) :
    Continuous fun x : Fin 1 → Coords m => ouPoint 1 m t c x := by
  unfold ouPoint
  fun_prop

/-- `∂_t E F(e^{-t/2} c + √(1 - e^{-t}) X)` after the integration by parts: the integrand of
`hasDerivAt_ouExpect` and the form `E(-½ DF(H_t)·H_t + ½ gLap F(H_t))` (display before (4.9)
[eq:prodnGt]) have the same integral, for `t > 0`. -/
private lemma CF_deriv_formula (F : (Fin 1 → Coords m) → ℂ) (hF : ContDiff ℝ 2 F) (B : ℝ)
    (h : ∀ v (j : ℕ), j ≤ 2 → ‖iteratedFDeriv ℝ j F v‖ ≤ B) (c : Fin 1 → Coords m) (t : ℝ)
    (ht : 0 < t) :
    ∫ x, (-(1 / 2 : ℂ) * (Real.exp (-t / 2) : ℂ) * fderiv ℝ F (ouPoint 1 m t c x) c +
        (1 / 2 : ℂ) * (Real.exp (-t) : ℂ) * gLap F (ouPoint 1 m t c x)) ∂(gueBlocks 1 m) =
      ∫ x, (-(1 / 2 : ℂ) * fderiv ℝ F (ouPoint 1 m t c x) (ouPoint 1 m t c x) +
        (1 / 2 : ℂ) * gLap F (ouPoint 1 m t c x)) ∂(gueBlocks 1 m) := by
  obtain ⟨h0, h1, h2⟩ := CF_bnd_of_iter F B h
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (h0 0)
  set σ : ℝ := Real.sqrt (1 - Real.exp (-t)) with hσ
  set e : ℝ := Real.exp (-t / 2) with he
  have hexp1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr (by linarith)
  have hσ1 : σ ≤ 1 := by
    rw [hσ]
    calc Real.sqrt (1 - Real.exp (-t)) ≤ Real.sqrt 1 :=
          Real.sqrt_le_sqrt (by linarith [Real.exp_pos (-t)])
      _ = 1 := Real.sqrt_one
  have hσσ : σ * σ = 1 - Real.exp (-t) := Real.mul_self_sqrt (by linarith)
  have hP : ∀ x, ouPoint 1 m t c x = e • c + σ • x := fun x => rfl
  have ibp := CF_ou_ibp F hF B h (e • c) σ hσ0 hσ1
  simp only [← hP] at ibp
  have hpt := CF_continuous_ouPoint t c
  have hDc : Continuous (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).continuous
  have hI1 : Integrable (fun x => fderiv ℝ F (ouPoint 1 m t c x) c) (gueBlocks 1 m) :=
    Integrable.of_bound ((hDc.comp hpt).clm_apply continuous_const).aestronglyMeasurable
      (B * ‖c‖) (Filter.Eventually.of_forall fun x => by
        calc ‖fderiv ℝ F (ouPoint 1 m t c x) c‖ ≤ ‖fderiv ℝ F (ouPoint 1 m t c x)‖ * ‖c‖ :=
              (fderiv ℝ F _).le_opNorm c
          _ ≤ B * ‖c‖ := mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _))
  have hI2 : Integrable (fun x => fderiv ℝ F (ouPoint 1 m t c x) x) (gueBlocks 1 m) := by
    refine Integrable.mono' ((CF_integrable_norm m).const_mul B)
      ((hDc.comp hpt).clm_apply continuous_id).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    calc ‖fderiv ℝ F (ouPoint 1 m t c x) x‖ ≤ ‖fderiv ℝ F (ouPoint 1 m t c x)‖ * ‖x‖ :=
          (fderiv ℝ F _).le_opNorm x
      _ ≤ B * ‖x‖ := mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _)
  have hI3 : Integrable (fun x => gLap F (ouPoint 1 m t c x)) (gueBlocks 1 m) :=
    Integrable.of_bound ((CF_continuous_gLap F hF).comp hpt).aestronglyMeasurable
      (((m : ℝ) + (m : ℝ) ^ 2) * B)
      (Filter.Eventually.of_forall fun x => CF_gLap_le F hF B h2 _)
  have hDP : ∀ x, fderiv ℝ F (ouPoint 1 m t c x) (ouPoint 1 m t c x) =
      (e : ℂ) * fderiv ℝ F (ouPoint 1 m t c x) c + (σ : ℂ) * fderiv ℝ F (ouPoint 1 m t c x) x := by
    intro x
    rw [hP x, map_add, map_smul, map_smul]
    simp only [← hP x, Complex.real_smul]
  have hexpc : (Real.exp (-t) : ℂ) = 1 - (σ : ℂ) * (σ : ℂ) := by
    rw [← Complex.ofReal_mul, hσσ]; push_cast; ring
  have hR : (fun x => -(1 / 2 : ℂ) * fderiv ℝ F (ouPoint 1 m t c x) (ouPoint 1 m t c x) +
        (1 / 2 : ℂ) * gLap F (ouPoint 1 m t c x)) =
      fun x => (-(1 / 2 : ℂ) * (e : ℂ) * fderiv ℝ F (ouPoint 1 m t c x) c +
        (1 / 2 : ℂ) * (Real.exp (-t) : ℂ) * gLap F (ouPoint 1 m t c x)) +
        (-(1 / 2 : ℂ) * (σ : ℂ)) * (fderiv ℝ F (ouPoint 1 m t c x) x -
          (σ : ℂ) * gLap F (ouPoint 1 m t c x)) := by
    funext x
    rw [hDP x, hexpc]
    ring
  have hLint : Integrable (fun x => -(1 / 2 : ℂ) * (e : ℂ) * fderiv ℝ F (ouPoint 1 m t c x) c +
      (1 / 2 : ℂ) * (Real.exp (-t) : ℂ) * gLap F (ouPoint 1 m t c x)) (gueBlocks 1 m) :=
    (hI1.const_mul _).add (hI3.const_mul _)
  have hcorr : Integrable (fun x => (-(1 / 2 : ℂ) * (σ : ℂ)) *
      (fderiv ℝ F (ouPoint 1 m t c x) x - (σ : ℂ) * gLap F (ouPoint 1 m t c x)))
      (gueBlocks 1 m) := (hI2.sub (hI3.const_mul _)).const_mul _
  rw [hR, integral_add hLint hcorr, integral_const_mul, integral_sub hI2 (hI3.const_mul _),
    integral_const_mul, ibp]
  simp

end DerivW

/-! ### The expectation `t ↦ E_{H_t} F(A)` as an iterated integral -/

section Main

variable (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (Ac : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) {n : ℕ}
  (F : (Fin n → ℝ) → ℝ) (E₁ E₂ : Fin n → ℝ)

/-- The set of Hermitian arrays is closed. -/
private lemma CF_isClosed_herm (D N : ℕ) :
    IsClosed {h : Idx D N → Idx D N → ℂ | (Matrix.of h).IsHermitian} := by
  have : {h : Idx D N → Idx D N → ℂ | (Matrix.of h).IsHermitian} =
      ⋂ p : Idx D N, ⋂ q : Idx D N, {h | star (h q p) = h p q} := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact Matrix.IsHermitian.ext_iff
  rw [this]
  refine isClosed_iInter fun p => isClosed_iInter fun q => ?_
  exact isClosed_eq (continuous_star.comp ((continuous_apply p).comp (continuous_apply q)))
    ((continuous_apply q).comp (continuous_apply p))

/-- Almost every `h` under the law of `H_s` is Hermitian, for every real `s`. -/
private lemma CF_herm_ae (s : ℝ) : ∀ᵐ h ∂(ouMatLaw D N L s), (Matrix.of h).IsHermitian := by
  rw [CF_ouMatLaw_eq, ae_map_iff (CF_continuous_Psi D N s).measurable.aemeasurable
    (CF_isClosed_herm D N).measurableSet]
  exact Filter.Eventually.of_forall fun q => CF_arr_herm D N _

/-- `G ∘ symArr` for `G = edgeFn`, as a complex-valued function of the array. -/
private def CF_Phi (h : Idx D N → Idx D N → ℂ) : ℂ :=
  ((edgeFn D N Ac η F E₁ E₂ (symArr h) : ℝ) : ℂ)

private lemma CF_Phi_contDiff (hη : 0 < η) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (CF_Phi D N Ac η F E₁ E₂) := by
  have : ContDiff ℝ ∞ (fun h => edgeFn D N Ac η F E₁ E₂ (symArr h)) :=
    hF.comp (contDiff_pi.mpr fun i => edgeCount_contDiff D N Ac η (E₁ i) (E₂ i) hη)
  exact Complex.ofRealCLM.contDiff.comp this

private lemma CF_edgeFn_eq (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ((edgeFn D N Ac η F E₁ E₂ h : ℝ) : ℂ) = CF_Phi D N Ac η F E₁ E₂ h := by
  simp only [CF_Phi, symArr_of_isHermitian h hh]

private lemma CF_Fc_eq_Phi (v : Fin 1 → Coords (D * N)) :
    CF_Fc D N Ac η F E₁ E₂ v = CF_Phi D N Ac η F E₁ E₂ (CF_arr D N v) := by
  rw [CF_Fc_eq]
  simp only [CF_Phi, CF_symArr_arr]

/-- `E_{H_s} F(A)` as an integral over `blockLaw ⊗ gueBlocks 1 (DN)`, every `s`. -/
private lemma CF_expect_Om (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (s : ℝ) :
    ∫ h, ((edgeFn D N Ac η F E₁ E₂ h : ℝ) : ℂ) ∂(ouMatLaw D N L s) =
      ∫ q, CF_Phi D N Ac η F E₁ E₂ (CF_Psi D N s q)
        ∂((blockLaw D N L).prod (gueBlocks 1 (D * N))) := by
  have hae : (fun h => ((edgeFn D N Ac η F E₁ E₂ h : ℝ) : ℂ)) =ᵐ[ouMatLaw D N L s]
      CF_Phi D N Ac η F E₁ E₂ :=
    (CF_herm_ae D N L s).mono fun h hh => CF_edgeFn_eq D N Ac η F E₁ E₂ h hh
  have hcont : Continuous (CF_Phi D N Ac η F E₁ E₂) :=
    (CF_Phi_contDiff D N Ac η F E₁ E₂ hη hF).continuous
  rw [integral_congr_ae hae, CF_integral_ou D N L s _ hcont.measurable]

/-- The bound `‖F(A)‖ ≤ B` along the law of `H_s`. -/
private lemma CF_Phi_Psi_le (hη : 0 < η) (hF : ContDiff ℝ ∞ F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (s : ℝ) (q : CF_Om D N), ‖CF_Phi D N Ac η F E₁ E₂ (CF_Psi D N s q)‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := CF_Fc_bound D N Ac η F E₁ E₂ hη hF
  refine ⟨B, hB0, fun s q => ?_⟩
  have := hB (ouPoint 1 (D * N) s (fun _ => blockEmb D N q.1) q.2) 0 (by norm_num)
  rw [norm_iteratedFDeriv_zero, CF_Fc_eq_Phi] at this
  exact this

/-- (4.3) [eq:eq_in_law_H] through one block of size `DN` for `E_{H_s} F(A)`, every `s`. -/
private lemma CF_expect_eq (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (s : ℝ) :
    ∫ h, ((edgeFn D N Ac η F E₁ E₂ h : ℝ) : ℂ) ∂(ouMatLaw D N L s) =
      ∫ w, (∫ x, CF_Fc D N Ac η F E₁ E₂ (ouPoint 1 (D * N) s (fun _ => blockEmb D N w) x)
        ∂(gueBlocks 1 (D * N))) ∂(blockLaw D N L) := by
  obtain ⟨B, hB0, hB⟩ := CF_Phi_Psi_le D N Ac η F E₁ E₂ hη hF
  have hcont : Continuous (CF_Phi D N Ac η F E₁ E₂) :=
    (CF_Phi_contDiff D N Ac η F E₁ E₂ hη hF).continuous
  rw [CF_expect_Om D N L Ac η F E₁ E₂ hη hF s]
  have hint : Integrable (fun q => CF_Phi D N Ac η F E₁ E₂ (CF_Psi D N s q))
      ((blockLaw D N L).prod (gueBlocks 1 (D * N))) :=
    Integrable.of_bound (hcont.comp (CF_continuous_Psi D N s)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun q => hB s q)
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [CF_Fc_eq_Phi]
  rfl

end Main

/-! ### The integrands of `entryDrift` and `entryGen` -/

section Theta

variable (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (Ac : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) {n : ℕ}
  (F : (Fin n → ℝ) → ℝ) (E₁ E₂ : Fin n → ℝ)

/-- The integrand of `entryDrift`: `h̄_{ij} ∂_{w̄} G(setEntry h i j w)|_{w = h_{ij}}`. -/
private def CF_thDr (i j : Idx D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  starRingEnd ℂ (h i j) *
    wirt 0 1 (fun w => ((edgeFn D N Ac η F E₁ E₂ (setEntry h i j w) : ℝ) : ℂ)) (h i j)

/-- The integrand of `entryGen`: `∂_w ∂_{w̄} G(setEntry h i j w)|_{w = h_{ij}}`. -/
private def CF_thGen (i j : Idx D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  wirt 1 1 (fun w => ((edgeFn D N Ac η F E₁ E₂ (setEntry h i j w) : ℝ) : ℂ)) (h i j)

/-- `setEntry` is jointly continuous in the array and the value. -/
private lemma CF_continuous_setEntry (i j : Idx D N) :
    Continuous fun p : (Idx D N → Idx D N → ℂ) × ℂ => setEntry p.1 i j p.2 := by
  refine continuous_pi fun k => continuous_pi fun l => ?_
  unfold setEntry
  by_cases hij : i = j
  · simp only [hij, ite_true]
    split_ifs
    · exact Complex.continuous_ofReal.comp (Complex.continuous_re.comp continuous_snd)
    · exact (continuous_apply l).comp ((continuous_apply k).comp continuous_fst)
  · simp only [hij, ite_false]
    split_ifs
    · exact continuous_snd
    · exact Complex.continuous_conj.comp continuous_snd
    · exact (continuous_apply l).comp ((continuous_apply k).comp continuous_fst)

/-- The slice values of a Hermitian array are those of `G ∘ symArr`. -/
private lemma CF_slice_eq_Phi (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) :
    (fun w => ((edgeFn D N Ac η F E₁ E₂ (setEntry h i j w) : ℝ) : ℂ)) =
      fun w => CF_Phi D N Ac η F E₁ E₂ (setEntry h i j w) := by
  funext w
  exact CF_edgeFn_eq D N Ac η F E₁ E₂ _ (CF_setEntry_herm h hh i j w)

/-- The continuous version of `CF_thDr`, equal to it at Hermitian arrays. -/
private def CF_thDr' (i j : Idx D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  starRingEnd ℂ (h i j) * ((1 / 2 : ℂ) *
    (fderiv ℝ (CF_Phi D N Ac η F E₁ E₂) (setEntry h i j (h i j)) (setEntry 0 i j 1) +
      Complex.I * fderiv ℝ (CF_Phi D N Ac η F E₁ E₂) (setEntry h i j (h i j))
        (setEntry 0 i j Complex.I)))

/-- The continuous version of `CF_thGen`, equal to it at Hermitian arrays. -/
private def CF_thGen' (i j : Idx D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  (1 / 4 : ℂ) * (d2 (CF_Phi D N Ac η F E₁ E₂) (setEntry h i j (h i j)) (setEntry 0 i j 1) +
    d2 (CF_Phi D N Ac η F E₁ E₂) (setEntry h i j (h i j)) (setEntry 0 i j Complex.I))

private lemma CF_thDr_eq (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    CF_thDr D N Ac η F E₁ E₂ i j h = CF_thDr' D N Ac η F E₁ E₂ i j h := by
  unfold CF_thDr CF_thDr'
  rw [CF_slice_eq_Phi D N Ac η F E₁ E₂ h hh i j,
    CF_slice_wirt01 _ ((CF_Phi_contDiff D N Ac η F E₁ E₂ hη hF).of_le (by simp))]

private lemma CF_thGen_eq (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    CF_thGen D N Ac η F E₁ E₂ i j h = CF_thGen' D N Ac η F E₁ E₂ i j h := by
  unfold CF_thGen CF_thGen'
  rw [CF_slice_eq_Phi D N Ac η F E₁ E₂ h hh i j,
    CF_slice_wirt11 _ ((CF_Phi_contDiff D N Ac η F E₁ E₂ hη hF).of_le (by simp))]

private lemma CF_continuous_thDr' (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (i j : Idx D N) :
    Continuous (CF_thDr' D N Ac η F E₁ E₂ i j) := by
  have hΦ := CF_Phi_contDiff D N Ac η F E₁ E₂ hη hF
  have hDc : Continuous (fderiv ℝ (CF_Phi D N Ac η F E₁ E₂)) :=
    hΦ.continuous_fderiv (by simp)
  have hse : Continuous fun h : Idx D N → Idx D N → ℂ => setEntry h i j (h i j) :=
    (CF_continuous_setEntry D N i j).comp
      (continuous_id.prodMk ((continuous_apply j).comp (continuous_apply i)))
  unfold CF_thDr'
  exact (Complex.continuous_conj.comp ((continuous_apply j).comp (continuous_apply i))).mul
    (continuous_const.mul (((hDc.comp hse).clm_apply continuous_const).add
      (continuous_const.mul ((hDc.comp hse).clm_apply continuous_const))))

private lemma CF_continuous_thGen' (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (i j : Idx D N) :
    Continuous (CF_thGen' D N Ac η F E₁ E₂ i j) := by
  have hΦ := CF_Phi_contDiff D N Ac η F E₁ E₂ hη hF
  have hΦ2 : ContDiff ℝ 2 (CF_Phi D N Ac η F E₁ E₂) := hΦ.of_le (by simp)
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ (CF_Phi D N Ac η F E₁ E₂))) :=
    (hΦ2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hse : Continuous fun h : Idx D N → Idx D N → ℂ => setEntry h i j (h i j) :=
    (CF_continuous_setEntry D N i j).comp
      (continuous_id.prodMk ((continuous_apply j).comp (continuous_apply i)))
  have hd : ∀ v, Continuous fun h : Idx D N → Idx D N → ℂ =>
      d2 (CF_Phi D N Ac η F E₁ E₂) (setEntry h i j (h i j)) v := by
    intro v
    simp_rw [CF_d2_eq _ hΦ2]
    exact (((hD2.comp hse).clm_apply continuous_const).clm_apply continuous_const)
  unfold CF_thGen'
  exact continuous_const.mul ((hd _).add (hd _))

/-- The Wirtinger derivatives of order `1 ≤ p + q ≤ 2` of the slices of `edgeFn` at Hermitian arrays
are bounded uniformly (`edgeFn_wirt_le` with `Γ = Γ_I = max 1 η⁻¹`). -/
private lemma CF_edgeFn_wirt_bound (p q : ℕ) (hpq : 1 ≤ p + q) (hpq2 : p + q ≤ 2) (hη : 0 < η)
    (hF : ContDiff ℝ ∞ F) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      ∀ (i j : Idx D N) (z : ℂ),
        ‖wirt p q (fun w' => ((edgeFn D N Ac η F E₁ E₂ (setEntry h i j w') : ℝ) : ℂ)) z‖ ≤ W := by
  obtain ⟨K, hK, H⟩ := edgeFn_wirt_le n p q hpq
  obtain ⟨C0, hC0, hC⟩ := CF_deriv_bound F hF (∑ k, ((D * N : ℕ) : ℝ) * |E₂ k - E₁ k| / η)
  set Γ : ℝ := max 1 η⁻¹ with hΓ
  have hΓ1 : 1 ≤ Γ := le_max_left _ _
  refine ⟨K * C0 * Γ * Γ ^ (p + q - 1), by positivity, fun h hh i j z => ?_⟩
  have hX : (Matrix.of (setEntry h i j z) + lam D N Ac).IsHermitian :=
    (CF_setEntry_herm h hh i j z).add (lam_isHermitian D N Ac)
  refine H D N Ac η hη F hF E₁ E₂ h hh i j z C0 Γ Γ hΓ1 (by linarith) le_rfl ?_ ?_
  · intro k hk1 hk2
    refine hC _ ?_ k (by omega)
    have h0 : 0 ≤ ∑ k, ((D * N : ℕ) : ℝ) * |E₂ k - E₁ k| / η :=
      Finset.sum_nonneg fun k _ => by positivity
    refine (pi_norm_le_iff_of_nonneg h0).mpr fun m => ?_
    have := edgeCount_abs_le D N Ac η (E₁ m) (E₂ m) hη (setEntry h i j z)
      (CF_setEntry_herm h hh i j z)
    rw [Real.norm_eq_abs]
    exact this.trans (Finset.single_le_sum
      (f := fun k => ((D * N : ℕ) : ℝ) * |E₂ k - E₁ k| / η) (fun k _ => by positivity)
      (Finset.mem_univ m))
  · intro r a b _ _
    have hz : (edgePt η E₁ E₂ r).im = η := by
      unfold edgePt
      split_ifs <;> simp
    have h1 := CF_entries_le _ hX (edgePt η E₁ E₂ r) η hη hz a b
    have h2 : η⁻¹ ≤ Γ := le_max_right _ _
    exact ⟨h1.1.trans h2, h1.2.trans h2⟩

end Theta

/-! ### The derivative as `entryDeriv` -/

section Main2

variable (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (Ac : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) {n : ℕ}
  (F : (Fin n → ℝ) → ℝ) (E₁ E₂ : Fin n → ℝ)

private lemma CF_isProb (s : ℝ) : IsProbabilityMeasure (ouMatLaw D N L s) := by
  rw [CF_ouMatLaw_eq]
  infer_instance

/-- The integrand `thDr` is integrable under `ouMatLaw D N L t`, `t ≥ 0`. -/
private lemma CF_thDr_int (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (t : ℝ) (ht : 0 ≤ t)
    (i j : Idx D N) :
    Integrable (CF_thDr D N Ac η F E₁ E₂ i j) (ouMatLaw D N L t) := by
  have := CF_isProb D N L t
  obtain ⟨W, hW0, hW⟩ := CF_edgeFn_wirt_bound D N Ac η F E₁ E₂ 0 1 (by norm_num) (by norm_num) hη hF
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  have hI := (hC' N L t ht).integrable 1 i j
  have hmeas : AEStronglyMeasurable (CF_thDr D N Ac η F E₁ E₂ i j) (ouMatLaw D N L t) :=
    (CF_continuous_thDr' D N Ac η F E₁ E₂ hη hF i j).aestronglyMeasurable.congr
      ((CF_herm_ae D N L t).mono fun h hh => (CF_thDr_eq D N Ac η F E₁ E₂ hη hF h hh i j).symm)
  refine Integrable.mono' (hI.const_mul W) hmeas ?_
  filter_upwards [CF_herm_ae D N L t] with h hh
  unfold CF_thDr
  rw [norm_mul, Complex.norm_conj, pow_one]
  calc ‖h i j‖ * ‖wirt 0 1 (fun w =>
        ((edgeFn D N Ac η F E₁ E₂ (setEntry h i j w) : ℝ) : ℂ)) (h i j)‖
      ≤ ‖h i j‖ * W := mul_le_mul_of_nonneg_left (hW h hh i j _) (norm_nonneg _)
    _ = W * ‖h i j‖ := mul_comm _ _

/-- The integrand `thGen` is integrable under `ouMatLaw D N L t`. -/
private lemma CF_thGen_int (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (t : ℝ) (i j : Idx D N) :
    Integrable (CF_thGen D N Ac η F E₁ E₂ i j) (ouMatLaw D N L t) := by
  have := CF_isProb D N L t
  obtain ⟨W, hW0, hW⟩ := CF_edgeFn_wirt_bound D N Ac η F E₁ E₂ 1 1 (by norm_num) (by norm_num) hη hF
  have hmeas : AEStronglyMeasurable (CF_thGen D N Ac η F E₁ E₂ i j) (ouMatLaw D N L t) :=
    (CF_continuous_thGen' D N Ac η F E₁ E₂ hη hF i j).aestronglyMeasurable.congr
      ((CF_herm_ae D N L t).mono fun h hh => (CF_thGen_eq D N Ac η F E₁ E₂ hη hF h hh i j).symm)
  refine Integrable.of_bound hmeas W ?_
  filter_upwards [CF_herm_ae D N L t] with h hh
  exact hW h hh i j _

/-- `∫ θ dν = ∫ θ ∘ Ψ dμ` for an integrable `θ` (a.e. equal to a continuous function). -/
private lemma CF_integral_theta (t : ℝ) (θ : (Idx D N → Idx D N → ℂ) → ℂ)
    (hθ : AEStronglyMeasurable θ (ouMatLaw D N L t)) :
    ∫ h, θ h ∂(ouMatLaw D N L t) =
      ∫ q, θ (CF_Psi D N t q) ∂((blockLaw D N L).prod (gueBlocks 1 (D * N))) := by
  have hθ' := hθ
  rw [CF_ouMatLaw_eq] at hθ'
  rw [CF_ouMatLaw_eq]
  exact integral_map (CF_continuous_Psi D N t).measurable.aemeasurable hθ'

end Main2

section Main3

variable (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (Ac : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) {n : ℕ}
  (F : (Fin n → ℝ) → ℝ) (E₁ E₂ : Fin n → ℝ)

private lemma CF_G_contDiff (hη : 0 < η) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun h => edgeFn D N Ac η F E₁ E₂ (symArr h)) :=
  hF.comp (contDiff_pi.mpr fun i => edgeCount_contDiff D N Ac η (E₁ i) (E₂ i) hη)

private lemma CF_fderiv_Phi (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (h u : Idx D N → Idx D N → ℂ) :
    fderiv ℝ (CF_Phi D N Ac η F E₁ E₂) h u =
      ((fderiv ℝ (fun h => edgeFn D N Ac η F E₁ E₂ (symArr h)) h u : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (CF_Phi D N Ac η F E₁ E₂)
      (Complex.ofRealCLM.comp (fderiv ℝ (fun h => edgeFn D N Ac η F E₁ E₂ (symArr h)) h)) h :=
    Complex.ofRealCLM.hasFDerivAt.comp h
      ((CF_G_contDiff D N Ac η F E₁ E₂ hη hF).differentiable (by simp) h).hasFDerivAt
  rw [h1.fderiv]
  rfl

private lemma CF_fderiv_Fc (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (y u : Fin 1 → Coords (D * N)) :
    fderiv ℝ (CF_Fc D N Ac η F E₁ E₂) y u =
      fderiv ℝ (CF_Phi D N Ac η F E₁ E₂) (CF_arr D N y) (CF_arr D N u) := by
  have e : CF_Fc D N Ac η F E₁ E₂ = fun y => CF_Phi D N Ac η F E₁ E₂ (0 + CF_arr D N y) := by
    funext y; simp [CF_Fc_eq_Phi]
  rw [e, CF_fderiv_affine _ ((CF_Phi_contDiff D N Ac η F E₁ E₂ hη hF).of_le (by simp))]
  simp

/-- The integrand `-½ DF(y)·y + ½ gLap F(y)` of the display before (4.9) [eq:prodnGt] as the entry
sums of `entryDrift` and `entryGen`. -/
private lemma CF_xi_eq (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (y : Fin 1 → Coords (D * N)) :
    -(1 / 2 : ℂ) * fderiv ℝ (CF_Fc D N Ac η F E₁ E₂) y y +
        (1 / 2 : ℂ) * gLap (CF_Fc D N Ac η F E₁ E₂) y =
      -(1 / 2 : ℂ) * (∑ i, ∑ j, driftWt i j * CF_thDr D N Ac η F E₁ E₂ i j (CF_arr D N y)) +
        (1 / 2 : ℂ) * ((D * N : ℕ) : ℂ)⁻¹ *
          ∑ i, ∑ j, genWt i j * CF_thGen D N Ac η F E₁ E₂ i j (CF_arr D N y) := by
  have hG := CF_G_contDiff D N Ac η F E₁ E₂ hη hF
  have h1 := fderiv_symArr_entry D N (edgeFn D N Ac η F E₁ E₂) (hG.of_le (by simp))
    (CF_arr D N y) (CF_arr D N y) (CF_arr_herm D N y) (CF_arr_herm D N y)
  have h2 := gLap_gueIdx D N (edgeFn D N Ac η F E₁ E₂) (hG.of_le (by simp)) y
  rw [CF_fderiv_Fc D N Ac η F E₁ E₂ hη hF, CF_fderiv_Phi D N Ac η F E₁ E₂ hη hF, h1]
  have e2 : gLap (CF_Fc D N Ac η F E₁ E₂) y = gLap (fun y : Fin 1 → Coords (D * N) =>
      ((edgeFn D N Ac η F E₁ E₂ (Matrix.of.symm (gueIdx D N (y 0))) : ℝ) : ℂ)) y := rfl
  rw [e2, h2]
  simp only [CF_thDr, CF_thGen, mul_assoc]
  rfl

end Main3

section Main4

variable (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (Ac : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) {n : ℕ}
  (F : (Fin n → ℝ) → ℝ) (E₁ E₂ : Fin n → ℝ)

/-- A weighted double sum of integrals. -/
private lemma CF_integral_double_sum {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : Idx D N → Idx D N → α → ℂ) (w : Idx D N → Idx D N → ℂ)
    (hf : ∀ i j, Integrable (f i j) μ) :
    ∫ q, ∑ i, ∑ j, w i j * f i j q ∂μ = ∑ i, ∑ j, w i j * ∫ q, f i j q ∂μ := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hf i j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hf i j).const_mul _)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- The derivative of `t ↦ E_{H_t} F(A)` at `t > 0` in the form of the display before (4.9)
[eq:prodnGt]: the iterated integral of `-½ DF(H_t)·H_t + ½ gLap F(H_t)` is `entryDeriv`. -/
private lemma CF_deriv_value (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (t : ℝ) (ht : 0 < t) :
    ∫ w, (∫ x, (-(1 / 2 : ℂ) * fderiv ℝ (CF_Fc D N Ac η F E₁ E₂)
          (ouPoint 1 (D * N) t (fun _ => blockEmb D N w) x)
          (ouPoint 1 (D * N) t (fun _ => blockEmb D N w) x) +
        (1 / 2 : ℂ) * gLap (CF_Fc D N Ac η F E₁ E₂)
          (ouPoint 1 (D * N) t (fun _ => blockEmb D N w) x)) ∂(gueBlocks 1 (D * N)))
        ∂(blockLaw D N L) =
      entryDeriv (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t) := by
  set μΩ : Measure (CF_Om D N) := (blockLaw D N L).prod (gueBlocks 1 (D * N)) with hμΩ
  set Ξ : CF_Om D N → ℂ := fun q =>
    -(1 / 2 : ℂ) * fderiv ℝ (CF_Fc D N Ac η F E₁ E₂)
      (ouPoint 1 (D * N) t (fun _ => blockEmb D N q.1) q.2)
      (ouPoint 1 (D * N) t (fun _ => blockEmb D N q.1) q.2) +
    (1 / 2 : ℂ) * gLap (CF_Fc D N Ac η F E₁ E₂)
      (ouPoint 1 (D * N) t (fun _ => blockEmb D N q.1) q.2) with hΞ
  have hΞe : ∀ q, Ξ q =
      -(1 / 2 : ℂ) * (∑ i, ∑ j, driftWt i j * CF_thDr D N Ac η F E₁ E₂ i j (CF_Psi D N t q)) +
        (1 / 2 : ℂ) * ((D * N : ℕ) : ℂ)⁻¹ *
          ∑ i, ∑ j, genWt i j * CF_thGen D N Ac η F E₁ E₂ i j (CF_Psi D N t q) :=
    fun q => CF_xi_eq D N Ac η F E₁ E₂ hη hF _
  have hΨm : AEMeasurable (CF_Psi D N t) μΩ := (CF_continuous_Psi D N t).measurable.aemeasurable
  have hmeasDr : ∀ i j, AEStronglyMeasurable (CF_thDr D N Ac η F E₁ E₂ i j)
      (ouMatLaw D N L t) := fun i j =>
    (CF_continuous_thDr' D N Ac η F E₁ E₂ hη hF i j).aestronglyMeasurable.congr
      ((CF_herm_ae D N L t).mono fun h hh => (CF_thDr_eq D N Ac η F E₁ E₂ hη hF h hh i j).symm)
  have hmeasGen : ∀ i j, AEStronglyMeasurable (CF_thGen D N Ac η F E₁ E₂ i j)
      (ouMatLaw D N L t) := fun i j =>
    (CF_continuous_thGen' D N Ac η F E₁ E₂ hη hF i j).aestronglyMeasurable.congr
      ((CF_herm_ae D N L t).mono fun h hh => (CF_thGen_eq D N Ac η F E₁ E₂ hη hF h hh i j).symm)
  have hintDr : ∀ i j, Integrable (fun q => CF_thDr D N Ac η F E₁ E₂ i j (CF_Psi D N t q)) μΩ :=
    fun i j => by
      have := CF_thDr_int D N L Ac η F E₁ E₂ hη hF t ht.le i j
      rw [CF_ouMatLaw_eq] at this hmeasDr
      exact (integrable_map_measure (hmeasDr i j) hΨm).mp this
  have hintGen : ∀ i j, Integrable (fun q => CF_thGen D N Ac η F E₁ E₂ i j (CF_Psi D N t q)) μΩ :=
    fun i j => by
      have := CF_thGen_int D N L Ac η F E₁ E₂ hη hF t i j
      rw [CF_ouMatLaw_eq] at this hmeasGen
      exact (integrable_map_measure (hmeasGen i j) hΨm).mp this
  have hΞint : Integrable Ξ μΩ := by
    have : Ξ = fun q =>
      -(1 / 2 : ℂ) * (∑ i, ∑ j, driftWt i j * CF_thDr D N Ac η F E₁ E₂ i j (CF_Psi D N t q)) +
        (1 / 2 : ℂ) * ((D * N : ℕ) : ℂ)⁻¹ *
          ∑ i, ∑ j, genWt i j * CF_thGen D N Ac η F E₁ E₂ i j (CF_Psi D N t q) := funext hΞe
    rw [this]
    refine (((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hintDr i j).const_mul _)).const_mul _).add
      (((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hintGen i j).const_mul _)).const_mul _)
  have hiter : ∫ w, (∫ x, Ξ (w, x) ∂(gueBlocks 1 (D * N))) ∂(blockLaw D N L) = ∫ q, Ξ q ∂μΩ :=
    (integral_prod _ hΞint).symm
  have hstep : ∀ w, ∫ x, (-(1 / 2 : ℂ) * fderiv ℝ (CF_Fc D N Ac η F E₁ E₂)
          (ouPoint 1 (D * N) t (fun _ => blockEmb D N w) x)
          (ouPoint 1 (D * N) t (fun _ => blockEmb D N w) x) +
        (1 / 2 : ℂ) * gLap (CF_Fc D N Ac η F E₁ E₂)
          (ouPoint 1 (D * N) t (fun _ => blockEmb D N w) x)) ∂(gueBlocks 1 (D * N)) =
      ∫ x, Ξ (w, x) ∂(gueBlocks 1 (D * N)) := fun w => rfl
  simp_rw [hstep]
  rw [hiter]
  simp_rw [hΞe]
  rw [integral_add (((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hintDr i j).const_mul _)).const_mul _)
      (((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hintGen i j).const_mul _)).const_mul _), integral_const_mul, integral_const_mul,
    CF_integral_double_sum D N μΩ _ _ hintDr, CF_integral_double_sum D N μΩ _ _ hintGen]
  have hDr : (∑ i, ∑ j, driftWt i j * ∫ q, CF_thDr D N Ac η F E₁ E₂ i j (CF_Psi D N t q) ∂μΩ) =
      entryDrift (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t) := by
    unfold entryDrift
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← CF_integral_theta D N L t _ (hmeasDr i j)]
    rfl
  have hGen : (∑ i, ∑ j, genWt i j * ∫ q, CF_thGen D N Ac η F E₁ E₂ i j (CF_Psi D N t q) ∂μΩ) =
      entryGen (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t) := by
    unfold entryGen
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← CF_integral_theta D N L t _ (hmeasGen i j)]
    rfl
  rw [hDr, hGen]
  rfl

end Main4

/-! ### The derivative of `t ↦ E_{H_t} F(A)` -/

section Deriv

variable (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (Ac : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) {n : ℕ}
  (F : (Fin n → ℝ) → ℝ) (E₁ E₂ : Fin n → ℝ)

/-- The coordinates `blockEmb D N w` of one block of size `DN`. -/
private def CF_c (D N : ℕ) (w : Fin D → Coords N) : Fin 1 → Coords (D * N) :=
  fun _ => blockEmb D N w

private lemma CF_continuous_c (D N : ℕ) : Continuous (CF_c D N) :=
  continuous_pi fun _ => CF_continuous_blockEmb D N

/-- The point `ouPoint` is jointly continuous in `(w, x)`. -/
private lemma CF_continuous_ouPoint2 (D N : ℕ) (s : ℝ) :
    Continuous fun p : CF_Om D N => ouPoint 1 (D * N) s (CF_c D N p.1) p.2 := by
  unfold ouPoint
  have h1 : Continuous fun p : CF_Om D N => CF_c D N p.1 :=
    (CF_continuous_c D N).comp continuous_fst
  exact (h1.const_smul (Real.exp (-s / 2))).add
    ((continuous_snd (X := Fin D → Coords N) (Y := Fin 1 → Coords (D * N))).const_smul
      (Real.sqrt (1 - Real.exp (-s))))

/-- The array of the coordinates `blockEmb D N w` is `H(w)`. -/
private lemma CF_arr_c (D N : ℕ) (w : Fin D → Coords N) :
    CF_arr D N (CF_c D N w) = Matrix.of.symm (blockH D N w) := by
  rw [CF_arr_apply]
  exact congrArg Matrix.of.symm (wig_blockEmb D N w)

/-- The entries of `H(w)` are integrable under `blockLaw`. -/
private lemma CF_blockH_int (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (p q : Idx D N) :
    Integrable (fun w => ‖CF_arr D N (CF_c D N w) p q‖) (blockLaw D N L) := by
  have h1 := (llClass_blockH D N C L).integrable 1 p q
  have hc : Continuous fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) := by
    have : (fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w)) =
        fun w => CF_arr D N (CF_c D N w) := funext fun w => (CF_arr_c D N w).symm
    rw [this]
    exact (CF_arr D N).continuous.comp (CF_continuous_c D N)
  have hm : AEStronglyMeasurable (fun h : Idx D N → Idx D N → ℂ => ‖h p q‖ ^ 1)
      ((blockLaw D N L).map fun w => Matrix.of.symm (blockH D N w)) :=
    ((continuous_norm.comp ((continuous_apply q).comp (continuous_apply p))).pow 1
      ).aestronglyMeasurable
  have h2 := (integrable_map_measure hm hc.measurable.aemeasurable).mp h1
  refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Function.comp, pow_one, CF_arr_c]

/-- The derivative of `t ↦ E_{H_t} F(A_t)` at `t > 0`, as the derivative of the iterated integral
(`hasDerivAt_ouExpect`, differentiated under `∫ w`). -/
private lemma CF_hasDerivAt (hη : 0 < η) (hF : ContDiff ℝ ∞ F) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => ∫ h, ((edgeFn D N Ac η F E₁ E₂ h : ℝ) : ℂ) ∂(ouMatLaw D N L s))
      (entryDeriv (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t)) t := by
  obtain ⟨B, hB0, hB⟩ := CF_Fc_bound D N Ac η F E₁ E₂ hη hF
  obtain ⟨K, hK0, hK⟩ := CF_Fc_fderiv_le D N Ac η F E₁ E₂ hη hF
  set Fc := CF_Fc D N Ac η F E₁ E₂ with hFc
  have hFc2 : ContDiff ℝ 2 Fc := (CF_Fc_contDiff D N Ac η F E₁ E₂ hη hF).of_le (by simp)
  obtain ⟨h0, h1, h2⟩ := CF_bnd_of_iter Fc B hB
  have hcont : Continuous Fc := hFc2.continuous
  have hDc : Continuous (fderiv ℝ Fc) := (hFc2.fderiv_right (m := 1) (by norm_num)).continuous
  have hgL := CF_continuous_gLap Fc hFc2
  set Fw : ℝ → (Fin D → Coords N) → ℂ := fun s w =>
    ∫ x, Fc (ouPoint 1 (D * N) s (CF_c D N w) x) ∂(gueBlocks 1 (D * N)) with hFw
  set F'w : ℝ → (Fin D → Coords N) → ℂ := fun s w =>
    ∫ x, (-(1 / 2 : ℂ) * (Real.exp (-s / 2) : ℂ) *
        fderiv ℝ Fc (ouPoint 1 (D * N) s (CF_c D N w) x) (CF_c D N w) +
      (1 / 2 : ℂ) * (Real.exp (-s) : ℂ) * gLap Fc (ouPoint 1 (D * N) s (CF_c D N w) x))
      ∂(gueBlocks 1 (D * N)) with hF'w
  have hFw_meas : ∀ s, StronglyMeasurable (Fw s) := fun s => by
    have hc : Continuous (Function.uncurry fun (w : Fin D → Coords N)
        (x : Fin 1 → Coords (D * N)) => Fc (ouPoint 1 (D * N) s (CF_c D N w) x)) :=
      hcont.comp (CF_continuous_ouPoint2 D N s)
    exact hc.stronglyMeasurable.integral_prod_right
  have hF'w_meas : ∀ s, StronglyMeasurable (F'w s) := fun s => by
    have hc : Continuous (Function.uncurry fun (w : Fin D → Coords N)
        (x : Fin 1 → Coords (D * N)) =>
        -(1 / 2 : ℂ) * (Real.exp (-s / 2) : ℂ) *
          fderiv ℝ Fc (ouPoint 1 (D * N) s (CF_c D N w) x) (CF_c D N w) +
        (1 / 2 : ℂ) * (Real.exp (-s) : ℂ) * gLap Fc (ouPoint 1 (D * N) s (CF_c D N w) x)) := by
      have hP := CF_continuous_ouPoint2 D N s
      have hcw : Continuous fun p : CF_Om D N => CF_c D N p.1 :=
        (CF_continuous_c D N).comp continuous_fst
      exact (continuous_const.mul ((hDc.comp hP).clm_apply hcw)).add
        (continuous_const.mul (hgL.comp hP))
    exact hc.stronglyMeasurable.integral_prod_right
  -- the bound
  set bound : (Fin D → Coords N) → ℝ := fun w =>
    (1 / 2 : ℝ) * K * CF_S (CF_arr D N (CF_c D N w)) +
      (1 / 2 : ℝ) * (((D * N : ℕ) : ℝ) + ((D * N : ℕ) : ℝ) ^ 2) * B with hbound
  have hbound_int : Integrable bound (blockLaw D N L) := by
    refine Integrable.add ?_ (integrable_const _)
    exact (integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
      CF_blockH_int D N L p q).const_mul _
  have hFint : Integrable (Fw t) (blockLaw D N L) := by
    refine Integrable.of_bound (hFw_meas t).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun w => ?_)
    have := norm_integral_le_of_norm_le_const (μ := gueBlocks 1 (D * N))
      (f := fun x => Fc (ouPoint 1 (D * N) t (CF_c D N w) x)) (C := B)
      (Filter.Eventually.of_forall fun x => h0 _)
    rw [probReal_univ, mul_one] at this
    exact this
  have hbd : ∀ w, ∀ s ∈ Set.Ioo (t / 2) (3 * t / 2), ‖F'w s w‖ ≤ bound w := by
    intro w s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have he1 : Real.exp (-s / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have he2 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hpt : ∀ x, ‖-(1 / 2 : ℂ) * (Real.exp (-s / 2) : ℂ) *
          fderiv ℝ Fc (ouPoint 1 (D * N) s (CF_c D N w) x) (CF_c D N w) +
        (1 / 2 : ℂ) * (Real.exp (-s) : ℂ) * gLap Fc (ouPoint 1 (D * N) s (CF_c D N w) x)‖ ≤
        bound w := by
      intro x
      have hD := hK (ouPoint 1 (D * N) s (CF_c D N w) x) (CF_c D N w)
      have hG := CF_gLap_le Fc hFc2 B h2 (ouPoint 1 (D * N) s (CF_c D N w) x)
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, norm_mul]
      have n1 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      have n2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      have n3 : ‖((Real.exp (-s / 2) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact he1
      have n4 : ‖((Real.exp (-s) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact he2
      rw [n1, n2]
      have hS := CF_S_nonneg (CF_arr D N (CF_c D N w))
      have a1 : 1 / 2 * ‖((Real.exp (-s / 2) : ℝ) : ℂ)‖ *
          ‖fderiv ℝ Fc (ouPoint 1 (D * N) s (CF_c D N w) x) (CF_c D N w)‖ ≤
          1 / 2 * K * CF_S (CF_arr D N (CF_c D N w)) := by
        calc _ ≤ 1 / 2 * 1 * (K * CF_S (CF_arr D N (CF_c D N w))) := by
              gcongr
          _ = _ := by ring
      have a2 : 1 / 2 * ‖((Real.exp (-s) : ℝ) : ℂ)‖ *
          ‖gLap Fc (ouPoint 1 (D * N) s (CF_c D N w) x)‖ ≤
          1 / 2 * (((D * N : ℕ) : ℝ) + ((D * N : ℕ) : ℝ) ^ 2) * B := by
        calc _ ≤ 1 / 2 * 1 * ((((D * N : ℕ) : ℝ) + ((D * N : ℕ) : ℝ) ^ 2) * B) := by
              gcongr
          _ = _ := by ring
      exact (add_le_add a1 a2)
    have := norm_integral_le_of_norm_le_const (μ := gueBlocks 1 (D * N))
      (f := fun x => -(1 / 2 : ℂ) * (Real.exp (-s / 2) : ℂ) *
          fderiv ℝ Fc (ouPoint 1 (D * N) s (CF_c D N w) x) (CF_c D N w) +
        (1 / 2 : ℂ) * (Real.exp (-s) : ℂ) * gLap Fc (ouPoint 1 (D * N) s (CF_c D N w) x))
      (C := bound w) (Filter.Eventually.of_forall hpt)
    rw [probReal_univ, mul_one] at this
    exact this
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := blockLaw D N L)
    (s := Set.Ioo (t / 2) (3 * t / 2)) (F := Fw) (F' := F'w) (x₀ := t) (bound := bound)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun s => (hFw_meas s).aestronglyMeasurable) hFint
    (hF'w_meas t).aestronglyMeasurable
    (Filter.Eventually.of_forall hbd) hbound_int
    (Filter.Eventually.of_forall fun w s hs =>
      hasDerivAt_ouExpect 1 (D * N) Fc B hFc2 (fun j hj v => hB v j hj) (CF_c D N w) s
        (by linarith [hs.1]))
  obtain ⟨-, hD⟩ := hmain
  have e1 : (fun s => ∫ h, ((edgeFn D N Ac η F E₁ E₂ h : ℝ) : ℂ) ∂(ouMatLaw D N L s)) =
      fun s => ∫ w, Fw s w ∂(blockLaw D N L) :=
    funext fun s => CF_expect_eq D N L Ac η F E₁ E₂ hη hF s
  have e2 : ∫ w, F'w t w ∂(blockLaw D N L) =
      entryDeriv (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t) := by
    rw [← CF_deriv_value D N L Ac η F E₁ E₂ hη hF t ht]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    exact CF_deriv_formula Fc hFc2 B (fun v j hj => hB v j hj) (CF_c D N w) t ht
  rw [e1, ← e2]
  exact hD

end Deriv

/-! ### The fundamental theorem of calculus on `[0, T]` -/

section FTC

variable (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (Ac : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) {n : ℕ}
  (F : (Fin n → ℝ) → ℝ) (E₁ E₂ : Fin n → ℝ)

/-- `s ↦ E_{H_s} F(A)` is continuous on all of `ℝ`. -/
private lemma CF_continuous_expect (hη : 0 < η) (hF : ContDiff ℝ ∞ F) :
    Continuous fun s : ℝ => ∫ h, ((edgeFn D N Ac η F E₁ E₂ h : ℝ) : ℂ) ∂(ouMatLaw D N L s) := by
  obtain ⟨B, hB0, hB⟩ := CF_Phi_Psi_le D N Ac η F E₁ E₂ hη hF
  have hcont : Continuous (CF_Phi D N Ac η F E₁ E₂) :=
    (CF_Phi_contDiff D N Ac η F E₁ E₂ hη hF).continuous
  have e : (fun s : ℝ => ∫ h, ((edgeFn D N Ac η F E₁ E₂ h : ℝ) : ℂ) ∂(ouMatLaw D N L s)) =
      fun s => ∫ q, CF_Phi D N Ac η F E₁ E₂ (CF_Psi D N s q)
        ∂((blockLaw D N L).prod (gueBlocks 1 (D * N))) :=
    funext fun s => CF_expect_Om D N L Ac η F E₁ E₂ hη hF s
  rw [e]
  refine continuous_of_dominated (bound := fun _ => B) (fun s => ?_)
    (fun s => Filter.Eventually.of_forall fun q => hB s q) (integrable_const B)
    (Filter.Eventually.of_forall fun q => ?_)
  · exact (hcont.comp (CF_continuous_Psi D N s)).aestronglyMeasurable
  · refine hcont.comp ?_
    unfold CF_Psi ouPoint
    refine (CF_arr D N).continuous.comp ?_
    exact ((Real.continuous_exp.comp (by fun_prop)).smul continuous_const).add
      ((Real.continuous_sqrt.comp (by fun_prop)).smul continuous_const)

/-- `entryDeriv` is bounded uniformly in `t ≥ 0`. -/
private lemma CF_entryDeriv_le (hη : 0 < η) (hF : ContDiff ℝ ∞ F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t →
      ‖entryDeriv (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t)‖ ≤ M := by
  obtain ⟨W₁, hW₁, hW₁'⟩ := CF_edgeFn_wirt_bound D N Ac η F E₁ E₂ 0 1 (by norm_num) (by norm_num)
    hη hF
  obtain ⟨W₂, hW₂, hW₂'⟩ := CF_edgeFn_wirt_bound D N Ac η F E₁ E₂ 1 1 (by norm_num) (by norm_num)
    hη hF
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  set M₁ : ℝ := W₁ * (C' 1 * (N : ℝ) ^ (-(((1 : ℕ) : ℝ) / 2))) with hM₁
  set M : ℝ := (1 / 2) * (((D * N : ℕ) : ℝ) ^ 2 * (2 * M₁)) +
    (1 / 2) * (((D * N : ℕ) : ℝ) ^ 2 * (4 * W₂)) with hM
  have key : ∀ t : ℝ, 0 ≤ t →
      ‖entryDeriv (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t)‖ ≤ M := by
    intro t ht
    have := CF_isProb D N L t
    have hdr : ∀ i j : Idx D N, ‖∫ h, CF_thDr D N Ac η F E₁ E₂ i j h ∂(ouMatLaw D N L t)‖ ≤ M₁ := by
      intro i j
      have hI := (hC' N L t ht).integrable 1 i j
      have hmo := (hC' N L t ht).moments 1 i j
      calc ‖∫ h, CF_thDr D N Ac η F E₁ E₂ i j h ∂(ouMatLaw D N L t)‖
          ≤ ∫ h, W₁ * ‖h i j‖ ^ 1 ∂(ouMatLaw D N L t) := by
            refine norm_integral_le_of_norm_le (hI.const_mul W₁) ?_
            filter_upwards [CF_herm_ae D N L t] with h hh
            unfold CF_thDr
            rw [norm_mul, Complex.norm_conj, pow_one]
            calc ‖h i j‖ * ‖wirt 0 1 (fun w =>
                  ((edgeFn D N Ac η F E₁ E₂ (setEntry h i j w) : ℝ) : ℂ)) (h i j)‖
                ≤ ‖h i j‖ * W₁ := mul_le_mul_of_nonneg_left (hW₁' h hh i j _) (norm_nonneg _)
              _ = W₁ * ‖h i j‖ := mul_comm _ _
        _ = W₁ * ∫ h, ‖h i j‖ ^ 1 ∂(ouMatLaw D N L t) := integral_const_mul _ _
        _ ≤ W₁ * (C' 1 * (N : ℝ) ^ (-(((1 : ℕ) : ℝ) / 2))) :=
            mul_le_mul_of_nonneg_left hmo hW₁
    have hgen : ∀ i j : Idx D N,
        ‖∫ h, CF_thGen D N Ac η F E₁ E₂ i j h ∂(ouMatLaw D N L t)‖ ≤ W₂ := by
      intro i j
      have := norm_integral_le_of_norm_le_const (μ := ouMatLaw D N L t)
        (f := CF_thGen D N Ac η F E₁ E₂ i j) (C := W₂) (by
          filter_upwards [CF_herm_ae D N L t] with h hh
          exact hW₂' h hh i j _)
      rwa [probReal_univ, mul_one] at this
    have hcardIdx : (Finset.univ : Finset (Idx D N)).card = D * N := by simp
    have hdw : ∀ i j : Idx D N, ‖driftWt i j‖ ≤ 2 := fun i j => by
      unfold driftWt; split_ifs <;> simp
    have hgw : ∀ i j : Idx D N, ‖genWt i j‖ ≤ 4 := fun i j => by
      unfold genWt; split_ifs <;> simp
    have hsum : ∀ (c : ℝ), (∑ _i : Idx D N, ∑ _j : Idx D N, c) = ((D * N : ℕ) : ℝ) ^ 2 * c := by
      intro c
      rw [Finset.sum_const, Finset.sum_const, hcardIdx, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    have h1 : ‖entryDrift (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t)‖ ≤
        ((D * N : ℕ) : ℝ) ^ 2 * (2 * M₁) := by
      unfold entryDrift
      rw [← hsum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul (hdw i j) (hdr i j) (norm_nonneg _) (by norm_num)
    have h2 : ‖entryGen (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t)‖ ≤
        ((D * N : ℕ) : ℝ) ^ 2 * (4 * W₂) := by
      unfold entryGen
      rw [← hsum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul (hgw i j) (hgen i j) (norm_nonneg _) (by norm_num)
    have hinv : ‖(((D * N : ℕ) : ℂ))⁻¹‖ ≤ 1 := by
      by_cases h0 : D * N = 0
      · simp [h0]
      · rw [norm_inv, Complex.norm_natCast]
        exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0)
    unfold entryDeriv
    calc ‖-(1 / 2 : ℂ) * entryDrift (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t) +
          (1 / 2 : ℂ) * (((D * N : ℕ) : ℂ))⁻¹ *
            entryGen (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t)‖
        ≤ (1 / 2) * ‖entryDrift (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t)‖ +
          (1 / 2) * (‖(((D * N : ℕ) : ℂ))⁻¹‖ *
            ‖entryGen (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t)‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_mul]
          have n1 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
          have n2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
          rw [n1, n2]
          exact le_of_eq (by ring)
      _ ≤ M := by
          have hg0 : 0 ≤ ‖entryGen (edgeFn D N Ac η F E₁ E₂) (ouMatLaw D N L t)‖ := norm_nonneg _
          calc _ ≤ (1 / 2) * (((D * N : ℕ) : ℝ) ^ 2 * (2 * M₁)) +
                (1 / 2) * (1 * (((D * N : ℕ) : ℝ) ^ 2 * (4 * W₂))) := by
                gcongr
            _ = M := by rw [hM]; ring
  exact ⟨M, (norm_nonneg _).trans (key 0 le_rfl), key⟩

end FTC

/-- The fundamental theorem of calculus on `[0, T]` for `t ↦ E_{H_t} F(A_t)` (proof of
Lemma 4.3 [rescomY]). -/
theorem edgeExpect_ftc (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C)
    (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η) (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (E₁ E₂ : Fin n → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ h, (edgeFn D N A η F E₁ E₂ h : ℂ) ∂(ouMatLaw D N L T)) -
        (∫ h, (edgeFn D N A η F E₁ E₂ h : ℂ) ∂(ouMatLaw D N L 0)) =
      ∫ t in (0 : ℝ)..T, entryDeriv (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t)  := by
  rcases hT.eq_or_lt with rfl | hTpos
  · simp
  have hcont := CF_continuous_expect D N L A η F E₁ E₂ hη hF
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt
      (fun s : ℝ => ∫ h, ((edgeFn D N A η F E₁ E₂ h : ℝ) : ℂ) ∂(ouMatLaw D N L s))
      (entryDeriv (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t)) t :=
    fun t ht => CF_hasDerivAt D N L A η F E₁ E₂ hη hF t ht
  obtain ⟨M, hM0, hM⟩ := CF_entryDeriv_le D N L A η F E₁ E₂ hη hF
  have hint : IntervalIntegrable
      (fun t => entryDeriv (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t))
      MeasureTheory.volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTpos.le]
    refine Integrable.of_bound (μ := MeasureTheory.volume.restrict (Set.Ioc 0 T)) ?_ M ?_
    · have e : (fun t => entryDeriv (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t)) =ᵐ[
          MeasureTheory.volume.restrict (Set.Ioc 0 T)] deriv (fun s : ℝ =>
            ∫ h, ((edgeFn D N A η F E₁ E₂ h : ℝ) : ℂ) ∂(ouMatLaw D N L s)) := by
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall fun t ht => (hd t ht.1).deriv.symm
      exact (Measurable.aestronglyMeasurable (μ := MeasureTheory.volume.restrict (Set.Ioc 0 T))
        (measurable_deriv _)).congr e.symm
    · rw [ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun t ht => hM t ht.1.le
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hTpos.le hcont.continuousOn
    (fun t ht => hd t ht.1) hint).symm

end RBMTransitionEdge

end
