module

public import RBMTransitionEdge.Model.Basic

@[expose] public section

/-!
# Gaussian facts: GUE coordinates, block embedding, the law (4.3)

Linearity of `wig`; invariance of the GUE under `W ↦ −W` and under `aW₁ + bW₂` with `a² + b² = 1`; `D` independent GUE
blocks; the embedding of the block coordinates into size `DN`; and the one-time law (4.3) [eq:eq_in_law_H] of `H_t` in
(4.1) [defVt].
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped NNReal ENNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The GUE law `gueLaw n` is a probability measure (instance form of `gueLaw_isProbabilityMeasure`). -/
instance gueLaw_instIsProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (gueLaw n) :=
  gueLaw_isProbabilityMeasure n

/-- The block law `blockLaw D N L` of Assumption 1 [main_assm] is a probability measure (instance form
of `blockLaw_isProbabilityMeasure`). -/
instance blockLaw_instIsProbabilityMeasure (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    IsProbabilityMeasure (blockLaw D N L) :=
  blockLaw_isProbabilityMeasure D N L

/-- `wig` is additive in the coordinates. -/
theorem wig_add (n : ℕ) (v w : Coords n) : wig n (v + w) = wig n v + wig n w := by
  ext i j
  simp only [wig, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> simp [mul_add]

/-- `wig` is real-homogeneous in the coordinates. -/
theorem wig_smul (n : ℕ) (c : ℝ) (w : Coords n) : wig n (c • w) = (c : ℂ) • wig n w := by
  ext i j
  simp only [wig, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · push_cast; ring
  · rw [Complex.real_smul]
    ring
  · rw [Complex.real_smul, star_mul']; simp; ring

/-- The rearrangement `((A × B) × (C × D)) → ((A × C) × (B × D))` preserves product measures. -/
private theorem gaussianNeg_prodRearr_mp {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 : MeasurePreserving (Prod.map (id : A → A)
      (fun q : B × (C × D) => ((q.1, q.2.1), q.2.2)))
      (μa.prod (μb.prod (μc.prod μd))) (μa.prod ((μb.prod μc).prod μd)) :=
    (MeasurePreserving.id μa).prod
      (MeasurePreserving.symm _ (measurePreserving_prodAssoc μb μc μd))
  have h3 : MeasurePreserving (Prod.map (id : A → A)
      (Prod.map (Prod.swap : B × C → C × B) (id : D → D)))
      (μa.prod ((μb.prod μc).prod μd)) (μa.prod ((μc.prod μb).prod μd)) :=
    (MeasurePreserving.id μa).prod
      ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h4 : MeasurePreserving (Prod.map (id : A → A)
      (fun q : (C × B) × D => (q.1.1, (q.1.2, q.2))))
      (μa.prod ((μc.prod μb).prod μd)) (μa.prod (μc.prod (μb.prod μd))) :=
    (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 : MeasurePreserving (fun q : A × (C × (B × D)) => ((q.1, q.2.1), q.2.2))
      (μa.prod (μc.prod (μb.prod μd))) ((μa.prod μc).prod (μb.prod μd)) :=
    MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μc (μb.prod μd))
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))


/-- If `g` maps `μ ⊗ μ` to `μ`, then the coordinatewise `g` maps `(⊗ᵢ μ) ⊗ (⊗ᵢ μ)` to `⊗ᵢ μ`. -/
private theorem gaussianNeg_piPair_map {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (g : E × E → E) (hg : Measurable g)
    (h : (μ.prod μ).map g = μ) :
    ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => μ)).map
      (fun p i => g (p.1 i, p.2 i)) = Measure.pi fun _ : ι => μ := by
  have hmp := measurePreserving_arrowProdEquivProdArrow E E ι (fun _ => μ) (fun _ => μ)
  have e := (MeasurePreserving.symm _ hmp).map_eq
  have hf : (fun p : (ι → E) × (ι → E) => fun i => g (p.1 i, p.2 i)) =
      (fun x : ι → E × E => fun i => g (x i)) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow E E ι).symm := by
    funext p i; rfl
  rw [hf, ← Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _), e,
    Measure.pi_map_pi (fun _ => hg.aemeasurable)]
  simp [h]

/-- If `gⱼ` maps `μⱼ ⊗ μⱼ` to `μⱼ` (`j = 1, 2`), then `(g₁, g₂)` maps `(μ₁ ⊗ μ₂) ⊗ (μ₁ ⊗ μ₂)`
to `μ₁ ⊗ μ₂`. -/
private theorem gaussianNeg_prodPair_map {E1 E2 : Type*} [MeasurableSpace E1] [MeasurableSpace E2]
    (μ1 : Measure E1) (μ2 : Measure E2) [IsProbabilityMeasure μ1] [IsProbabilityMeasure μ2]
    (g1 : E1 × E1 → E1) (g2 : E2 × E2 → E2) (h1 : Measurable g1) (h2 : Measurable g2)
    (e1 : (μ1.prod μ1).map g1 = μ1) (e2 : (μ2.prod μ2).map g2 = μ2) :
    ((μ1.prod μ2).prod (μ1.prod μ2)).map
      (fun p => (g1 (p.1.1, p.2.1), g2 (p.1.2, p.2.2))) = μ1.prod μ2 := by
  have hmp := gaussianNeg_prodRearr_mp μ1 μ2 μ1 μ2
  have hf : (fun p : (E1 × E2) × (E1 × E2) => (g1 (p.1.1, p.2.1), g2 (p.1.2, p.2.2))) =
      Prod.map g1 g2 ∘ (fun p : (E1 × E2) × (E1 × E2) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) := rfl
  rw [hf, ← Measure.map_map (h1.prodMap h2) hmp.measurable, hmp.map_eq,
    ← Measure.map_prod_map _ _ h1 h2, e1, e2]

/-- For `a² + b² = 1`, `a X + b Y` is `N(0, v)` for independent `N(0, v)` variables `X`, `Y`. -/
private theorem gaussianNeg_real_comb (v : ℝ≥0) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)).map (fun p => a * p.1 + b * p.2) =
      gaussianReal 0 v := by
  set P := (gaussianReal 0 v).prod (gaussianReal 0 v) with hP
  have hX : HasLaw (fun p : ℝ × ℝ => p.1) (gaussianReal 0 v) P :=
    ⟨measurable_fst.aemeasurable, by simp [P, Measure.map_fst_prod]⟩
  have hY : HasLaw (fun p : ℝ × ℝ => p.2) (gaussianReal 0 v) P :=
    ⟨measurable_snd.aemeasurable, by simp [P, Measure.map_snd_prod]⟩
  have hX' := gaussianReal_const_mul hX a
  have hY' := gaussianReal_const_mul hY b
  have hind : IndepFun (fun p : ℝ × ℝ => a * p.1) (fun p : ℝ × ℝ => b * p.2) P :=
    indepFun_prod (X := fun x : ℝ => a * x) (Y := fun y : ℝ => b * y) (by fun_prop) (by fun_prop)
  have := gaussianReal_add_gaussianReal_of_indepFun hind hX' hY'
  have hv : (NNReal.mk (a ^ 2) (sq_nonneg _) * v + NNReal.mk (b ^ 2) (sq_nonneg _) * v) = v := by
    rw [← add_mul]
    have : NNReal.mk (a ^ 2) (sq_nonneg _) + NNReal.mk (b ^ 2) (sq_nonneg _) = 1 := by
      ext; simpa using hab
    rw [this, one_mul]
  rw [hv, mul_zero, mul_zero, add_zero] at this
  exact this


/-- The law `cGauss` as the image of `N(0,1/2) ⊗ N(0,1/2)` under `(x, y) ↦ x + y i`. -/
private theorem gaussianNeg_cGauss_eq : (cGauss : Measure ℂ) =
    ((gaussianReal 0 (1 / 2 : ℝ≥0)).prod (gaussianReal 0 (1 / 2 : ℝ≥0))).map
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := rfl

/-- `z ↦ -z` preserves `cGauss`. -/
private theorem gaussianNeg_cGauss_neg :
    (cGauss : Measure ℂ).map (fun z => -z) = cGauss := by
  have hφ : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have hn : Measurable (fun x : ℝ => -x) := by fun_prop
  rw [gaussianNeg_cGauss_eq, Measure.map_map (by fun_prop) hφ]
  have hf : ((fun z : ℂ => -z) ∘ fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) =
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∘ Prod.map (fun x : ℝ => -x)
        (fun x : ℝ => -x) := by
    funext p; simp [Prod.map]; ring
  rw [hf, ← Measure.map_map hφ (hn.prodMap hn), ← Measure.map_prod_map _ _ hn hn,
    gaussianReal_map_neg, neg_zero]

/-- For real `a² + b² = 1`, `a z₁ + b z₂` is `cGauss` for independent `cGauss` variables
`z₁`, `z₂`. -/
private theorem gaussianNeg_cGauss_comb (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((cGauss : Measure ℂ).prod (cGauss : Measure ℂ)).map (fun p => a • p.1 + b • p.2) =
      cGauss := by
  set G := gaussianReal 0 (1 / 2 : ℝ≥0) with hG
  have hφ : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have hg : Measurable (fun p : ℝ × ℝ => a * p.1 + b * p.2) := by fun_prop
  rw [gaussianNeg_cGauss_eq, ← hG, Measure.map_prod_map _ _ hφ hφ,
    Measure.map_map (by fun_prop) (hφ.prodMap hφ)]
  have hf : ((fun p : ℂ × ℂ => a • p.1 + b • p.2) ∘
      Prod.map (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
        (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) =
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∘
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
          ((fun q : ℝ × ℝ => a * q.1 + b * q.2) (p.1.1, p.2.1),
           (fun q : ℝ × ℝ => a * q.1 + b * q.2) (p.1.2, p.2.2))) := by
    funext p
    simp only [Function.comp, Prod.map, Complex.real_smul]
    push_cast
    ring
  rw [hf, ← Measure.map_map hφ (by fun_prop),
    gaussianNeg_prodPair_map G G _ _ hg hg (gaussianNeg_real_comb _ a b hab)
      (gaussianNeg_real_comb _ a b hab)]

/-- `W ↦ -W` preserves the GUE. -/
theorem gueLaw_map_neg (n : ℕ) : (gueLaw n).map (fun w => -w) = gueLaw n := by
  have hn1 : (Measure.pi fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0)).map (fun x => -x) =
      Measure.pi fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0) := by
    have := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0))
      (f := fun _ x => -x) (fun _ => measurable_neg.aemeasurable)
    simp only [gaussianReal_map_neg, neg_zero] at this
    exact this
  have hn2 : (Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)).map (fun x => -x) =
      Measure.pi fun _ : Fin n => (cGauss : Measure ℂ) := by
    have := Measure.pi_map_pi (μ := fun _ : Fin n => (cGauss : Measure ℂ))
      (f := fun _ x => -x) (fun _ => measurable_neg.aemeasurable)
    simp only [gaussianNeg_cGauss_neg] at this
    exact this
  have hn3 : (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)).map
      (fun x => -x) =
      Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ) := by
    have := Measure.pi_map_pi
      (μ := fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ))
      (f := fun _ x => -x) (fun _ => measurable_neg.aemeasurable)
    simp only [hn2] at this
    exact this
  unfold gueLaw
  have := Measure.map_prod_map (Measure.pi fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0))
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ))
    measurable_neg measurable_neg
  rw [hn1, hn3] at this
  exact this.symm

/-- `a W₁ + b W₂` is GUE for independent GUE `W₁`, `W₂` and `a² + b² = 1`. -/
theorem gueLaw_map_add (n : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((gueLaw n).prod (gueLaw n)).map (fun p => a • p.1 + b • p.2) = gueLaw n := by
  have hR : ((Measure.pi fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0)).prod
      (Measure.pi fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0))).map
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => a • p.1 + b • p.2) =
      Measure.pi fun _ : Fin n => gaussianReal 0 (1 : ℝ≥0) :=
    gaussianNeg_piPair_map (ι := Fin n) (gaussianReal 0 (1 : ℝ≥0))
      (fun q : ℝ × ℝ => a * q.1 + b * q.2) (by fun_prop) (gaussianNeg_real_comb _ a b hab)
  have hC1 : ((Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)).prod
      (Measure.pi fun _ : Fin n => (cGauss : Measure ℂ))).map
      (fun p : (Fin n → ℂ) × (Fin n → ℂ) => a • p.1 + b • p.2) =
      Measure.pi fun _ : Fin n => (cGauss : Measure ℂ) :=
    gaussianNeg_piPair_map (ι := Fin n) (cGauss : Measure ℂ)
      (fun q : ℂ × ℂ => a • q.1 + b • q.2) (by fun_prop) (gaussianNeg_cGauss_comb a b hab)
  have hC : ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)).prod
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ))).map
      (fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => a • p.1 + b • p.2) =
      Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ) :=
    gaussianNeg_piPair_map (ι := Fin n) (Measure.pi fun _ : Fin n => (cGauss : Measure ℂ))
      (fun q : (Fin n → ℂ) × (Fin n → ℂ) => a • q.1 + b • q.2) (by fun_prop) hC1
  unfold gueLaw
  exact gaussianNeg_prodPair_map _ _
    (fun q : (Fin n → ℝ) × (Fin n → ℝ) => a • q.1 + b • q.2)
    (fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => a • q.1 + b • q.2)
    (by fun_prop) (by fun_prop) hR hC

/-- The block analogue: `D` independent GUE blocks. -/
def gueBlocks (D N : ℕ) : Measure (Fin D → Coords N) := Measure.pi fun _ : Fin D => gueLaw N

/-- `gueBlocks D N` is a probability measure. -/
instance gueBlocks_instIsProbabilityMeasure (D N : ℕ) : IsProbabilityMeasure (gueBlocks D N) := by
  unfold gueBlocks
  infer_instance

/-- The coordinates of size `DN` of `blockH D N w`, entries scaled by `√D` because `wig (D * N)`
scales by `(DN)^{-1/2}`; entries outside the diagonal blocks are `0`. -/
def blockEmb (D N : ℕ) (w : Fin D → Coords N) : Coords (D * N) :=
  (fun k => Real.sqrt D * (w (finProdFinEquiv.symm k).1).1 (finProdFinEquiv.symm k).2,
    fun k l => if (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1 then
      (Real.sqrt D : ℂ) * (w (finProdFinEquiv.symm k).1).2 (finProdFinEquiv.symm k).2
        (finProdFinEquiv.symm l).2 else 0)

/-- `blockEmb` reproduces the block-diagonal matrix `H` of (1.3) [matrix_H] as a `DN × DN` matrix. -/
theorem wig_blockEmb (D N : ℕ) (w : Fin D → Coords N) :
    (wig (D * N) (blockEmb D N w)).submatrix finProdFinEquiv finProdFinEquiv = blockH D N w := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [Matrix.submatrix_apply, wig, blockH, blockEmb, Equiv.symm_apply_apply]
  have hD : (0 : ℝ) < D := by exact_mod_cast Fin.pos a
  have hs : ((D * N : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt D = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Nat.cast_mul, Real.mul_rpow hD.le (Nat.cast_nonneg N), Real.sqrt_eq_rpow,
      Real.rpow_neg hD.le,
      Real.rpow_neg (Nat.cast_nonneg N)]
    field_simp
  by_cases hab : a = b
  · subst hab
    have hlt : finProdFinEquiv (a, i) < finProdFinEquiv (a, j) ↔ i < j := by
      simp only [Fin.lt_def, finProdFinEquiv_apply_val]
      omega
    have heq : finProdFinEquiv (a, i) = finProdFinEquiv (a, j) ↔ i = j := by
      simp
    simp only [ite_true, heq, hlt]
    split_ifs with h1 h2
    · subst h1
      rw [← hs]; push_cast; ring
    · rw [← hs]; push_cast; ring
    · rw [star_mul']
      simp only [Complex.star_def, Complex.conj_ofReal]
      rw [← hs]; push_cast; ring
  · have hne : finProdFinEquiv (a, i) ≠ finProdFinEquiv (b, j) := by
      simp [hab]
    have hba : ¬ b = a := fun h => hab h.symm
    simp [hne, hab, hba]

/-- The law (4.3) [eq:eq_in_law_H] of the coordinates of `H_t` in (4.1) [defVt]:
`e^{-t/2} H + √(1 - e^{-t}) W`, `W` a GUE of size `DN` independent of `H`. -/
def ouLaw (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) : Measure (Coords (D * N)) :=
  ((blockLaw D N L).prod (gueLaw (D * N))).map fun p =>
    Real.exp (-t / 2) • blockEmb D N p.1 + Real.sqrt (1 - Real.exp (-t)) • p.2

end RBMTransitionEdge

end
