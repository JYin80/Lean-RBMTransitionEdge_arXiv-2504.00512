module

public import RBMTransitionEdge.LocalLaw.Class
public import RBMTransitionEdge.Prob.Gaussian

@[expose] public section

/-!
# The law of `H_t` in the class

The law (4.3) [eq:eq_in_law_H] of `H_t` of (4.1) [defVt] on arrays indexed by `Idx D N`, and its
membership in `LLClass` with `θ = e^{-t}` and moment constants depending on `C` only.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge


/-! ### Independence tools -/

/-- Two independent families of independent complex random variables form one independent
family, indexed by the disjoint sum. -/
private lemma OU_iIndepFun_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ι κ : Type*} {u : ι → Ω → ℂ} {v : κ → Ω → ℂ}
    (h1 : iIndepFun u P) (h2 : iIndepFun v P)
    (h3 : IndepFun (fun ω i => u i ω) (fun ω k => v k ω) P) :
    iIndepFun (Sum.elim u v) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h1 h2 ⊢
  intro S A hA
  have e : (⋂ s ∈ S, Sum.elim u v s ⁻¹' A s) =
      (fun ω i => u i ω) ⁻¹' (Set.pi (S.toLeft : Set ι) fun i => A (Sum.inl i)) ∩
      (fun ω k => v k ω) ⁻¹' (Set.pi (S.toRight : Set κ) fun k => A (Sum.inr k)) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe,
      Finset.mem_toLeft, Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun i hi => h _ hi, fun k hk => h _ hk⟩
    · rintro ⟨hl, hr⟩ s hs
      cases s with
      | inl i => exact hl i hs
      | inr k => exact hr k hs
  have m1 : MeasurableSet (Set.pi (S.toLeft : Set ι) fun i => A (Sum.inl i)) :=
    MeasurableSet.pi S.toLeft.countable_toSet fun i hi => hA _ (by simpa using hi)
  have m2 : MeasurableSet (Set.pi (S.toRight : Set κ) fun k => A (Sum.inr k)) :=
    MeasurableSet.pi S.toRight.countable_toSet fun i hi => hA _ (by simpa using hi)
  rw [e, h3.measure_inter_preimage_eq_mul _ _ m1 m2]
  have p1 : P ((fun ω i => u i ω) ⁻¹' (Set.pi (S.toLeft : Set ι) fun i => A (Sum.inl i))) =
      ∏ i ∈ S.toLeft, P (u i ⁻¹' A (Sum.inl i)) := by
    have := h1 S.toLeft (sets := fun i => A (Sum.inl i)) (fun i hi => hA _ (by simpa using hi))
    rw [← this]
    congr 1
    ext ω
    simp
  have p2 : P ((fun ω k => v k ω) ⁻¹' (Set.pi (S.toRight : Set κ) fun k => A (Sum.inr k))) =
      ∏ k ∈ S.toRight, P (v k ⁻¹' A (Sum.inr k)) := by
    have := h2 S.toRight (sets := fun k => A (Sum.inr k)) (fun i hi => hA _ (by simpa using hi))
    rw [← this]
    congr 1
    ext ω
    simp
  rw [p1, p2]
  conv_rhs => rw [← Finset.toLeft_disjSum_toRight (u := S), Finset.prod_disjSum]
  simp

/-- Independence of a family transfers along a measure-preserving map. -/
private lemma OU_iIndepFun_comp_mp {Ω Ω' ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] {P : Measure Ω} {ν : Measure Ω'} {e : Ω → Ω'}
    (he : MeasurePreserving e P ν) {f : ι → Ω' → β} (hf : ∀ q, Measurable (f q))
    (h : iIndepFun f ν) : iIndepFun (fun q ω => f q (e ω)) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S A hA
  have e1 : (⋂ q ∈ S, (fun ω => f q (e ω)) ⁻¹' A q) = e ⁻¹' (⋂ q ∈ S, f q ⁻¹' A q) := by
    ext ω
    simp
  have m1 : MeasurableSet (⋂ q ∈ S, f q ⁻¹' A q) :=
    MeasurableSet.biInter S.countable_toSet fun q hq => hf q (hA q hq)
  rw [e1, he.measure_preimage m1.nullMeasurableSet, h S hA]
  refine Finset.prod_congr rfl fun q hq => ?_
  exact (he.measure_preimage (hf q (hA q hq)).nullMeasurableSet).symm

/-- Independence of the family `g q ∘ e` under `P` gives independence of `g` under the image law
`P.map e`. -/
private lemma OU_iIndepFun_map {Ω Ω' ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] {P : Measure Ω} {e : Ω → Ω'} (he : Measurable e)
    {g : ι → Ω' → β} (hg : ∀ q, Measurable (g q))
    (h : iIndepFun (fun q ω => g q (e ω)) P) : iIndepFun g (P.map e) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S A hA
  have e1 : (⋂ q ∈ S, (fun ω => g q (e ω)) ⁻¹' A q) = e ⁻¹' (⋂ q ∈ S, g q ⁻¹' A q) := by
    ext ω
    simp
  have m1 : MeasurableSet (⋂ q ∈ S, g q ⁻¹' A q) :=
    MeasurableSet.biInter S.countable_toSet fun q hq => hg q (hA q hq)
  rw [Measure.map_apply he m1, ← e1, h S hA]
  refine Finset.prod_congr rfl fun q hq => ?_
  rw [Measure.map_apply he (hg q (hA q hq))]
  rfl

/-- The coordinates of one array `Coords n`, the `n` diagonal entries (as complex numbers) and the
`n²` array entries, are independent under the product of coordinatewise laws `μ`, `ν`. -/
private lemma OU_iIndep_coords (n : ℕ) (μ : Measure ℝ) (ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    iIndepFun (Sum.elim (fun (i : Fin n) (c : Coords n) => ((c.1 i : ℝ) : ℂ))
      (fun (p : Fin n × Fin n) (c : Coords n) => c.2 p.1 p.2))
      ((Measure.pi fun _ : Fin n => μ).prod
        (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => ν)) := by
  have hx : iIndepFun (fun (i : Fin n) (c : Coords n) => ((c.1 i : ℝ) : ℂ))
      ((Measure.pi fun _ : Fin n => μ).prod
        (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => ν)) := by
    have h0 : iIndepFun (fun (i : Fin n) (x : Fin n → ℝ) => x i)
        (Measure.pi fun _ : Fin n => μ) :=
      iIndepFun_pi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id.aemeasurable)
    have h1 := OU_iIndepFun_comp_mp
      (measurePreserving_fst (μ := Measure.pi fun _ : Fin n => μ)
        (ν := Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => ν))
      (f := fun (i : Fin n) (x : Fin n → ℝ) => x i) (fun i => measurable_pi_apply i) h0
    exact h1.comp (fun _ => fun x : ℝ => (x : ℂ)) (fun _ => Complex.measurable_ofReal)
  have hy : iIndepFun (fun (p : Fin n × Fin n) (c : Coords n) => c.2 p.1 p.2)
      ((Measure.pi fun _ : Fin n => μ).prod
        (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => ν)) := by
    have h1 : iIndepFun (fun (i : Fin n) (z : Fin n → Fin n → ℂ) => z i)
        (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => ν) :=
      iIndepFun_pi (X := fun _ (z : Fin n → ℂ) => z) (fun _ => measurable_id.aemeasurable)
    have h2 : ∀ i : Fin n, iIndepFun (fun (j : Fin n) (z : Fin n → Fin n → ℂ) => z i j)
        (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => ν) := by
      intro i
      have h0 : iIndepFun (fun (j : Fin n) (z : Fin n → ℂ) => z j)
          (Measure.pi fun _ : Fin n => ν) :=
        iIndepFun_pi (X := fun _ (x : ℂ) => x) (fun _ => measurable_id.aemeasurable)
      exact OU_iIndepFun_comp_mp
        (measurePreserving_eval (fun _ : Fin n => Measure.pi fun _ : Fin n => ν) i)
        (f := fun (j : Fin n) (z : Fin n → ℂ) => z j) (fun j => measurable_pi_apply j) h0
    have h3 := iIndepFun_uncurry' (X := fun (i j : Fin n) (z : Fin n → Fin n → ℂ) => z i j)
      (fun i j => (measurable_pi_apply j).comp (measurable_pi_apply i)) h1 h2
    exact OU_iIndepFun_comp_mp
      (measurePreserving_snd (μ := Measure.pi fun _ : Fin n => μ)
        (ν := Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => ν))
      (f := fun (p : Fin n × Fin n) (z : Fin n → Fin n → ℂ) => z p.1 p.2)
      (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)) h3
  have hp : IndepFun (fun (c : Coords n) (i : Fin n) => ((c.1 i : ℝ) : ℂ))
      (fun (c : Coords n) (p : Fin n × Fin n) => c.2 p.1 p.2)
      ((Measure.pi fun _ : Fin n => μ).prod
        (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => ν)) :=
    indepFun_prod (μ := Measure.pi fun _ : Fin n => μ)
      (ν := Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => ν)
      (X := fun (x : Fin n → ℝ) (i : Fin n) => ((x i : ℝ) : ℂ))
      (Y := fun (z : Fin n → Fin n → ℂ) (p : Fin n × Fin n) => z p.1 p.2)
      (measurable_pi_iff.mpr fun i => Complex.measurable_ofReal.comp (measurable_pi_apply i))
      (measurable_pi_iff.mpr fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  exact OU_iIndepFun_sum hx hy hp

/-- Two independent families, one on each factor of a product space, give the independent family
of the linear combinations `a u_q + b v_q`. -/
private lemma OU_iIndep_pair {Ω₁ Ω₂ ι : Type*} [Finite ι] [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {u : ι → Ω₁ → ℂ} {v : ι → Ω₂ → ℂ}
    (hu : ∀ q, Measurable (u q)) (hv : ∀ q, Measurable (v q))
    (hu' : iIndepFun u μ₁) (hv' : iIndepFun v μ₂) (a b : ℂ) :
    iIndepFun (fun q (ω : Ω₁ × Ω₂) => a * u q ω.1 + b * v q ω.2) (μ₁.prod μ₂) := by
  have := Fintype.ofFinite ι
  have hφ : Measurable (fun r : ℂ × ℂ => a * r.1 + b * r.2) := by fun_prop
  have hUm : Measurable (fun (w : Ω₁) (q : ι) => u q w) := measurable_pi_iff.mpr hu
  have hVm : Measurable (fun (w : Ω₂) (q : ι) => v q w) := measurable_pi_iff.mpr hv
  have hg : ∀ q, Measurable (fun ω : Ω₁ × Ω₂ => a * u q ω.1 + b * v q ω.2) := by
    intro q
    exact hφ.comp (((hu q).comp measurable_fst).prodMk ((hv q).comp measurable_snd))
  have hmp := (measurePreserving_arrowProdEquivProdArrow ℂ ℂ ι
    (fun q => μ₁.map (u q)) (fun q => μ₂.map (v q))).symm
  have hΦ : (fun (ω : Ω₁ × Ω₂) (q : ι) => a * u q ω.1 + b * v q ω.2) =
      (fun (x : ι → ℂ × ℂ) (q : ι) => (fun r : ℂ × ℂ => a * r.1 + b * r.2) (x q)) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow ℂ ℂ ι).symm ∘
        Prod.map (fun (w : Ω₁) (q : ι) => u q w) (fun (w : Ω₂) (q : ι) => v q w) := by
    funext ω q; rfl
  refine (iIndepFun_iff_map_fun_eq_pi_map (fun q => (hg q).aemeasurable)).2 ?_
  rw [hΦ, ← Measure.map_map (by fun_prop)
      ((MeasurableEquiv.measurable _).comp (hUm.prodMap hVm)),
    ← Measure.map_map (MeasurableEquiv.measurable _) (hUm.prodMap hVm),
    ← Measure.map_prod_map _ _ hUm hVm, hu'.map_fun_eq_pi_map (fun q => (hu q).aemeasurable),
    hv'.map_fun_eq_pi_map (fun q => (hv q).aemeasurable), hmp.map_eq,
    Measure.pi_map_pi (fun q => hφ.aemeasurable)]
  congr 1
  funext q
  have hq : (fun ω : Ω₁ × Ω₂ => a * u q ω.1 + b * v q ω.2) =
      (fun r : ℂ × ℂ => a * r.1 + b * r.2) ∘ Prod.map (u q) (v q) := rfl
  rw [hq, ← Measure.map_map hφ ((hu q).prodMap (hv q)),
    ← Measure.map_prod_map _ _ (hu q) (hv q)]

/-! ### Gaussian facts -/

/-- `(a + b)^k ≤ 2^k (a^k + b^k)` for `a, b ≥ 0`. -/
private lemma OU_pow_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  refine (add_pow_le ha hb k).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)

/-- Integrals against a measure-preserving image. -/
private lemma OU_integral_comp {Ω α E : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {P : Measure Ω} {ν : Measure α} {cd : Ω → α}
    (hcd : MeasurePreserving cd P ν) {G : α → E} (hG : AEStronglyMeasurable G ν) :
    ∫ w, G (cd w) ∂P = ∫ a, G a ∂ν := by
  rw [← hcd.map_eq] at hG ⊢
  exact (integral_map hcd.measurable.aemeasurable hG).symm

/-- Every absolute moment of a real Gaussian law is finite. -/
private lemma OU_G_int (v : NNReal) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
  have := (memLp_id_gaussianReal' (μ := 0) (v := v) ((k : ℕ) : ENNReal)
    (by simp)).integrable_norm_pow'
  simpa using this

/-- The identity is integrable against a real Gaussian law. -/
private lemma OU_G_int1 (v : NNReal) : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal' (μ := 0) (v := v) 1 (by simp)).integrable le_rfl

/-- The second moment of `N(0, v)` is `v`. -/
private lemma OU_G_sq (v : NNReal) : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- The law `cGauss` as the image of `N(0,1/2) ⊗ N(0,1/2)` under `(x, y) ↦ x + y i`. -/
private lemma OU_cGauss_eq : (cGauss : Measure ℂ) =
    ((gaussianReal 0 (1 / 2 : NNReal)).prod (gaussianReal 0 (1 / 2 : NNReal))).map
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := rfl

/-- The map `(x, y) ↦ x + y i` is measurable. -/
private lemma OU_measurable_phi :
    Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop

/-- Integrals against `cGauss` of a continuous function are integrals against the product of two
real Gaussians. -/
private lemma OU_c_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E)
    (hf : Continuous f) :
    ∫ z, f z ∂(cGauss : Measure ℂ) =
      ∫ p : ℝ × ℝ, f ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
        ∂((gaussianReal 0 (1 / 2 : NNReal)).prod (gaussianReal 0 (1 / 2 : NNReal))) := by
  rw [OU_cGauss_eq]
  exact integral_map OU_measurable_phi.aemeasurable hf.aestronglyMeasurable

/-- Every absolute moment of `cGauss` is finite. -/
private lemma OU_c_int (k : ℕ) : Integrable (fun z : ℂ => ‖z‖ ^ k) (cGauss : Measure ℂ) := by
  set G := gaussianReal 0 (1 / 2 : NNReal) with hG
  have hc : Continuous (fun z : ℂ => ‖z‖ ^ k) := by fun_prop
  rw [OU_cGauss_eq, integrable_map_measure hc.aestronglyMeasurable
    OU_measurable_phi.aemeasurable]
  refine Integrable.mono' (g := fun p : ℝ × ℝ => 2 ^ k * (|p.1| ^ k + |p.2| ^ k)) ?_ ?_ ?_
  · exact (((OU_G_int _ k).comp_fst G).add ((OU_G_int _ k).comp_snd G)).const_mul _
  · exact (hc.measurable.comp OU_measurable_phi).aestronglyMeasurable
  · filter_upwards with p
    have h1 : ‖(p.1 : ℂ) + (p.2 : ℂ) * Complex.I‖ ≤ |p.1| + |p.2| := by
      refine (norm_add_le _ _).trans ?_
      simp
    have h2 := OU_pow_add_le (abs_nonneg p.1) (abs_nonneg p.2) k
    simp only [Function.comp, Real.norm_eq_abs, abs_pow, abs_norm]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 k).trans h2

/-- The second moment `x²` is integrable against a real Gaussian law. -/
private lemma OU_G_int_sq (v : NNReal) : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
  simpa [sq_abs] using OU_G_int v 2

/-- `cGauss` has mean zero. -/
private lemma OU_c_mean : ∫ z : ℂ, z ∂(cGauss : Measure ℂ) = 0 := by
  set G := gaussianReal 0 (1 / 2 : NNReal) with hG
  rw [OU_c_integral (fun z => z) continuous_id]
  have h1 : Integrable (fun p : ℝ × ℝ => (p.1 : ℂ)) (G.prod G) :=
    ((OU_G_int1 _).comp_fst G).ofReal
  have h2 : Integrable (fun p : ℝ × ℝ => (p.2 : ℂ) * Complex.I) (G.prod G) :=
    (((OU_G_int1 _).comp_snd G).ofReal).mul_const _
  rw [integral_add h1 h2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_fun_fst (fun x : ℝ => x), integral_fun_snd (fun x : ℝ => x)]
  simp [hG]

/-- `E|z|² = 1` for `cGauss`. -/
private lemma OU_c_var : ∫ z : ℂ, ‖z‖ ^ 2 ∂(cGauss : Measure ℂ) = 1 := by
  set G := gaussianReal 0 (1 / 2 : NNReal) with hG
  rw [OU_c_integral (fun z => ‖z‖ ^ 2) (by fun_prop)]
  have e : ∀ p : ℝ × ℝ, ‖(p.1 : ℂ) + (p.2 : ℂ) * Complex.I‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    intro p
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  simp only [e]
  rw [integral_add ((OU_G_int_sq _).comp_fst G) ((OU_G_int_sq _).comp_snd G),
    integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2), hG, OU_G_sq]
  norm_num

/-- `E z² = 0` for `cGauss`. -/
private lemma OU_c_pseudo : ∫ z : ℂ, z ^ 2 ∂(cGauss : Measure ℂ) = 0 := by
  set G := gaussianReal 0 (1 / 2 : NNReal) with hG
  rw [OU_c_integral (fun z => z ^ 2) (by fun_prop)]
  have e : ∀ p : ℝ × ℝ, ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ^ 2 =
      ((p.1 ^ 2 : ℝ) : ℂ) - ((p.2 ^ 2 : ℝ) : ℂ) + (2 * Complex.I) * ((p.1 : ℂ) * (p.2 : ℂ)) := by
    intro p
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [e]
  have h1 : Integrable (fun p : ℝ × ℝ => ((p.1 ^ 2 : ℝ) : ℂ)) (G.prod G) :=
    ((OU_G_int_sq _).comp_fst G).ofReal
  have h2 : Integrable (fun p : ℝ × ℝ => ((p.2 ^ 2 : ℝ) : ℂ)) (G.prod G) :=
    ((OU_G_int_sq _).comp_snd G).ofReal
  have h3 : Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) * (p.2 : ℂ)) (G.prod G) :=
    Integrable.mul_prod (OU_G_int1 _).ofReal (OU_G_int1 _).ofReal
  have h12 : Integrable (fun p : ℝ × ℝ => ((p.1 ^ 2 : ℝ) : ℂ) - ((p.2 ^ 2 : ℝ) : ℂ))
      (G.prod G) := h1.sub h2
  rw [integral_add h12 (h3.const_mul _), integral_sub h1 h2, integral_const_mul,
    integral_prod_mul (fun x : ℝ => (x : ℂ)) (fun y : ℝ => (y : ℂ))]
  simp only [integral_complex_ofReal]
  rw [integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2),
    integral_complex_ofReal (f := fun x : ℝ => x)]
  simp [hG]

/-- The moment constant `m_k`: the sum of the `k`-th absolute moments of the standard real
Gaussian law and of `cGauss`. It dominates the `k`-th absolute moment of each entry of the GUE
`gueLaw` before scaling. -/
private def OU_m (k : ℕ) : ℝ :=
  (∫ x : ℝ, |x| ^ k ∂(gaussianReal 0 1)) + ∫ z : ℂ, ‖z‖ ^ k ∂(cGauss : Measure ℂ)

/-- A centred complex random variable with all absolute moments finite. -/
private structure OU_Facts {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℂ) : Prop where
  /-- `X` is measurable. -/
  meas : Measurable X
  /-- Every absolute moment of `X` is finite. -/
  integrable : ∀ k : ℕ, Integrable (fun ω => ‖X ω‖ ^ k) μ
  /-- `E X = 0`. -/
  mean : ∫ ω, X ω ∂μ = 0

/-- A unit-variance noise whose absolute moments are bounded by `m_k`. -/
private structure OU_Unit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ) : Prop where
  /-- The basic facts. -/
  facts : OU_Facts μ Z
  /-- `E|Z|² = 1`. -/
  var : ∫ ω, ‖Z ω‖ ^ 2 ∂μ = 1
  /-- `E|Z|^k ≤ m_k`. -/
  moments : ∀ k : ℕ, ∫ ω, ‖Z ω‖ ^ k ∂μ ≤ OU_m k

/-- The absolute moments of the standard real Gaussian law and of `cGauss` are nonnegative. -/
private lemma OU_m_parts (k : ℕ) :
    0 ≤ ∫ x : ℝ, |x| ^ k ∂(gaussianReal 0 1) ∧ 0 ≤ ∫ z : ℂ, ‖z‖ ^ k ∂(cGauss : Measure ℂ) :=
  ⟨integral_nonneg fun x => by positivity, integral_nonneg fun z => by positivity⟩

/-- The moment facts of a noise transfer along a measure-preserving coordinate map. -/
private lemma OU_Unit.comp {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {ν : Measure α} {cd : Ω → α} (hcd : MeasurePreserving cd P ν)
    {Z : α → ℂ} (h : OU_Unit ν Z) : OU_Unit P (fun w => Z (cd w)) := by
  have hZ := h.facts.meas
  have hn : ∀ k : ℕ, Measurable fun a => ‖Z a‖ ^ k := fun k => hZ.norm.pow_const k
  refine ⟨⟨hZ.comp hcd.measurable, fun k => ?_, ?_⟩, ?_, fun k => ?_⟩
  · exact (hcd.integrable_comp (hn k).aestronglyMeasurable).mpr (h.facts.integrable k)
  · rw [OU_integral_comp hcd hZ.aestronglyMeasurable, h.facts.mean]
  · rw [OU_integral_comp hcd (hn 2).aestronglyMeasurable (G := fun a => ‖Z a‖ ^ 2), h.var]
  · rw [OU_integral_comp hcd (hn k).aestronglyMeasurable (G := fun a => ‖Z a‖ ^ k)]
    exact h.moments k

/-- The standard real Gaussian, as a complex noise. -/
private lemma OU_unit_real : OU_Unit (gaussianReal 0 1) (fun x : ℝ => (x : ℂ)) := by
  refine ⟨⟨Complex.measurable_ofReal, fun k => ?_, ?_⟩, ?_, fun k => ?_⟩
  · simpa [Complex.norm_real] using OU_G_int 1 k
  · rw [integral_complex_ofReal (f := fun x : ℝ => x)]
    simp
  · simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [OU_G_sq]
    simp
  · simp only [Complex.norm_real, Real.norm_eq_abs]
    unfold OU_m
    linarith [(OU_m_parts k).2]

/-- The standard complex Gaussian `cGauss`, as a noise. -/
private lemma OU_unit_c : OU_Unit (cGauss : Measure ℂ) (fun z : ℂ => z) := by
  refine ⟨⟨measurable_id, OU_c_int, OU_c_mean⟩, OU_c_var, fun k => ?_⟩
  unfold OU_m
  linarith [(OU_m_parts k).1]

/-- The conjugate of a standard complex Gaussian, as a noise. -/
private lemma OU_unit_cstar : OU_Unit (cGauss : Measure ℂ) (fun z : ℂ => star z) := by
  refine ⟨⟨(continuous_star (R := ℂ)).measurable, fun k => ?_, ?_⟩, ?_, fun k => ?_⟩
  · simpa using OU_c_int k
  · have : ∫ z : ℂ, star z ∂(cGauss : Measure ℂ) = star (∫ z : ℂ, z ∂(cGauss : Measure ℂ)) := by
      simpa [Complex.star_def] using integral_conj (f := fun z : ℂ => z) (μ := (cGauss : Measure ℂ))
    rw [this, OU_c_mean, star_zero]
  · simpa using OU_c_var
  · simp only [norm_star]
    unfold OU_m
    linarith [(OU_m_parts k).1]

/-- The conjugate of a standard complex Gaussian has vanishing pseudo-variance. -/
private lemma OU_cstar_pseudo : ∫ z : ℂ, (star z) ^ 2 ∂(cGauss : Measure ℂ) = 0 := by
  have : ∫ z : ℂ, star (z ^ 2) ∂(cGauss : Measure ℂ) =
      star (∫ z : ℂ, z ^ 2 ∂(cGauss : Measure ℂ)) :=
    integral_conj (f := fun z : ℂ => z ^ 2) (μ := (cGauss : Measure ℂ))
  simp only [star_pow] at this
  rw [this, OU_c_pseudo, star_zero]

/-- The diagonal coordinate `W.1 k` of the GUE has law `N(0,1)`. -/
private lemma OU_mp_x (n : ℕ) (k : Fin n) :
    MeasurePreserving (fun W : Coords n => W.1 k) (gueLaw n) (gaussianReal 0 1) := by
  unfold gueLaw
  exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) k).comp measurePreserving_fst

/-- The array coordinate `W.2 k l` of the GUE has law `cGauss`. -/
private lemma OU_mp_y (n : ℕ) (k l : Fin n) :
    MeasurePreserving (fun W : Coords n => W.2 k l) (gueLaw n) (cGauss : Measure ℂ) := by
  unfold gueLaw
  have h4 : MeasurePreserving (fun z : Fin n → ℂ => z l)
      (Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)) (cGauss : Measure ℂ) :=
    measurePreserving_eval (fun _ : Fin n => (cGauss : Measure ℂ)) l
  have h3 : MeasurePreserving (fun z : Fin n → Fin n → ℂ => z k)
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ))
      (Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)) :=
    measurePreserving_eval (fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)) k
  exact h4.comp (h3.comp measurePreserving_snd)

/-- The unscaled entry `(k, l)` of the GUE: `n^{1/2}` times the entry of `wig n`. -/
private def OU_U (n : ℕ) (k l : Fin n) (W : Coords n) : ℂ :=
  if k = l then ((W.1 k : ℝ) : ℂ) else if k < l then W.2 k l else star (W.2 l k)

/-- The unscaled entries of the GUE are unit noises, and have vanishing pseudo-variance off the
diagonal. -/
private lemma OU_unit_entry (n : ℕ) (k l : Fin n) :
    OU_Unit (gueLaw n) (OU_U n k l) ∧
      (k ≠ l → ∫ W, (OU_U n k l W) ^ 2 ∂(gueLaw n) = 0) := by
  by_cases h : k = l
  · subst h
    have e : OU_U n k k = fun W => ((W.1 k : ℝ) : ℂ) := by
      funext W
      simp [OU_U]
    rw [e]
    exact ⟨OU_unit_real.comp (OU_mp_x n k), fun h' => absurd rfl h'⟩
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · have e : OU_U n k l = fun W => W.2 k l := by
        funext W
        simp [OU_U, h, hlt]
      rw [e]
      refine ⟨OU_unit_c.comp (OU_mp_y n k l), fun _ => ?_⟩
      exact (OU_integral_comp (OU_mp_y n k l) (G := fun z : ℂ => z ^ 2)
        (continuous_pow 2).aestronglyMeasurable).trans OU_c_pseudo
    · have e : OU_U n k l = fun W => star (W.2 l k) := by
        funext W
        simp [OU_U, h, hgt.not_gt]
      rw [e]
      refine ⟨OU_unit_cstar.comp (OU_mp_y n l k), fun _ => ?_⟩
      exact (OU_integral_comp (OU_mp_y n l k) (G := fun z : ℂ => (star z) ^ 2)
        (by fun_prop)).trans OU_cstar_pseudo

/-! ### Combining two independent noises -/

/-- `X` is integrable. -/
private lemma OU_Facts.int1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℂ}
    (h : OU_Facts μ X) : Integrable X μ :=
  (integrable_norm_iff h.meas.aestronglyMeasurable).mp (by simpa using h.integrable 1)

/-- `X²` is integrable. -/
private lemma OU_Facts.int_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℂ}
    (h : OU_Facts μ X) : Integrable (fun ω => X ω ^ 2) μ :=
  (integrable_norm_iff (h.meas.pow_const 2).aestronglyMeasurable).mp
    (by simpa [norm_pow] using h.integrable 2)

/-- Scaling a noise by a real constant. -/
private lemma OU_Facts.const_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℂ}
    (h : OU_Facts μ X) (c : ℝ) : OU_Facts μ (fun ω => (c : ℂ) * X ω) := by
  refine ⟨measurable_const.mul h.meas, fun k => ?_, ?_⟩
  · simp only [norm_mul, Complex.norm_real, mul_pow]
    exact (h.integrable k).const_mul _
  · rw [integral_const_mul, h.mean, mul_zero]

/-- The integral of a function of the first coordinate against a product probability measure. -/
private lemma OU_int_fst {Ω₁ Ω₂ E : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (F : Ω₁ → E) :
    ∫ ω, F ω.1 ∂(μ₁.prod μ₂) = ∫ x, F x ∂μ₁ := by
  rw [integral_fun_fst]
  simp

/-- The integral of a function of the second coordinate against a product probability measure. -/
private lemma OU_int_snd {Ω₁ Ω₂ E : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (F : Ω₂ → E) :
    ∫ ω, F ω.2 ∂(μ₁.prod μ₂) = ∫ x, F x ∂μ₂ := by
  rw [integral_fun_snd]
  simp

/-- `|a|, |b| ≤ 1` gives `‖aX + bY‖ ≤ ‖X‖ + ‖Y‖`. -/
private lemma OU_norm_comb_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (x y : ℂ) :
    ‖(a : ℂ) * x + (b : ℂ) * y‖ ≤ ‖x‖ + ‖y‖ := by
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [norm_nonneg x, norm_nonneg y, abs_nonneg a, abs_nonneg b]

/-- The integrability, centring and moment bound of the combination `aX + bY` of independent
noises on a product space. -/
private lemma OU_comb_facts {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {X : Ω₁ → ℂ} {Y : Ω₂ → ℂ} (hX : OU_Facts μ₁ X) (hY : OU_Facts μ₂ Y) (a b : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    OU_Facts (μ₁.prod μ₂) (fun ω => (a : ℂ) * X ω.1 + (b : ℂ) * Y ω.2) ∧
      ∀ k : ℕ, ∫ ω, ‖(a : ℂ) * X ω.1 + (b : ℂ) * Y ω.2‖ ^ k ∂(μ₁.prod μ₂) ≤
        2 ^ k * ((∫ x, ‖X x‖ ^ k ∂μ₁) + ∫ y, ‖Y y‖ ^ k ∂μ₂) := by
  have hm : Measurable (fun ω : Ω₁ × Ω₂ => (a : ℂ) * X ω.1 + (b : ℂ) * Y ω.2) :=
    (measurable_const.mul (hX.meas.comp measurable_fst)).add
      (measurable_const.mul (hY.meas.comp measurable_snd))
  have hint : ∀ k : ℕ, Integrable (fun ω : Ω₁ × Ω₂ =>
      2 ^ k * (‖X ω.1‖ ^ k + ‖Y ω.2‖ ^ k)) (μ₁.prod μ₂) := fun k =>
    (((hX.integrable k).comp_fst μ₂).add ((hY.integrable k).comp_snd μ₁)).const_mul _
  have hle : ∀ (k : ℕ) (ω : Ω₁ × Ω₂),
      ‖(a : ℂ) * X ω.1 + (b : ℂ) * Y ω.2‖ ^ k ≤ 2 ^ k * (‖X ω.1‖ ^ k + ‖Y ω.2‖ ^ k) :=
    fun k ω => (pow_le_pow_left₀ (norm_nonneg _) (OU_norm_comb_le ha hb _ _) k).trans
      (OU_pow_add_le (norm_nonneg _) (norm_nonneg _) k)
  have h1 := hX.int1
  have h2 := hY.int1
  have hF : OU_Facts (μ₁.prod μ₂) (fun ω => (a : ℂ) * X ω.1 + (b : ℂ) * Y ω.2) := by
    refine ⟨hm, fun k => ?_, ?_⟩
    · refine Integrable.mono' (hint k) (hm.norm.pow_const k).aestronglyMeasurable ?_
      filter_upwards with ω
      simpa using hle k ω
    · rw [integral_add ((h1.comp_fst μ₂).const_mul _) ((h2.comp_snd μ₁).const_mul _),
        integral_const_mul, integral_const_mul, OU_int_fst (μ₂ := μ₂) X,
        OU_int_snd (μ₁ := μ₁) Y, hX.mean, hY.mean]
      simp
  refine ⟨hF, fun k => ?_⟩
  refine (integral_mono (hF.integrable k) (hint k) (hle k)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add ((hX.integrable k).comp_fst μ₂)
    ((hY.integrable k).comp_snd μ₁), OU_int_fst (μ₂ := μ₂) (fun x => ‖X x‖ ^ k),
    OU_int_snd (μ₁ := μ₁) (fun y => ‖Y y‖ ^ k)]

/-- The variance of the combination `aX + bY` of independent centred noises. -/
private lemma OU_comb_var {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {X : Ω₁ → ℂ} {Y : Ω₂ → ℂ} (hX : OU_Facts μ₁ X) (hY : OU_Facts μ₂ Y) (a b : ℝ) :
    ∫ ω, ‖(a : ℂ) * X ω.1 + (b : ℂ) * Y ω.2‖ ^ 2 ∂(μ₁.prod μ₂) =
      a ^ 2 * ∫ x, ‖X x‖ ^ 2 ∂μ₁ + b ^ 2 * ∫ y, ‖Y y‖ ^ 2 ∂μ₂ := by
  have e : ∀ ω : Ω₁ × Ω₂, ‖(a : ℂ) * X ω.1 + (b : ℂ) * Y ω.2‖ ^ 2 =
      a ^ 2 * ‖X ω.1‖ ^ 2 + b ^ 2 * ‖Y ω.2‖ ^ 2 +
        2 * (a * b) * ((X ω.1).re * (Y ω.2).re + (X ω.1).im * (Y ω.2).im) := by
    intro ω
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  simp only [e]
  have hXre : Integrable (fun x => (X x).re) μ₁ := by simpa using hX.int1.re
  have hXim : Integrable (fun x => (X x).im) μ₁ := by simpa using hX.int1.im
  have hYre : Integrable (fun y => (Y y).re) μ₂ := by simpa using hY.int1.re
  have hYim : Integrable (fun y => (Y y).im) μ₂ := by simpa using hY.int1.im
  have hXre0 : ∫ x, (X x).re ∂μ₁ = 0 := by
    have := integral_re (𝕜 := ℂ) hX.int1
    simpa [hX.mean] using this
  have hXim0 : ∫ x, (X x).im ∂μ₁ = 0 := by
    have := integral_im (𝕜 := ℂ) hX.int1
    simpa [hX.mean] using this
  have i1 : Integrable (fun ω : Ω₁ × Ω₂ => a ^ 2 * ‖X ω.1‖ ^ 2) (μ₁.prod μ₂) :=
    ((hX.integrable 2).comp_fst μ₂).const_mul _
  have i2 : Integrable (fun ω : Ω₁ × Ω₂ => b ^ 2 * ‖Y ω.2‖ ^ 2) (μ₁.prod μ₂) :=
    ((hY.integrable 2).comp_snd μ₁).const_mul _
  have i3 : Integrable (fun ω : Ω₁ × Ω₂ => (X ω.1).re * (Y ω.2).re) (μ₁.prod μ₂) :=
    Integrable.mul_prod hXre hYre
  have i4 : Integrable (fun ω : Ω₁ × Ω₂ => (X ω.1).im * (Y ω.2).im) (μ₁.prod μ₂) :=
    Integrable.mul_prod hXim hYim
  have i12 : Integrable (fun ω : Ω₁ × Ω₂ => a ^ 2 * ‖X ω.1‖ ^ 2 + b ^ 2 * ‖Y ω.2‖ ^ 2)
      (μ₁.prod μ₂) := i1.add i2
  have i34 : Integrable (fun ω : Ω₁ × Ω₂ =>
      (X ω.1).re * (Y ω.2).re + (X ω.1).im * (Y ω.2).im) (μ₁.prod μ₂) := i3.add i4
  rw [integral_add i12 (i34.const_mul _), integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_add i3 i4,
    integral_prod_mul (fun x => (X x).re) (fun y => (Y y).re),
    integral_prod_mul (fun x => (X x).im) (fun y => (Y y).im), hXre0, hXim0,
    OU_int_fst (μ₂ := μ₂) (fun x => ‖X x‖ ^ 2), OU_int_snd (μ₁ := μ₁) (fun y => ‖Y y‖ ^ 2)]
  simp

/-- The pseudo-variance of the combination `aX + bY` of independent centred noises, when those of
`X` and `Y` vanish. -/
private lemma OU_comb_pseudo {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {X : Ω₁ → ℂ} {Y : Ω₂ → ℂ} (hX : OU_Facts μ₁ X) (hY : OU_Facts μ₂ Y) (a b : ℝ)
    (hX2 : ∫ x, X x ^ 2 ∂μ₁ = 0) (hY2 : ∫ y, Y y ^ 2 ∂μ₂ = 0) :
    ∫ ω, ((a : ℂ) * X ω.1 + (b : ℂ) * Y ω.2) ^ 2 ∂(μ₁.prod μ₂) = 0 := by
  have e : ∀ ω : Ω₁ × Ω₂, ((a : ℂ) * X ω.1 + (b : ℂ) * Y ω.2) ^ 2 =
      (a : ℂ) ^ 2 * X ω.1 ^ 2 + (b : ℂ) ^ 2 * Y ω.2 ^ 2 + (2 * (a : ℂ) * b) * (X ω.1 * Y ω.2) := by
    intro ω
    ring
  simp only [e]
  have i1 : Integrable (fun ω : Ω₁ × Ω₂ => (a : ℂ) ^ 2 * X ω.1 ^ 2) (μ₁.prod μ₂) :=
    (hX.int_sq.comp_fst μ₂).const_mul _
  have i2 : Integrable (fun ω : Ω₁ × Ω₂ => (b : ℂ) ^ 2 * Y ω.2 ^ 2) (μ₁.prod μ₂) :=
    (hY.int_sq.comp_snd μ₁).const_mul _
  have i3 : Integrable (fun ω : Ω₁ × Ω₂ => X ω.1 * Y ω.2) (μ₁.prod μ₂) :=
    Integrable.mul_prod hX.int1 hY.int1
  have i12 : Integrable (fun ω : Ω₁ × Ω₂ => (a : ℂ) ^ 2 * X ω.1 ^ 2 + (b : ℂ) ^ 2 * Y ω.2 ^ 2)
      (μ₁.prod μ₂) := i1.add i2
  rw [integral_add i12 (i3.const_mul _), integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_prod_mul X Y,
    OU_int_fst (μ₂ := μ₂) (fun x => X x ^ 2), OU_int_snd (μ₁ := μ₁) (fun y => Y y ^ 2),
    hX.mean, hY.mean, hX2, hY2]
  simp

/-! ### The array law -/

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private lemma OU_measurable_wig (n : ℕ) (i j : Fin n) :
    Measurable fun c : Coords n => wig n c i j := by
  unfold wig
  by_cases h1 : i = j
  · simp only [h1, ite_true]
    exact measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_pi_apply j).comp measurable_fst))
  · by_cases h2 : i < j
    · simp only [h1, h2, ite_true, ite_false]
      exact measurable_const.mul
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))
    · simp only [h1, h2, ite_false]
      exact measurable_const.mul ((continuous_star (R := ℂ)).measurable.comp
        ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)))

/-- Every entry of `blockH D N w` is a measurable function of `w`. -/
private lemma OU_measurable_blockH (D N : ℕ) (p q : Idx D N) :
    Measurable fun w : Fin D → Coords N => blockH D N w p q := by
  by_cases h : p.1 = q.1
  · simp only [blockH, h, ↓reduceIte]
    exact (OU_measurable_wig N p.2 q.2).comp (measurable_pi_apply q.1)
  · simp only [blockH, h, ↓reduceIte]
    exact measurable_const

/-- The array of coordinates `blockEmb D N w` is a measurable function of `w`. -/
private lemma OU_measurable_blockEmb (D N : ℕ) : Measurable (blockEmb D N) := by
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.mpr fun k => ?_
    exact measurable_const.mul ((measurable_pi_apply _).comp
      (measurable_fst.comp (measurable_pi_apply _)))
  · refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun l => ?_
    by_cases h : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1
    · simp only [h, ↓reduceIte]
      exact measurable_const.mul ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        (measurable_snd.comp (measurable_pi_apply _))))
    · simp only [h, ↓reduceIte]
      exact measurable_const

/-- The map `(w, W) ↦ e^{-t/2} blockEmb w + √(1 - e^{-t}) W` of the law `ouLaw` is measurable. -/
private lemma OU_measurable_phi0 (D N : ℕ) (t : ℝ) :
    Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.exp (-t / 2) • blockEmb D N p.1 + Real.sqrt (1 - Real.exp (-t)) • p.2 := by
  have h1 : Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.exp (-t / 2) • blockEmb D N p.1 :=
    ((OU_measurable_blockEmb D N).comp measurable_fst).const_smul (Real.exp (-t / 2))
  have h2 : Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.sqrt (1 - Real.exp (-t)) • p.2 :=
    measurable_snd.const_smul (Real.sqrt (1 - Real.exp (-t)))
  exact h1.add h2

/-- The array `Matrix.of.symm ((wig (D N) c).submatrix _ _)` is a measurable function of the
coordinates `c`. -/
private lemma OU_measurable_psi (D N : ℕ) :
    Measurable fun c : Coords (D * N) => Matrix.of.symm
      ((wig (D * N) c).submatrix finProdFinEquiv finProdFinEquiv) :=
  measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q =>
    OU_measurable_wig (D * N) (finProdFinEquiv p) (finProdFinEquiv q)

/-- The entries of `H_t` in the law (4.3) [eq:eq_in_law_H]: `e^{-t/2} (blockH w)_{pq}` plus
`√(1 - e^{-t})` times the entry `(fPFE p, fPFE q)` of the GUE `wig (DN) W`, where
`fPFE = finProdFinEquiv`. -/
private def OU_Θ (D N : ℕ) (t : ℝ) (ω : (Fin D → Coords N) × Coords (D * N)) :
    Idx D N → Idx D N → ℂ := fun p q =>
  ((Real.exp (-t / 2) : ℝ) : ℂ) * blockH D N ω.1 p q +
    ((Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ) *
      wig (D * N) ω.2 (finProdFinEquiv p) (finProdFinEquiv q)

/-- `OU_Θ` is measurable. -/
private lemma OU_measurable_Θ (D N : ℕ) (t : ℝ) : Measurable (OU_Θ D N t) :=
  measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q =>
    (measurable_const.mul ((OU_measurable_blockH D N p q).comp measurable_fst)).add
      (measurable_const.mul
        ((OU_measurable_wig (D * N) (finProdFinEquiv p) (finProdFinEquiv q)).comp measurable_snd))

/-- The law (4.3) [eq:eq_in_law_H] of `H_t` of (4.1) [defVt] as a law on arrays indexed by
`Idx D N`. -/
def ouMatLaw (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) : Measure (Idx D N → Idx D N → ℂ) :=
  (ouLaw D N L t).map fun c => Matrix.of.symm
    ((wig (D * N) c).submatrix finProdFinEquiv finProdFinEquiv)

/-- The law `ouMatLaw` is the image of `blockLaw ⊗ gueLaw (DN)` under `OU_Θ`, by `wig_add`,
`wig_smul` and `wig_blockEmb`. -/
private lemma OU_ouMatLaw_eq (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) :
    ouMatLaw D N L t = ((blockLaw D N L).prod (gueLaw (D * N))).map (OU_Θ D N t) := by
  unfold ouMatLaw ouLaw
  rw [Measure.map_map (OU_measurable_psi D N) (OU_measurable_phi0 D N t)]
  congr 1
  funext ω
  funext p q
  change wig (D * N) (Real.exp (-t / 2) • blockEmb D N ω.1 + Real.sqrt (1 - Real.exp (-t)) • ω.2)
      (finProdFinEquiv p) (finProdFinEquiv q) = OU_Θ D N t ω p q
  rw [wig_add, wig_smul, wig_smul]
  have h := congrFun (congrFun (wig_blockEmb D N ω.1) p) q
  simp only [Matrix.submatrix_apply] at h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h, OU_Θ]

/-! ### Hermitian symmetry -/

/-- The Wigner matrix `wig n c` is Hermitian. -/
private lemma OU_wig_isHermitian (n : ℕ) (c : Coords n) : (wig n c).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [wig, star_mul', Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.not_gt, h.ne']
  · subst h
    simp
  · simp [h, h.ne, h.not_gt, h.ne']

/-- `blockH D N w` is Hermitian. -/
private lemma OU_blockH_isHermitian (D N : ℕ) (w : Fin D → Coords N) :
    (blockH D N w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  by_cases h : p.1 = q.1
  · simp only [blockH, h, ↓reduceIte]
    exact (OU_wig_isHermitian N (w q.1)).apply p.2 q.2
  · have h' : ¬ q.1 = p.1 := fun e => h e.symm
    simp [blockH, h, h']

/-- The set of Hermitian arrays is measurable. -/
private lemma OU_measurableSet_herm (D N : ℕ) :
    MeasurableSet {h : Idx D N → Idx D N → ℂ | (Matrix.of h).IsHermitian} := by
  have : {h : Idx D N → Idx D N → ℂ | (Matrix.of h).IsHermitian} =
      ⋂ i, ⋂ j, {h | star (h j i) = h i j} := by
    ext h
    simp [Matrix.IsHermitian.ext_iff]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    measurableSet_eq_fun ((continuous_star (R := ℂ)).measurable.comp
      ((measurable_pi_apply i).comp (measurable_pi_apply j)))
      ((measurable_pi_apply j).comp (measurable_pi_apply i))

/-- Every array `OU_Θ D N t ω` is Hermitian. -/
private lemma OU_Θ_isHermitian (D N : ℕ) (t : ℝ) (ω : (Fin D → Coords N) × Coords (D * N)) :
    (Matrix.of (OU_Θ D N t ω)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  have hb := (OU_blockH_isHermitian D N ω.1).apply p q
  have hw := (OU_wig_isHermitian (D * N) ω.2).apply (finProdFinEquiv p) (finProdFinEquiv q)
  simp only [OU_Θ, Matrix.of_apply, star_add, star_mul', hb, hw, Complex.star_def,
    Complex.conj_ofReal]

/-! ### Moment facts of the two summands -/

/-- The scaling `n^{-1/2}` of `wig n`. -/
private abbrev OU_c (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ))

/-- `(n^{-1/2})² = n⁻¹`. -/
private lemma OU_c_sq (n : ℕ) : OU_c n ^ 2 = (n : ℝ)⁻¹ := by
  rw [OU_c, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num [Real.rpow_neg_one]

/-- `(n^{-1/2})^k = n^{-k/2}`. -/
private lemma OU_c_pow (n k : ℕ) : OU_c n ^ k = (n : ℝ) ^ (-((k : ℝ) / 2)) := by
  rw [OU_c, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

/-- The entries of the GUE `wig n` under `gueLaw n`: centred, `E|·|² = 1/n`, `E (·)² = 0` off the
diagonal, and `E|·|^j ≤ m_j n^{-j/2}`. -/
private lemma OU_Y_facts (n : ℕ) (k l : Fin n) :
    OU_Facts (gueLaw n) (fun W => wig n W k l) ∧
      ∫ W, ‖wig n W k l‖ ^ 2 ∂(gueLaw n) = (n : ℝ)⁻¹ ∧
      (k ≠ l → ∫ W, (wig n W k l) ^ 2 ∂(gueLaw n) = 0) ∧
      ∀ j : ℕ, ∫ W, ‖wig n W k l‖ ^ j ∂(gueLaw n) ≤ (n : ℝ) ^ (-((j : ℝ) / 2)) * OU_m j := by
  obtain ⟨hU, hU2⟩ := OU_unit_entry n k l
  have hnorm : ∀ (j : ℕ) (W : Coords n), ‖((OU_c n : ℝ) : ℂ) * OU_U n k l W‖ ^ j =
      OU_c n ^ j * ‖OU_U n k l W‖ ^ j := by
    intro j W
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), mul_pow]
  refine ⟨hU.facts.const_mul (OU_c n), ?_, fun h => ?_, fun j => ?_⟩
  · change ∫ W, ‖((OU_c n : ℝ) : ℂ) * OU_U n k l W‖ ^ 2 ∂(gueLaw n) = (n : ℝ)⁻¹
    simp only [hnorm]
    rw [integral_const_mul, hU.var, mul_one, OU_c_sq]
  · change ∫ W, (((OU_c n : ℝ) : ℂ) * OU_U n k l W) ^ 2 ∂(gueLaw n) = 0
    simp only [mul_pow]
    rw [integral_const_mul, hU2 h, mul_zero]
  · change ∫ W, ‖((OU_c n : ℝ) : ℂ) * OU_U n k l W‖ ^ j ∂(gueLaw n) ≤ _
    simp only [hnorm]
    rw [integral_const_mul, OU_c_pow]
    exact mul_le_mul_of_nonneg_left (hU.moments j) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The entries of `blockH` under `blockLaw`, from `llClass_blockH`: centred, with variance
`varProf D N 1`, vanishing pseudo-variance off the diagonal, and `E|·|^k ≤ C_k N^{-k/2}`. -/
private lemma OU_X_facts (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (p q : Idx D N) :
    OU_Facts (blockLaw D N L) (fun w => blockH D N w p q) ∧
      ∫ w, ‖blockH D N w p q‖ ^ 2 ∂(blockLaw D N L) = varProf D N 1 p q ∧
      (p ≠ q → ∫ w, (blockH D N w p q) ^ 2 ∂(blockLaw D N L) = 0) ∧
      ∀ k : ℕ, ∫ w, ‖blockH D N w p q‖ ^ k ∂(blockLaw D N L) ≤
        C k * (N : ℝ) ^ (-((k : ℝ) / 2)) := by
  have hf : Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) :=
    measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => OU_measurable_blockH D N p q
  have hmp : MeasurePreserving (fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w))
      (blockLaw D N L) ((blockLaw D N L).map fun w => Matrix.of.symm (blockH D N w)) :=
    ⟨hf, rfl⟩
  have hL := llClass_blockH D N C L
  have hcont : ∀ (F : ℂ → ℝ), Continuous F →
      AEStronglyMeasurable (fun h : Idx D N → Idx D N → ℂ => F (h p q))
        ((blockLaw D N L).map fun w => Matrix.of.symm (blockH D N w)) := fun F hF =>
    (hF.comp ((continuous_apply q).comp (continuous_apply p))).aestronglyMeasurable
  refine ⟨⟨OU_measurable_blockH D N p q, fun k => ?_, ?_⟩, ?_, fun hpq => ?_, fun k => ?_⟩
  · exact (hmp.integrable_comp (hcont (fun z => ‖z‖ ^ k) (by fun_prop))).mpr (hL.integrable k p q)
  · exact (OU_integral_comp hmp (G := fun h : Idx D N → Idx D N → ℂ => h p q)
      ((continuous_apply q).comp (continuous_apply p)).aestronglyMeasurable).trans (hL.mean p q)
  · exact (OU_integral_comp hmp (G := fun h : Idx D N → Idx D N → ℂ => ‖h p q‖ ^ 2)
      (hcont (fun z => ‖z‖ ^ 2) (by fun_prop))).trans (hL.var p q)
  · exact (OU_integral_comp hmp (G := fun h : Idx D N → Idx D N → ℂ => h p q ^ 2)
      (((continuous_apply q).comp (continuous_apply p)).pow 2).aestronglyMeasurable).trans
        (hL.pseudo p q hpq)
  · exact (OU_integral_comp hmp (G := fun h : Idx D N → Idx D N → ℂ => ‖h p q‖ ^ k)
      (hcont (fun z => ‖z‖ ^ k) (by fun_prop))).le.trans (hL.moments k p q)

/-! ### Independence of the entries -/

/-- `finProdFinEquiv` is monotone for the lexicographic order of `Idx D N`, so that the `toLex`
pairs `p ≤ q` of `Idx D N` correspond to pairs `k ≤ l` of `Fin (D N)`. -/
private lemma OU_fPFE_le {D N : ℕ} {p q : Idx D N} (h : toLex p ≤ toLex q) :
    finProdFinEquiv p ≤ finProdFinEquiv q := by
  rw [Fin.le_def]
  simp only [finProdFinEquiv_apply_val]
  rcases Prod.Lex.toLex_le_toLex.mp h with h1 | ⟨h1, h2⟩
  · have h3 : (p.1 : ℕ) + 1 ≤ q.1 := h1
    have h4 := Nat.mul_le_mul_left N h3
    rw [Nat.mul_add, mul_one] at h4
    have := p.2.isLt
    omega
  · rw [h1]
    have : (p.2 : ℕ) ≤ q.2 := h2
    omega

/-- The entries `(k, l)`, `k ≤ l`, of the GUE `wig (DN)`, indexed by the `toLex`-ordered pairs of
`Idx D N` through `finProdFinEquiv`, are independent under `gueLaw (DN)`. -/
private lemma OU_iIndep_gue (D N : ℕ) :
    iIndepFun (fun (q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2}) (W : Coords (D * N)) =>
      wig (D * N) W (finProdFinEquiv q.val.1) (finProdFinEquiv q.val.2)) (gueLaw (D * N)) := by
  let κ : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2} →
      Fin (D * N) ⊕ (Fin (D * N) × Fin (D * N)) :=
    fun q => if finProdFinEquiv q.val.1 = finProdFinEquiv q.val.2 then
      Sum.inl (finProdFinEquiv q.val.1) else
      Sum.inr (finProdFinEquiv q.val.1, finProdFinEquiv q.val.2)
  have hκ : Function.Injective κ := by
    intro q q' h
    have key : finProdFinEquiv q.val.1 = finProdFinEquiv q'.val.1 ∧
        finProdFinEquiv q.val.2 = finProdFinEquiv q'.val.2 := by
      by_cases h1 : finProdFinEquiv q.val.1 = finProdFinEquiv q.val.2 <;>
        by_cases h1' : finProdFinEquiv q'.val.1 = finProdFinEquiv q'.val.2 <;>
        simp only [κ, h1, h1', ↓reduceIte, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq,
          Prod.mk.injEq] at h
      · exact ⟨h1.trans (h.trans h1'.symm), h⟩
      · exact h
    exact Subtype.ext (Prod.ext (finProdFinEquiv.injective key.1)
      (finProdFinEquiv.injective key.2))
  have h := ((OU_iIndep_coords (D * N) (gaussianReal 0 1) (cGauss : Measure ℂ)).precomp hκ).comp
    (fun _ => fun z : ℂ => ((OU_c (D * N) : ℝ) : ℂ) * z)
    (fun _ => measurable_const.mul measurable_id)
  unfold gueLaw
  convert h using 1
  funext q W
  obtain ⟨⟨p, p'⟩, hle⟩ := q
  have hkl : finProdFinEquiv p ≤ finProdFinEquiv p' := OU_fPFE_le hle
  by_cases h1 : finProdFinEquiv p = finProdFinEquiv p'
  · have hκq : κ ⟨(p, p'), hle⟩ = Sum.inl (finProdFinEquiv p) := by
      simp only [κ, h1, ↓reduceIte]
    simp only [Function.comp_apply, hκq, Sum.elim_inl]
    simp only [wig, h1, ↓reduceIte, OU_c]
  · have h2 : finProdFinEquiv p < finProdFinEquiv p' := lt_of_le_of_ne hkl h1
    have hκq : κ ⟨(p, p'), hle⟩ = Sum.inr (finProdFinEquiv p, finProdFinEquiv p') := by
      simp only [κ, h1, ↓reduceIte]
    simp only [Function.comp_apply, hκq, Sum.elim_inr]
    simp only [wig, h1, h2, ↓reduceIte, OU_c]

/-- The entries `h_{pq}` of `H_t`, `p q : Idx D N`, with `toLex p ≤ toLex q`, are independent under
the law `ouMatLaw`, as functions of the pair `(blockH w, W)` of independent arrays. -/
private lemma OU_iIndep_Θ (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) :
    iIndepFun (fun (q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2})
      (h : Idx D N → Idx D N → ℂ) => h q.val.1 q.val.2)
      (((blockLaw D N L).prod (gueLaw (D * N))).map (OU_Θ D N t)) := by
  have hf : Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) :=
    measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => OU_measurable_blockH D N p q
  have hmp : MeasurePreserving (fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w))
      (blockLaw D N L) ((blockLaw D N L).map fun w => Matrix.of.symm (blockH D N w)) :=
    ⟨hf, rfl⟩
  have hu : iIndepFun (fun (q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2})
      (w : Fin D → Coords N) => blockH D N w q.val.1 q.val.2) (blockLaw D N L) :=
    OU_iIndepFun_comp_mp hmp
      (f := fun (q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2})
        (h : Idx D N → Idx D N → ℂ) => h q.val.1 q.val.2)
      (fun q => (measurable_pi_apply q.val.2).comp (measurable_pi_apply q.val.1))
      (llClass_blockH D N C L).indep
  have h := OU_iIndep_pair (μ₁ := blockLaw D N L) (μ₂ := gueLaw (D * N))
    (u := fun (q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2}) (w : Fin D → Coords N) =>
      blockH D N w q.val.1 q.val.2)
    (v := fun (q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2}) (W : Coords (D * N)) =>
      wig (D * N) W (finProdFinEquiv q.val.1) (finProdFinEquiv q.val.2))
    (fun q => OU_measurable_blockH D N _ _)
    (fun q => OU_measurable_wig (D * N) _ _) hu (OU_iIndep_gue D N)
    ((Real.exp (-t / 2) : ℝ) : ℂ) ((Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ)
  exact OU_iIndepFun_map (OU_measurable_Θ D N t)
    (fun q => (measurable_pi_apply q.val.2).comp (measurable_pi_apply q.val.1)) h

/-- The entry `(p, q)` of `H_t`: centred, variance `varProf D N e^{-t}`, vanishing pseudo-variance
off the diagonal, and `E|·|^k ≤ 2^k (|C_k| + m_k) N^{-k/2}`, for `t ≥ 0`. -/
private lemma OU_entry (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (ht : 0 ≤ t)
    (p q : Idx D N) :
    OU_Facts ((blockLaw D N L).prod (gueLaw (D * N))) (fun ω => OU_Θ D N t ω p q) ∧
      ∫ ω, ‖OU_Θ D N t ω p q‖ ^ 2 ∂((blockLaw D N L).prod (gueLaw (D * N))) =
        varProf D N (Real.exp (-t)) p q ∧
      (p ≠ q → ∫ ω, (OU_Θ D N t ω p q) ^ 2 ∂((blockLaw D N L).prod (gueLaw (D * N))) = 0) ∧
      ∀ k : ℕ, ∫ ω, ‖OU_Θ D N t ω p q‖ ^ k ∂((blockLaw D N L).prod (gueLaw (D * N))) ≤
        (2 ^ k * (|C k| + OU_m k)) * (N : ℝ) ^ (-((k : ℝ) / 2)) := by
  obtain ⟨hX, hXv, hXp, hXm⟩ := OU_X_facts D N L p q
  obtain ⟨hY, hYv, hYp, hYm⟩ := OU_Y_facts (D * N) (finProdFinEquiv p) (finProdFinEquiv q)
  have hexp : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hα : |Real.exp (-t / 2)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hβ : |Real.sqrt (1 - Real.exp (-t))| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.sqrt_le_one.mpr ?_
    linarith [Real.exp_pos (-t)]
  have hα2 : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hβ2 : Real.sqrt (1 - Real.exp (-t)) ^ 2 = 1 - Real.exp (-t) :=
    Real.sq_sqrt (by linarith)
  obtain ⟨hF, hFm⟩ := OU_comb_facts hX hY _ _ hα hβ
  refine ⟨hF, ?_, fun hpq => ?_, fun k => ?_⟩
  · have := OU_comb_var hX hY (Real.exp (-t / 2)) (Real.sqrt (1 - Real.exp (-t)))
    refine this.trans ?_
    rw [hXv, hYv, hα2, hβ2]
    simp only [varProf, Nat.cast_mul]
    ring
  · have hne : finProdFinEquiv p ≠ finProdFinEquiv q := fun h => hpq (finProdFinEquiv.injective h)
    exact OU_comb_pseudo hX hY (Real.exp (-t / 2)) (Real.sqrt (1 - Real.exp (-t)))
      (hXp hpq) (hYp hne)
  · refine (hFm k).trans ?_
    have hr0 : 0 ≤ (N : ℝ) ^ (-((k : ℝ) / 2)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos p.2
    have hDN : (N : ℝ) ≤ ((D * N : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left N (Fin.pos p.1)
    have hk : -((k : ℝ) / 2) ≤ 0 := by
      have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      linarith
    have hs : ((D * N : ℕ) : ℝ) ^ (-((k : ℝ) / 2)) ≤ (N : ℝ) ^ (-((k : ℝ) / 2)) :=
      Real.rpow_le_rpow_of_nonpos hN hDN hk
    have hm0 : 0 ≤ OU_m k := by
      have := OU_m_parts k
      unfold OU_m
      linarith [this.1, this.2]
    have hC : C k ≤ |C k| := le_abs_self _
    have h1 := add_le_add (hXm k) (hYm k)
    have h2 : C k * (N : ℝ) ^ (-((k : ℝ) / 2)) +
        ((D * N : ℕ) : ℝ) ^ (-((k : ℝ) / 2)) * OU_m k ≤
        (|C k| + OU_m k) * (N : ℝ) ^ (-((k : ℝ) / 2)) := by
      nlinarith [mul_le_mul_of_nonneg_right hC hr0, mul_le_mul_of_nonneg_right hs hm0]
    calc 2 ^ k * ((∫ x, ‖blockH D N x p q‖ ^ k ∂(blockLaw D N L)) +
        ∫ y, ‖wig (D * N) y (finProdFinEquiv p) (finProdFinEquiv q)‖ ^ k ∂(gueLaw (D * N)))
        ≤ 2 ^ k * ((|C k| + OU_m k) * (N : ℝ) ^ (-((k : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = (2 ^ k * (|C k| + OU_m k)) * (N : ℝ) ^ (-((k : ℝ) / 2)) := by ring

/-- Integrals of a continuous function of the entry `(i, j)` against the law of the array `Θ ω`
equal the integrals of the same function of `Θ ω i j` against the underlying measure. -/
private lemma OU_integral_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D N : ℕ}
    {Θ : Ω → Idx D N → Idx D N → ℂ} (hΘ : Measurable Θ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (i j : Idx D N) (F : ℂ → E) (hF : Continuous F) :
    ∫ h, F (h i j) ∂(P.map Θ) = ∫ ω, F (Θ ω i j) ∂P :=
  integral_map hΘ.aemeasurable
    (hF.comp ((continuous_apply j).comp (continuous_apply i))).aestronglyMeasurable

/-- The law (4.3) [eq:eq_in_law_H] of `H_t` is in the class with `θ = e^{-t}`, for every
`t ≥ 0`, with moment constants that depend on `C` only. -/
theorem llClass_ouLaw (D : ℕ) (C : ℕ → ℝ) :
    ∃ C' : ℕ → ℝ, ∀ (N : ℕ) (L : EntryLaws C) (t : ℝ), 0 ≤ t →
      LLClass D N C' (Real.exp (-t)) (ouMatLaw D N L t) := by
  refine ⟨fun k => 2 ^ k * (|C k| + OU_m k), ?_⟩
  intro N L t ht
  rw [OU_ouMatLaw_eq]
  have hΘ := OU_measurable_Θ D N t
  have hcm : ∀ (k : ℕ) (i j : Idx D N), AEStronglyMeasurable
      (fun h : Idx D N → Idx D N → ℂ => ‖h i j‖ ^ k)
      (((blockLaw D N L).prod (gueLaw (D * N))).map (OU_Θ D N t)) := fun k i j =>
    (((continuous_norm.comp ((continuous_apply j).comp (continuous_apply i))).pow k)
      ).aestronglyMeasurable
  refine ⟨inferInstance, ?_, OU_iIndep_Θ D N L t,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [ae_map_iff hΘ.aemeasurable (OU_measurableSet_herm D N)]
    exact Eventually.of_forall (OU_Θ_isHermitian D N t)
  · intro k i j
    exact (integrable_map_measure (hcm k i j) hΘ.aemeasurable).mpr
      ((OU_entry D N L t ht i j).1.integrable k)
  · intro i j
    rw [OU_integral_map hΘ i j (fun z : ℂ => z) continuous_id]
    exact (OU_entry D N L t ht i j).1.mean
  · intro i j
    rw [OU_integral_map hΘ i j (fun z : ℂ => ‖z‖ ^ 2) (continuous_norm.pow 2)]
    exact (OU_entry D N L t ht i j).2.1
  · intro i j hij
    rw [OU_integral_map hΘ i j (fun z : ℂ => z ^ 2) (continuous_pow 2)]
    exact (OU_entry D N L t ht i j).2.2.1 hij
  · intro k i j
    rw [OU_integral_map hΘ i j (fun z : ℂ => ‖z‖ ^ k) (continuous_norm.pow k)]
    exact (OU_entry D N L t ht i j).2.2.2 k

end RBMTransitionEdge

end
