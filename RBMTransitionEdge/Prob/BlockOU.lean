module

public import RBMTransitionEdge.LocalLaw.OU
public import RBMTransitionEdge.Prob.MomentMatch

@[expose] public section

/-!
# The block-OU law and class membership along the flow

The single-time law (3.13) [eq:Gauss_div] of the flow from any member, its membership in the class,
the entry laws (3.34) [Gcom_a], Lindeberg hybrids for Lemma 3.13 [main_lemma_com], and the law
identities of `ouMatLaw` behind Lemma 3.3 [key_lemma_delocalized_eigenvector].
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The law of `e^{-s/2} h + √(1 - e^{-s}) H^{(g)}` with `h ∼ μ` and an independent
block-diagonal GUE `H^{(g)}`: the single-time law of the flow (3.12) [eq:Ht] with the drift on
all entries, (3.13) [eq:Gauss_div] for a block-diagonal start. -/
def blockOULaw (D N : ℕ) (μ : Measure (Idx D N → Idx D N → ℂ)) (s : ℝ) :
    Measure (Idx D N → Idx D N → ℂ) :=
  (μ.prod (gueBlocks D N)).map fun p =>
    Real.exp (-s / 2) • p.1 + Real.sqrt (1 - Real.exp (-s)) • Matrix.of.symm (blockH D N p.2)

/-- The hybrid array of the Lindeberg replacement in Lemma 3.13 [main_lemma_com]: the entries
`(i, j)` and `(j, i)` come from `h` when `(i, j) ∈ Γ` or `(j, i) ∈ Γ`, from `h'` otherwise. -/
def hybridArr {D N : ℕ} (Γ : Set (Idx D N × Idx D N))
    (p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) : Idx D N → Idx D N → ℂ :=
  fun i j => if (i, j) ∈ Γ ∨ (j, i) ∈ Γ then p.1 i j else p.2 i j


/-! ### Independence tools -/

/-- Two independent families of independent complex random variables form one independent
family, indexed by the disjoint sum. -/
private lemma BOU_iIndepFun_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
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
private lemma BOU_iIndepFun_comp_mp {Ω Ω' ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
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
private lemma BOU_iIndepFun_map {Ω Ω' ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
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

/-- Two independent families, one on each factor of a product space, give the independent family
of the linear combinations `a u_q + b v_q`. -/
private lemma BOU_iIndep_pair {Ω₁ Ω₂ ι : Type*} [Finite ι] [MeasurableSpace Ω₁]
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
private lemma BOU_pow_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  refine (add_pow_le ha hb k).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)

/-- Every absolute moment of a real Gaussian law is finite. -/
private lemma BOU_G_int (v : NNReal) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
  have := (memLp_id_gaussianReal' (μ := 0) (v := v) ((k : ℕ) : ENNReal)
    (by simp)).integrable_norm_pow'
  simpa using this

/-- The identity is integrable against a real Gaussian law. -/
private lemma BOU_G_int1 (v : NNReal) : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal' (μ := 0) (v := v) 1 (by simp)).integrable le_rfl

/-- The second moment of `N(0, v)` is `v`. -/
private lemma BOU_G_sq (v : NNReal) : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- The law `cGauss` as the image of `N(0,1/2) ⊗ N(0,1/2)` under `(x, y) ↦ x + y i`. -/
private lemma BOU_cGauss_eq : (cGauss : Measure ℂ) =
    ((gaussianReal 0 (1 / 2 : NNReal)).prod (gaussianReal 0 (1 / 2 : NNReal))).map
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := rfl

/-- The map `(x, y) ↦ x + y i` is measurable. -/
private lemma BOU_measurable_phi :
    Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop

/-- Integrals against `cGauss` of a continuous function are integrals against the product of two
real Gaussians. -/
private lemma BOU_c_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E)
    (hf : Continuous f) :
    ∫ z, f z ∂(cGauss : Measure ℂ) =
      ∫ p : ℝ × ℝ, f ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
        ∂((gaussianReal 0 (1 / 2 : NNReal)).prod (gaussianReal 0 (1 / 2 : NNReal))) := by
  rw [BOU_cGauss_eq]
  exact integral_map BOU_measurable_phi.aemeasurable hf.aestronglyMeasurable

/-- Every absolute moment of `cGauss` is finite. -/
private lemma BOU_c_int (k : ℕ) : Integrable (fun z : ℂ => ‖z‖ ^ k) (cGauss : Measure ℂ) := by
  set G := gaussianReal 0 (1 / 2 : NNReal) with hG
  have hc : Continuous (fun z : ℂ => ‖z‖ ^ k) := by fun_prop
  rw [BOU_cGauss_eq, integrable_map_measure hc.aestronglyMeasurable
    BOU_measurable_phi.aemeasurable]
  refine Integrable.mono' (g := fun p : ℝ × ℝ => 2 ^ k * (|p.1| ^ k + |p.2| ^ k)) ?_ ?_ ?_
  · exact (((BOU_G_int _ k).comp_fst G).add ((BOU_G_int _ k).comp_snd G)).const_mul _
  · exact (hc.measurable.comp BOU_measurable_phi).aestronglyMeasurable
  · filter_upwards with p
    have h1 : ‖(p.1 : ℂ) + (p.2 : ℂ) * Complex.I‖ ≤ |p.1| + |p.2| := by
      refine (norm_add_le _ _).trans ?_
      simp
    have h2 := BOU_pow_add_le (abs_nonneg p.1) (abs_nonneg p.2) k
    simp only [Function.comp, Real.norm_eq_abs, abs_pow, abs_norm]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 k).trans h2

/-- The second moment `x²` is integrable against a real Gaussian law. -/
private lemma BOU_G_int_sq (v : NNReal) : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
  simpa [sq_abs] using BOU_G_int v 2

/-- `cGauss` has mean zero. -/
private lemma BOU_c_mean : ∫ z : ℂ, z ∂(cGauss : Measure ℂ) = 0 := by
  set G := gaussianReal 0 (1 / 2 : NNReal) with hG
  rw [BOU_c_integral (fun z => z) continuous_id]
  have h1 : Integrable (fun p : ℝ × ℝ => (p.1 : ℂ)) (G.prod G) :=
    ((BOU_G_int1 _).comp_fst G).ofReal
  have h2 : Integrable (fun p : ℝ × ℝ => (p.2 : ℂ) * Complex.I) (G.prod G) :=
    (((BOU_G_int1 _).comp_snd G).ofReal).mul_const _
  rw [integral_add h1 h2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_fun_fst (fun x : ℝ => x), integral_fun_snd (fun x : ℝ => x)]
  simp [hG]

/-- `E|z|² = 1` for `cGauss`. -/
private lemma BOU_c_var : ∫ z : ℂ, ‖z‖ ^ 2 ∂(cGauss : Measure ℂ) = 1 := by
  set G := gaussianReal 0 (1 / 2 : NNReal) with hG
  rw [BOU_c_integral (fun z => ‖z‖ ^ 2) (by fun_prop)]
  have e : ∀ p : ℝ × ℝ, ‖(p.1 : ℂ) + (p.2 : ℂ) * Complex.I‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    intro p
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  simp only [e]
  rw [integral_add ((BOU_G_int_sq _).comp_fst G) ((BOU_G_int_sq _).comp_snd G),
    integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2), hG, BOU_G_sq]
  norm_num

/-- `E z² = 0` for `cGauss`. -/
private lemma BOU_c_pseudo : ∫ z : ℂ, z ^ 2 ∂(cGauss : Measure ℂ) = 0 := by
  set G := gaussianReal 0 (1 / 2 : NNReal) with hG
  rw [BOU_c_integral (fun z => z ^ 2) (by fun_prop)]
  have e : ∀ p : ℝ × ℝ, ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ^ 2 =
      ((p.1 ^ 2 : ℝ) : ℂ) - ((p.2 ^ 2 : ℝ) : ℂ) + (2 * Complex.I) * ((p.1 : ℂ) * (p.2 : ℂ)) := by
    intro p
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [e]
  have h1 : Integrable (fun p : ℝ × ℝ => ((p.1 ^ 2 : ℝ) : ℂ)) (G.prod G) :=
    ((BOU_G_int_sq _).comp_fst G).ofReal
  have h2 : Integrable (fun p : ℝ × ℝ => ((p.2 ^ 2 : ℝ) : ℂ)) (G.prod G) :=
    ((BOU_G_int_sq _).comp_snd G).ofReal
  have h3 : Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) * (p.2 : ℂ)) (G.prod G) :=
    Integrable.mul_prod (BOU_G_int1 _).ofReal (BOU_G_int1 _).ofReal
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
private def BOU_m (k : ℕ) : ℝ :=
  (∫ x : ℝ, |x| ^ k ∂(gaussianReal 0 1)) + ∫ z : ℂ, ‖z‖ ^ k ∂(cGauss : Measure ℂ)

/-- A centred complex random variable with all absolute moments finite. -/
private structure BOU_Facts {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℂ) : Prop where
  /-- `X` is measurable. -/
  meas : Measurable X
  /-- Every absolute moment of `X` is finite. -/
  integrable : ∀ k : ℕ, Integrable (fun ω => ‖X ω‖ ^ k) μ
  /-- `E X = 0`. -/
  mean : ∫ ω, X ω ∂μ = 0

/-- A unit-variance noise whose absolute moments are bounded by `m_k`. -/
private structure BOU_Unit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ) : Prop where
  /-- The basic facts. -/
  facts : BOU_Facts μ Z
  /-- `E|Z|² = 1`. -/
  var : ∫ ω, ‖Z ω‖ ^ 2 ∂μ = 1
  /-- `E|Z|^k ≤ m_k`. -/
  moments : ∀ k : ℕ, ∫ ω, ‖Z ω‖ ^ k ∂μ ≤ BOU_m k

/-- The absolute moments of the standard real Gaussian law and of `cGauss` are nonnegative. -/
private lemma BOU_m_parts (k : ℕ) :
    0 ≤ ∫ x : ℝ, |x| ^ k ∂(gaussianReal 0 1) ∧ 0 ≤ ∫ z : ℂ, ‖z‖ ^ k ∂(cGauss : Measure ℂ) :=
  ⟨integral_nonneg fun x => by positivity, integral_nonneg fun z => by positivity⟩

/-- The standard real Gaussian, as a complex noise. -/
private lemma BOU_unit_real : BOU_Unit (gaussianReal 0 1) (fun x : ℝ => (x : ℂ)) := by
  refine ⟨⟨Complex.measurable_ofReal, fun k => ?_, ?_⟩, ?_, fun k => ?_⟩
  · simpa [Complex.norm_real] using BOU_G_int 1 k
  · rw [integral_complex_ofReal (f := fun x : ℝ => x)]
    simp
  · simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [BOU_G_sq]
    simp
  · simp only [Complex.norm_real, Real.norm_eq_abs]
    unfold BOU_m
    linarith [(BOU_m_parts k).2]

/-- The standard complex Gaussian `cGauss`, as a noise. -/
private lemma BOU_unit_c : BOU_Unit (cGauss : Measure ℂ) (fun z : ℂ => z) := by
  refine ⟨⟨measurable_id, BOU_c_int, BOU_c_mean⟩, BOU_c_var, fun k => ?_⟩
  unfold BOU_m
  linarith [(BOU_m_parts k).1]


/-- `X` is integrable. -/
private lemma BOU_Facts.int1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℂ}
    (h : BOU_Facts μ X) : Integrable X μ :=
  (integrable_norm_iff h.meas.aestronglyMeasurable).mp (by simpa using h.integrable 1)

/-- `X²` is integrable. -/
private lemma BOU_Facts.int_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℂ}
    (h : BOU_Facts μ X) : Integrable (fun ω => X ω ^ 2) μ :=
  (integrable_norm_iff (h.meas.pow_const 2).aestronglyMeasurable).mp
    (by simpa [norm_pow] using h.integrable 2)


/-- The integral of a function of the first coordinate against a product probability measure. -/
private lemma BOU_int_fst {Ω₁ Ω₂ E : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (F : Ω₁ → E) :
    ∫ ω, F ω.1 ∂(μ₁.prod μ₂) = ∫ x, F x ∂μ₁ := by
  rw [integral_fun_fst]
  simp

/-- The integral of a function of the second coordinate against a product probability measure. -/
private lemma BOU_int_snd {Ω₁ Ω₂ E : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (F : Ω₂ → E) :
    ∫ ω, F ω.2 ∂(μ₁.prod μ₂) = ∫ x, F x ∂μ₂ := by
  rw [integral_fun_snd]
  simp

/-- `|a|, |b| ≤ 1` gives `‖aX + bY‖ ≤ ‖X‖ + ‖Y‖`. -/
private lemma BOU_norm_comb_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (x y : ℂ) :
    ‖(a : ℂ) * x + (b : ℂ) * y‖ ≤ ‖x‖ + ‖y‖ := by
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [norm_nonneg x, norm_nonneg y, abs_nonneg a, abs_nonneg b]

/-- The integrability, centring and moment bound of the combination `aX + bY` of independent
noises on a product space. -/
private lemma BOU_comb_facts {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {X : Ω₁ → ℂ} {Y : Ω₂ → ℂ} (hX : BOU_Facts μ₁ X) (hY : BOU_Facts μ₂ Y) (a b : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    BOU_Facts (μ₁.prod μ₂) (fun ω => (a : ℂ) * X ω.1 + (b : ℂ) * Y ω.2) ∧
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
    fun k ω => (pow_le_pow_left₀ (norm_nonneg _) (BOU_norm_comb_le ha hb _ _) k).trans
      (BOU_pow_add_le (norm_nonneg _) (norm_nonneg _) k)
  have h1 := hX.int1
  have h2 := hY.int1
  have hF : BOU_Facts (μ₁.prod μ₂) (fun ω => (a : ℂ) * X ω.1 + (b : ℂ) * Y ω.2) := by
    refine ⟨hm, fun k => ?_, ?_⟩
    · refine Integrable.mono' (hint k) (hm.norm.pow_const k).aestronglyMeasurable ?_
      filter_upwards with ω
      simpa using hle k ω
    · rw [integral_add ((h1.comp_fst μ₂).const_mul _) ((h2.comp_snd μ₁).const_mul _),
        integral_const_mul, integral_const_mul, BOU_int_fst (μ₂ := μ₂) X,
        BOU_int_snd (μ₁ := μ₁) Y, hX.mean, hY.mean]
      simp
  refine ⟨hF, fun k => ?_⟩
  refine (integral_mono (hF.integrable k) (hint k) (hle k)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add ((hX.integrable k).comp_fst μ₂)
    ((hY.integrable k).comp_snd μ₁), BOU_int_fst (μ₂ := μ₂) (fun x => ‖X x‖ ^ k),
    BOU_int_snd (μ₁ := μ₁) (fun y => ‖Y y‖ ^ k)]

/-- The variance of the combination `aX + bY` of independent centred noises. -/
private lemma BOU_comb_var {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {X : Ω₁ → ℂ} {Y : Ω₂ → ℂ} (hX : BOU_Facts μ₁ X) (hY : BOU_Facts μ₂ Y) (a b : ℝ) :
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
    BOU_int_fst (μ₂ := μ₂) (fun x => ‖X x‖ ^ 2), BOU_int_snd (μ₁ := μ₁) (fun y => ‖Y y‖ ^ 2)]
  simp

/-- The pseudo-variance of the combination `aX + bY` of independent centred noises, when those of
`X` and `Y` vanish. -/
private lemma BOU_comb_pseudo {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {X : Ω₁ → ℂ} {Y : Ω₂ → ℂ} (hX : BOU_Facts μ₁ X) (hY : BOU_Facts μ₂ Y) (a b : ℝ)
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
    BOU_int_fst (μ₂ := μ₂) (fun x => X x ^ 2), BOU_int_snd (μ₁ := μ₁) (fun y => Y y ^ 2),
    hX.mean, hY.mean, hX2, hY2]
  simp

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private lemma BOU_measurable_wig (n : ℕ) (i j : Fin n) :
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
private lemma BOU_measurable_blockH (D N : ℕ) (p q : Idx D N) :
    Measurable fun w : Fin D → Coords N => blockH D N w p q := by
  by_cases h : p.1 = q.1
  · simp only [blockH, h, ↓reduceIte]
    exact (BOU_measurable_wig N p.2 q.2).comp (measurable_pi_apply q.1)
  · simp only [blockH, h, ↓reduceIte]
    exact measurable_const

/-- The array of coordinates `blockEmb D N w` is a measurable function of `w`. -/
private lemma BOU_measurable_blockEmb (D N : ℕ) : Measurable (blockEmb D N) := by
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
private lemma BOU_measurable_phi0 (D N : ℕ) (t : ℝ) :
    Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.exp (-t / 2) • blockEmb D N p.1 + Real.sqrt (1 - Real.exp (-t)) • p.2 := by
  have h1 : Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.exp (-t / 2) • blockEmb D N p.1 :=
    ((BOU_measurable_blockEmb D N).comp measurable_fst).const_smul (Real.exp (-t / 2))
  have h2 : Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.sqrt (1 - Real.exp (-t)) • p.2 :=
    measurable_snd.const_smul (Real.sqrt (1 - Real.exp (-t)))
  exact h1.add h2

/-- The array `Matrix.of.symm ((wig (D N) c).submatrix _ _)` is a measurable function of the
coordinates `c`. -/
private lemma BOU_measurable_psi (D N : ℕ) :
    Measurable fun c : Coords (D * N) => Matrix.of.symm
      ((wig (D * N) c).submatrix finProdFinEquiv finProdFinEquiv) :=
  measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q =>
    BOU_measurable_wig (D * N) (finProdFinEquiv p) (finProdFinEquiv q)

/-- The entries of `H_t` in the law (4.3) [eq:eq_in_law_H]: `e^{-t/2} (blockH w)_{pq}` plus
`√(1 - e^{-t})` times the entry `(fPFE p, fPFE q)` of the GUE `wig (DN) W`, where
`fPFE = finProdFinEquiv`. -/
private def BOU_Θ (D N : ℕ) (t : ℝ) (ω : (Fin D → Coords N) × Coords (D * N)) :
    Idx D N → Idx D N → ℂ := fun p q =>
  ((Real.exp (-t / 2) : ℝ) : ℂ) * blockH D N ω.1 p q +
    ((Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ) *
      wig (D * N) ω.2 (finProdFinEquiv p) (finProdFinEquiv q)

/-- `BOU_Θ` is measurable. -/
private lemma BOU_measurable_Θ (D N : ℕ) (t : ℝ) : Measurable (BOU_Θ D N t) :=
  measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q =>
    (measurable_const.mul ((BOU_measurable_blockH D N p q).comp measurable_fst)).add
      (measurable_const.mul
        ((BOU_measurable_wig (D * N) (finProdFinEquiv p) (finProdFinEquiv q)).comp measurable_snd))

/-- The law `ouMatLaw` is the image of `blockLaw ⊗ gueLaw (DN)` under `BOU_Θ`, by `wig_add`,
`wig_smul` and `wig_blockEmb`. -/
private lemma BOU_ouMatLaw_eq (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) :
    ouMatLaw D N L t = ((blockLaw D N L).prod (gueLaw (D * N))).map (BOU_Θ D N t) := by
  unfold ouMatLaw ouLaw
  rw [Measure.map_map (BOU_measurable_psi D N) (BOU_measurable_phi0 D N t)]
  congr 1
  funext ω
  funext p q
  change wig (D * N) (Real.exp (-t / 2) • blockEmb D N ω.1 + Real.sqrt (1 - Real.exp (-t)) • ω.2)
      (finProdFinEquiv p) (finProdFinEquiv q) = BOU_Θ D N t ω p q
  rw [wig_add, wig_smul, wig_smul]
  have h := congrFun (congrFun (wig_blockEmb D N ω.1) p) q
  simp only [Matrix.submatrix_apply] at h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h, BOU_Θ]

/-- The set of Hermitian arrays is measurable. -/
private lemma BOU_measurableSet_herm (D N : ℕ) :
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

/-! ### Combination of two class members -/

/-- The entrywise combination `a h₁ + b h₂` of two arrays with real coefficients. -/
private def BOU_comb (D N : ℕ) (a b : ℝ)
    (p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) : Idx D N → Idx D N → ℂ :=
  fun i j => (a : ℂ) * p.1 i j + (b : ℂ) * p.2 i j

/-- `BOU_comb` is measurable. -/
private lemma BOU_comb_measurable (D N : ℕ) (a b : ℝ) : Measurable (BOU_comb D N a b) :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => by
    have h1 : Measurable fun x : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) => x.1 i j :=
      by fun_prop
    have h2 : Measurable fun x : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) => x.2 i j :=
      by fun_prop
    exact (measurable_const.mul h1).add (measurable_const.mul h2)

/-- `BOU_comb` is the combination with real scalars. -/
private lemma BOU_comb_eq_smul (D N : ℕ) (a b : ℝ)
    (p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ)) :
    a • p.1 + b • p.2 = BOU_comb D N a b p := by
  funext i j
  simp [BOU_comb, Complex.real_smul]

/-- Integrals of a continuous function of the entry `(i, j)` against the law of the array `Θ ω`. -/
private lemma BOU_integral_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D N : ℕ}
    {Θ : Ω → Idx D N → Idx D N → ℂ} (hΘ : Measurable Θ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (i j : Idx D N) (F : ℂ → E) (hF : Continuous F) :
    ∫ h, F (h i j) ∂(P.map Θ) = ∫ ω, F (Θ ω i j) ∂P :=
  integral_map hΘ.aemeasurable
    (hF.comp ((continuous_apply j).comp (continuous_apply i))).aestronglyMeasurable

/-- Integrability of a continuous real function of the entry `(i, j)` against the law of `Θ ω`. -/
private lemma BOU_integrable_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D N : ℕ}
    {Θ : Ω → Idx D N → Idx D N → ℂ} (hΘ : Measurable Θ) (i j : Idx D N) (F : ℂ → ℝ)
    (hF : Continuous F) :
    Integrable (fun h : Idx D N → Idx D N → ℂ => F (h i j)) (P.map Θ) ↔
      Integrable (fun ω => F (Θ ω i j)) P :=
  integrable_map_measure
    (hF.comp ((continuous_apply j).comp (continuous_apply i))).aestronglyMeasurable
    hΘ.aemeasurable

/-- The entry `(i, j)` of a class member is a centred noise with finite absolute moments. -/
private lemma BOU_facts_class {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ}
    {μ : Measure (Idx D N → Idx D N → ℂ)} (h : LLClass D N C θ μ) (i j : Idx D N) :
    BOU_Facts μ (fun x : Idx D N → Idx D N → ℂ => x i j) :=
  ⟨(measurable_pi_apply j).comp (measurable_pi_apply i), fun k => h.integrable k i j,
    h.mean i j⟩

/-- The independent combination `a h₁ + b h₂` of two class members with `a² + b² = 1` is a class
member with parameter `a² θ₁ + b² θ₂`. -/
private lemma BOU_class_comb (D N : ℕ) {C₁ C₂ : ℕ → ℝ} {θ₁ θ₂ : ℝ}
    {μ₁ μ₂ : Measure (Idx D N → Idx D N → ℂ)} (h₁ : LLClass D N C₁ θ₁ μ₁)
    (h₂ : LLClass D N C₂ θ₂ μ₂) (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : a ^ 2 + b ^ 2 = 1) :
    LLClass D N (fun k => 2 ^ k * (|C₁ k| + |C₂ k|)) (a ^ 2 * θ₁ + b ^ 2 * θ₂)
      ((μ₁.prod μ₂).map (BOU_comb D N a b)) := by
  have := h₁.prob
  have := h₂.prob
  have hΦ := BOU_comb_measurable D N a b
  have hX := BOU_facts_class h₁
  have hY := BOU_facts_class h₂
  have hcomb : ∀ i j, BOU_Facts (μ₁.prod μ₂) (fun ω => BOU_comb D N a b ω i j) ∧
      ∀ k : ℕ, ∫ ω, ‖BOU_comb D N a b ω i j‖ ^ k ∂(μ₁.prod μ₂) ≤
        2 ^ k * ((∫ x, ‖x i j‖ ^ k ∂μ₁) + ∫ y, ‖y i j‖ ^ k ∂μ₂) :=
    fun i j => BOU_comb_facts (hX i j) (hY i j) a b ha hb
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ae_map_iff hΦ.aemeasurable (BOU_measurableSet_herm D N)]
    have e1 : ∀ᵐ p ∂(μ₁.prod μ₂), (Matrix.of p.1).IsHermitian :=
      (measurePreserving_fst (μ := μ₁) (ν := μ₂)).quasiMeasurePreserving.ae h₁.herm
    have e2 : ∀ᵐ p ∂(μ₁.prod μ₂), (Matrix.of p.2).IsHermitian :=
      (measurePreserving_snd (μ := μ₁) (ν := μ₂)).quasiMeasurePreserving.ae h₂.herm
    filter_upwards [e1, e2] with p hp1 hp2
    refine Matrix.IsHermitian.ext fun i j => ?_
    have h1 := hp1.apply i j
    have h2 := hp2.apply i j
    simp only [Matrix.of_apply] at h1 h2 ⊢
    simp only [BOU_comb, star_add, star_mul', h1, h2, Complex.star_def, Complex.conj_ofReal]
  · have hu : ∀ q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2},
        Measurable (fun h : Idx D N → Idx D N → ℂ => h q.1.1 q.1.2) := fun q =>
      (measurable_pi_apply q.1.2).comp (measurable_pi_apply q.1.1)
    exact BOU_iIndepFun_map hΦ hu (BOU_iIndep_pair hu hu h₁.indep h₂.indep (a : ℂ) (b : ℂ))
  · intro k i j
    exact (BOU_integrable_map hΦ i j (fun z : ℂ => ‖z‖ ^ k) (by fun_prop)).mpr
      ((hcomb i j).1.integrable k)
  · intro i j
    rw [BOU_integral_map hΦ i j (fun z : ℂ => z) continuous_id]
    exact (hcomb i j).1.mean
  · intro i j
    rw [BOU_integral_map hΦ i j (fun z : ℂ => ‖z‖ ^ 2) (continuous_norm.pow 2)]
    refine (BOU_comb_var (hX i j) (hY i j) a b).trans ?_
    rw [h₁.var i j, h₂.var i j]
    have e : b ^ 2 = 1 - a ^ 2 := by linarith
    simp only [varProf]
    rw [e]
    ring
  · intro i j hij
    rw [BOU_integral_map hΦ i j (fun z : ℂ => z ^ 2) (continuous_pow 2)]
    exact BOU_comb_pseudo (hX i j) (hY i j) a b (h₁.pseudo i j hij) (h₂.pseudo i j hij)
  · intro k i j
    rw [BOU_integral_map hΦ i j (fun z : ℂ => ‖z‖ ^ k) (continuous_norm.pow k)]
    refine ((hcomb i j).2 k).trans ?_
    have hr : 0 ≤ (N : ℝ) ^ (-((k : ℝ) / 2)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have h1 := h₁.moments k i j
    have h2 := h₂.moments k i j
    have hC1 : C₁ k ≤ |C₁ k| := le_abs_self _
    have hC2 : C₂ k ≤ |C₂ k| := le_abs_self _
    have h3 : (∫ x, ‖x i j‖ ^ k ∂μ₁) + ∫ y, ‖y i j‖ ^ k ∂μ₂ ≤
        (|C₁ k| + |C₂ k|) * (N : ℝ) ^ (-((k : ℝ) / 2)) := by
      nlinarith [mul_le_mul_of_nonneg_right hC1 hr, mul_le_mul_of_nonneg_right hC2 hr]
    calc 2 ^ k * ((∫ x, ‖x i j‖ ^ k ∂μ₁) + ∫ y, ‖y i j‖ ^ k ∂μ₂)
        ≤ 2 ^ k * ((|C₁ k| + |C₂ k|) * (N : ℝ) ^ (-((k : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (2 ^ k * (|C₁ k| + |C₂ k|)) * (N : ℝ) ^ (-((k : ℝ) / 2)) := by ring

/-- The entry laws of the block GUE `H^{(g)}`: `N(0, 1)` on the diagonal and `cGauss` above it,
with moment constants `m_k`. -/
private def BOU_LG : EntryLaws BOU_m where
  νd := ⟨gaussianReal 0 1, inferInstance⟩
  νo := cGauss
  intd := fun p => BOU_G_int 1 p
  into := BOU_c_int
  meand := by
    change ∫ x : ℝ, x ∂(gaussianReal 0 1) = 0
    rw [integral_id_gaussianReal]
  vard := by
    change ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1
    rw [BOU_G_sq]
    simp
  meano := BOU_c_mean
  varo := BOU_c_var
  pseudo := BOU_c_pseudo
  moments := fun p => le_of_eq rfl

/-- The law of the block GUE `H^{(g)}` as a law on arrays is `blockLaw` of `BOU_LG`. -/
private lemma BOU_gueBlocks_eq (D N : ℕ) : gueBlocks D N = blockLaw D N BOU_LG := rfl

/-- The law of the array `H^{(g)}` of the block GUE is a class member with `θ = 1`. -/
private lemma BOU_class_gue (D N : ℕ) :
    LLClass D N BOU_m 1 ((gueBlocks D N).map fun w => Matrix.of.symm (blockH D N w)) := by
  rw [BOU_gueBlocks_eq]
  exact llClass_blockH D N BOU_m BOU_LG

/-- The array version of `blockOULaw`. -/
private lemma BOU_blockOU_eq (D N : ℕ) (μ : Measure (Idx D N → Idx D N → ℂ)) [SFinite μ] (s : ℝ) :
    blockOULaw D N μ s = (μ.prod ((gueBlocks D N).map fun w => Matrix.of.symm (blockH D N w))).map
      (BOU_comb D N (Real.exp (-s / 2)) (Real.sqrt (1 - Real.exp (-s)))) := by
  have hg : Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) :=
    measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => BOU_measurable_blockH D N p q
  unfold blockOULaw
  have h1 : μ.prod ((gueBlocks D N).map fun w => Matrix.of.symm (blockH D N w)) =
      (μ.prod (gueBlocks D N)).map (Prod.map id fun w => Matrix.of.symm (blockH D N w)) := by
    rw [← Measure.map_prod_map _ _ measurable_id hg, Measure.map_id]
  rw [h1, Measure.map_map (BOU_comb_measurable D N _ _) (measurable_id.prodMap hg)]
  congr 1

/-! ### The block-OU law -/


private lemma BOU_coef {s : ℝ} (hs : 0 ≤ s) :
    |Real.exp (-s / 2)| ≤ 1 ∧ |Real.sqrt (1 - Real.exp (-s))| ≤ 1 ∧
      Real.exp (-s / 2) ^ 2 + Real.sqrt (1 - Real.exp (-s)) ^ 2 = 1 := by
  have hexp : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hα2 : Real.exp (-s / 2) ^ 2 = Real.exp (-s) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hβ2 : Real.sqrt (1 - Real.exp (-s)) ^ 2 = 1 - Real.exp (-s) := Real.sq_sqrt (by linarith)
  refine ⟨?_, ?_, by rw [hα2, hβ2]; ring⟩
  · rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.sqrt_le_one.mpr ?_
    linarith [Real.exp_pos (-s)]

/-! ### Mixtures of the entry laws -/

/-- A square root of a number in `[0, 1]` has absolute value at most `1`. -/
private lemma BOU_abs_sqrt_le {x : ℝ} (h : x ≤ 1) : |Real.sqrt x| ≤ 1 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr h

/-- The mixture `√(1-σ) h + √σ g` of a probability measure on `ℝ` with the standard Gaussian is a
probability measure. -/
private lemma BOU_mixR_prob (σ : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (mixLawR σ ν) := by
  unfold mixLawR
  infer_instance

/-- The mixture `√(1-σ) h + √σ g` of a probability measure on `ℂ` with `cGauss` is a probability
measure. -/
private lemma BOU_mix_prob (σ : ℝ) (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (mixLaw σ ν) := by
  unfold mixLaw
  infer_instance

/-- The mixtures of the entry laws `L` with the Gaussian entry laws, for `σ ∈ [0, 1]`, are entry
laws with moment constants `2^k (|C_k| + m_k)`. -/
private lemma BOU_mix_exists {C : ℕ → ℝ} (L : EntryLaws C) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∃ L' : EntryLaws (fun k => 2 ^ k * (|C k| + BOU_m k)),
      (L'.νo : Measure ℂ) = mixLaw σ L.νo ∧ (L'.νd : Measure ℝ) = mixLawR σ L.νd := by
  have ha2 : Real.sqrt (1 - σ) ^ 2 = 1 - σ := Real.sq_sqrt (by linarith)
  have hb2 : Real.sqrt σ ^ 2 = σ := Real.sq_sqrt hσ0
  have ha1 : |Real.sqrt (1 - σ)| ≤ 1 := BOU_abs_sqrt_le (by linarith)
  have hb1 : |Real.sqrt σ| ≤ 1 := BOU_abs_sqrt_le hσ1
  set a := Real.sqrt (1 - σ) with ha
  set b := Real.sqrt σ with hb
  have fd : BOU_Facts (L.νd : Measure ℝ) (fun x : ℝ => (x : ℂ)) := by
    refine ⟨Complex.measurable_ofReal, fun k => ?_, ?_⟩
    · simpa [Complex.norm_real] using L.intd k
    · rw [integral_complex_ofReal (f := fun x : ℝ => x), L.meand]
      simp
  have fo : BOU_Facts (L.νo : Measure ℂ) (fun z : ℂ => z) := ⟨measurable_id, L.into, L.meano⟩
  have gd := BOU_unit_real
  have go := BOU_unit_c
  obtain ⟨cd, cdm⟩ := BOU_comb_facts fd gd.facts a b ha1 hb1
  obtain ⟨co, com⟩ := BOU_comb_facts fo go.facts a b ha1 hb1
  have cdv := BOU_comb_var fd gd.facts a b
  have cov := BOU_comb_var fo go.facts a b
  have cop := BOU_comb_pseudo fo go.facts a b L.pseudo BOU_c_pseudo
  have hreal : ∀ ω : ℝ × ℝ, (a : ℂ) * (ω.1 : ℂ) + (b : ℂ) * (ω.2 : ℂ) =
      ((a * ω.1 + b * ω.2 : ℝ) : ℂ) := fun ω => by push_cast; ring
  have hm : Measurable fun p : ℝ × ℝ => a * p.1 + b * p.2 := by fun_prop
  have hmo : Measurable fun p : ℂ × ℂ => (a : ℂ) * p.1 + (b : ℂ) * p.2 := by fun_prop
  have hRd : mixLawR σ (L.νd : Measure ℝ) =
      ((L.νd : Measure ℝ).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => a * p.1 + b * p.2) := rfl
  have hRo : mixLaw σ (L.νo : Measure ℂ) =
      ((L.νo : Measure ℂ).prod (cGauss : Measure ℂ)).map
        (fun p : ℂ × ℂ => (a : ℂ) * p.1 + (b : ℂ) * p.2) := rfl
  have Pd : IsProbabilityMeasure (mixLawR σ (L.νd : Measure ℝ)) := BOU_mixR_prob σ _
  have Po : IsProbabilityMeasure (mixLaw σ (L.νo : Measure ℂ)) := BOU_mix_prob σ _
  have hintd : ∀ k : ℕ, Integrable (fun x : ℝ => |x| ^ k) (mixLawR σ (L.νd : Measure ℝ)) := by
    intro k
    rw [hRd]
    refine (integrable_map_measure (by fun_prop : Continuous fun x : ℝ => |x| ^ k).aestronglyMeasurable
      hm.aemeasurable).mpr ?_
    have := cd.integrable k
    simp only [hreal, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hinto : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) (mixLaw σ (L.νo : Measure ℂ)) := by
    intro k
    rw [hRo]
    exact (integrable_map_measure (by fun_prop : Continuous fun z : ℂ => ‖z‖ ^ k).aestronglyMeasurable
      hmo.aemeasurable).mpr (co.integrable k)
  have hmeand : ∫ x, x ∂(mixLawR σ (L.νd : Measure ℝ)) = 0 := by
    rw [hRd]
    rw [integral_map hm.aemeasurable (by fun_prop : Continuous fun x : ℝ => x).aestronglyMeasurable]
    have := cd.mean
    simp only [hreal] at this
    rw [integral_complex_ofReal] at this
    exact_mod_cast this
  have hmeano : ∫ z, z ∂(mixLaw σ (L.νo : Measure ℂ)) = 0 := by
    rw [hRo]
    rw [integral_map hmo.aemeasurable (by fun_prop : Continuous fun z : ℂ => z).aestronglyMeasurable]
    exact co.mean
  have hvard : ∫ x, x ^ 2 ∂(mixLawR σ (L.νd : Measure ℝ)) = 1 := by
    rw [hRd]
    rw [integral_map hm.aemeasurable (by fun_prop : Continuous fun x : ℝ => x ^ 2).aestronglyMeasurable]
    have h : ∫ ω : ℝ × ℝ, ‖(a : ℂ) * (ω.1 : ℂ) + (b : ℂ) * (ω.2 : ℂ)‖ ^ 2
        ∂((L.νd : Measure ℝ).prod (gaussianReal 0 1)) =
        a ^ 2 * ∫ x : ℝ, ‖(x : ℂ)‖ ^ 2 ∂(L.νd : Measure ℝ) +
          b ^ 2 * ∫ y : ℝ, ‖(y : ℂ)‖ ^ 2 ∂(gaussianReal 0 1) := cdv
    have e1 : ∫ x : ℝ, ‖(x : ℂ)‖ ^ 2 ∂(L.νd : Measure ℝ) = 1 := by
      simpa [Complex.norm_real, sq_abs] using L.vard
    have e2 : ∫ y : ℝ, ‖(y : ℂ)‖ ^ 2 ∂(gaussianReal 0 1) = 1 := gd.var
    rw [e1, e2, ha2, hb2] at h
    have e3 : ∫ ω : ℝ × ℝ, (a * ω.1 + b * ω.2) ^ 2 ∂((L.νd : Measure ℝ).prod (gaussianReal 0 1)) =
        ∫ ω : ℝ × ℝ, ‖(a : ℂ) * (ω.1 : ℂ) + (b : ℂ) * (ω.2 : ℂ)‖ ^ 2
          ∂((L.νd : Measure ℝ).prod (gaussianReal 0 1)) := by
      congr 1
      funext ω
      rw [hreal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [e3, h]
    ring
  have hvaro : ∫ z, ‖z‖ ^ 2 ∂(mixLaw σ (L.νo : Measure ℂ)) = 1 := by
    rw [hRo]
    rw [integral_map hmo.aemeasurable (by fun_prop : Continuous fun z : ℂ => ‖z‖ ^ 2).aestronglyMeasurable]
    have h : ∫ ω : ℂ × ℂ, ‖(a : ℂ) * ω.1 + (b : ℂ) * ω.2‖ ^ 2
        ∂((L.νo : Measure ℂ).prod (cGauss : Measure ℂ)) =
        a ^ 2 * ∫ x : ℂ, ‖x‖ ^ 2 ∂(L.νo : Measure ℂ) +
          b ^ 2 * ∫ y : ℂ, ‖y‖ ^ 2 ∂(cGauss : Measure ℂ) := cov
    rw [L.varo, BOU_c_var, ha2, hb2] at h
    rw [h]
    ring
  have hpseudo : ∫ z, z ^ 2 ∂(mixLaw σ (L.νo : Measure ℂ)) = 0 := by
    rw [hRo]
    rw [integral_map hmo.aemeasurable (by fun_prop : Continuous fun z : ℂ => z ^ 2).aestronglyMeasurable]
    exact cop
  have hmom : ∀ k : ℕ, (∫ x, |x| ^ k ∂(mixLawR σ (L.νd : Measure ℝ))) +
      (∫ z, ‖z‖ ^ k ∂(mixLaw σ (L.νo : Measure ℂ))) ≤ 2 ^ k * (|C k| + BOU_m k) := by
    intro k
    have h1 : ∫ x, |x| ^ k ∂(mixLawR σ (L.νd : Measure ℝ)) ≤
        2 ^ k * ((∫ x : ℝ, |x| ^ k ∂(L.νd : Measure ℝ)) + ∫ y : ℝ, |y| ^ k ∂(gaussianReal 0 1)) := by
      rw [hRd]
      rw [integral_map hm.aemeasurable (by fun_prop : Continuous fun x : ℝ => |x| ^ k).aestronglyMeasurable]
      have h := cdm k
      simp only [hreal, Complex.norm_real, Real.norm_eq_abs] at h
      exact h
    have h2 : ∫ z, ‖z‖ ^ k ∂(mixLaw σ (L.νo : Measure ℂ)) ≤
        2 ^ k * ((∫ x : ℂ, ‖x‖ ^ k ∂(L.νo : Measure ℂ)) + ∫ y : ℂ, ‖y‖ ^ k ∂(cGauss : Measure ℂ)) := by
      rw [hRo]
      rw [integral_map hmo.aemeasurable (by fun_prop : Continuous fun z : ℂ => ‖z‖ ^ k).aestronglyMeasurable]
      exact com k
    have h3 := L.moments k
    have h4 : BOU_m k = (∫ y : ℝ, |y| ^ k ∂(gaussianReal 0 1)) +
        ∫ y : ℂ, ‖y‖ ^ k ∂(cGauss : Measure ℂ) := rfl
    have h5 : C k ≤ |C k| := le_abs_self _
    have h6 : (0 : ℝ) ≤ 2 ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h5 h6, h6]
  exact ⟨{ νd := ⟨mixLawR σ (L.νd : Measure ℝ), Pd⟩
           νo := ⟨mixLaw σ (L.νo : Measure ℂ), Po⟩
           intd := hintd
           into := hinto
           meand := hmeand
           vard := hvard
           meano := hmeano
           varo := hvaro
           pseudo := hpseudo
           moments := hmom }, rfl, rfl⟩


/-! ### Lindeberg hybrids -/

/-- Selecting, for each index, a member of one of two independent families on a product space
gives an independent family. -/
private lemma BOU_iIndep_select {Ω₁ Ω₂ ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {u : ι → Ω₁ → ℂ} {v : ι → Ω₂ → ℂ} (hu : ∀ q, Measurable (u q)) (hv : ∀ q, Measurable (v q))
    (hu' : iIndepFun u μ₁) (hv' : iIndepFun v μ₂) (S : ι → Prop) [DecidablePred S] :
    iIndepFun (fun q (ω : Ω₁ × Ω₂) => if S q then u q ω.1 else v q ω.2) (μ₁.prod μ₂) := by
  have h1 : iIndepFun (fun q (ω : Ω₁ × Ω₂) => u q ω.1) (μ₁.prod μ₂) :=
    BOU_iIndepFun_comp_mp (measurePreserving_fst (μ := μ₁) (ν := μ₂)) hu hu'
  have h2 : iIndepFun (fun q (ω : Ω₁ × Ω₂) => v q ω.2) (μ₁.prod μ₂) :=
    BOU_iIndepFun_comp_mp (measurePreserving_snd (μ := μ₁) (ν := μ₂)) hv hv'
  have h3 : IndepFun (fun (ω : Ω₁ × Ω₂) i => u i ω.1) (fun (ω : Ω₁ × Ω₂) k => v k ω.2)
      (μ₁.prod μ₂) :=
    indepFun_prod (μ := μ₁) (ν := μ₂) (X := fun x i => u i x) (Y := fun y k => v k y)
      (measurable_pi_iff.mpr hu) (measurable_pi_iff.mpr hv)
  have h := BOU_iIndepFun_sum h1 h2 h3
  let κ : ι → ι ⊕ ι := fun q => if S q then Sum.inl q else Sum.inr q
  have hκ : Function.Injective κ := by
    intro q q' hqq
    by_cases hq : S q <;> by_cases hq' : S q' <;>
      simp only [κ, hq, hq', ↓reduceIte, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at hqq <;>
      exact hqq
  have e : (fun q (ω : Ω₁ × Ω₂) => if S q then u q ω.1 else v q ω.2) =
      (Sum.elim (fun q (ω : Ω₁ × Ω₂) => u q ω.1) (fun q (ω : Ω₁ × Ω₂) => v q ω.2)) ∘ κ := by
    funext q ω
    by_cases hq : S q <;> simp [κ, hq]
  rw [e]
  exact iIndepFun.precomp (g := κ) hκ h

/-- `hybridArr Γ` is measurable. -/
private lemma BOU_hybridArr_measurable {D N : ℕ} (Γ : Set (Idx D N × Idx D N)) :
    Measurable (hybridArr Γ) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  have h1 : Measurable fun x : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) => x.1 i j := by
    fun_prop
  have h2 : Measurable fun x : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) => x.2 i j := by
    fun_prop
  by_cases h : (i, j) ∈ Γ ∨ (j, i) ∈ Γ
  · simpa only [hybridArr, h, ↓reduceIte] using h1
  · simpa only [hybridArr, h, ↓reduceIte] using h2

/-- The law of the entry `(i, j)` of the hybrid array is that under `μ` or under `μ'`. -/
private lemma BOU_hyb_integral {D N : ℕ} {μ μ' : Measure (Idx D N → Idx D N → ℂ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (Γ : Set (Idx D N × Idx D N))
    (i j : Idx D N) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℂ → E)
    (hF : Continuous F) :
    ∫ h, F (h i j) ∂((μ.prod μ').map (hybridArr Γ)) =
      if (i, j) ∈ Γ ∨ (j, i) ∈ Γ then ∫ h, F (h i j) ∂μ else ∫ h, F (h i j) ∂μ' := by
  rw [BOU_integral_map (BOU_hybridArr_measurable Γ) i j F hF]
  by_cases h : (i, j) ∈ Γ ∨ (j, i) ∈ Γ
  · simp only [h, ↓reduceIte]
    have e : ∀ p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ),
        F (hybridArr Γ p i j) = F (p.1 i j) := by
      intro p
      simp [hybridArr, h]
    simp only [e]
    exact BOU_int_fst (μ₂ := μ') (fun x : Idx D N → Idx D N → ℂ => F (x i j))
  · simp only [h, ↓reduceIte]
    have e : ∀ p : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ),
        F (hybridArr Γ p i j) = F (p.2 i j) := by
      intro p
      simp [hybridArr, h]
    simp only [e]
    exact BOU_int_snd (μ₁ := μ) (fun x : Idx D N → Idx D N → ℂ => F (x i j))

/-- Integrability of the entry `(i, j)` of the hybrid array. -/
private lemma BOU_hyb_integrable {D N : ℕ} {μ μ' : Measure (Idx D N → Idx D N → ℂ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (Γ : Set (Idx D N × Idx D N))
    (i j : Idx D N) (F : ℂ → ℝ) (hF : Continuous F)
    (h1 : Integrable (fun h : Idx D N → Idx D N → ℂ => F (h i j)) μ)
    (h2 : Integrable (fun h : Idx D N → Idx D N → ℂ => F (h i j)) μ') :
    Integrable (fun h : Idx D N → Idx D N → ℂ => F (h i j)) ((μ.prod μ').map (hybridArr Γ)) := by
  refine (BOU_integrable_map (BOU_hybridArr_measurable Γ) i j F hF).mpr ?_
  by_cases h : (i, j) ∈ Γ ∨ (j, i) ∈ Γ
  · have e : (fun ω : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) =>
        F (hybridArr Γ ω i j)) = fun ω => F (ω.1 i j) := by
      funext ω
      simp [hybridArr, h]
    rw [e]
    exact h1.comp_fst μ'
  · have e : (fun ω : (Idx D N → Idx D N → ℂ) × (Idx D N → Idx D N → ℂ) =>
        F (hybridArr Γ ω i j)) = fun ω => F (ω.2 i j) := by
      funext ω
      simp [hybridArr, h]
    rw [e]
    exact h2.comp_snd μ

/-! ### Mixtures of the block coordinates -/

/-- `blockH` is real-linear in the coordinates. -/
private lemma BOU_blockH_comb (D N : ℕ) (a b : ℝ) (w v : Fin D → Coords N) (p q : Idx D N) :
    blockH D N (a • w + b • v) p q =
      (a : ℂ) * blockH D N w p q + (b : ℂ) * blockH D N v p q := by
  by_cases h : p.1 = q.1
  · simp only [blockH, h, ↓reduceIte, Pi.add_apply, Pi.smul_apply, wig_add, wig_smul,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  · simp [blockH, h]

/-- The rearrangement `((A × B) × (C × D)) → ((A × C) × (B × D))` preserves product measures. -/
private lemma BOU_prodRearr_mp {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
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

/-- If `g` maps `μ₁ ⊗ μ₂` to `ν`, the coordinatewise `g` maps `(⊗ᵢ μ₁) ⊗ (⊗ᵢ μ₂)` to `⊗ᵢ ν`. -/
private lemma BOU_pi_pair {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ₁ μ₂ ν : Measure E)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (g : E × E → E) (hg : Measurable g)
    (h : (μ₁.prod μ₂).map g = ν) :
    ((Measure.pi fun _ : ι => μ₁).prod (Measure.pi fun _ : ι => μ₂)).map
      (fun p i => g (p.1 i, p.2 i)) = Measure.pi fun _ : ι => ν := by
  have hmp := measurePreserving_arrowProdEquivProdArrow E E ι (fun _ => μ₁) (fun _ => μ₂)
  have e := (MeasurePreserving.symm _ hmp).map_eq
  have hf : (fun p : (ι → E) × (ι → E) => fun i => g (p.1 i, p.2 i)) =
      (fun x : ι → E × E => fun i => g (x i)) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow E E ι).symm := by
    funext p i; rfl
  rw [hf, ← Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _), e,
    Measure.pi_map_pi (fun _ => hg.aemeasurable)]
  simp [h]

/-- If `g₁` maps `μ₁ ⊗ μ₁'` to `ν₁` and `g₂` maps `μ₂ ⊗ μ₂'` to `ν₂`, then `(g₁, g₂)` maps
`(μ₁ ⊗ μ₂) ⊗ (μ₁' ⊗ μ₂')` to `ν₁ ⊗ ν₂`. -/
private lemma BOU_prod_pair {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ₁ μ₁' ν₁ : Measure A) (μ₂ μ₂' ν₂ : Measure B) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₁'] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₂']
    (g₁ : A × A → A) (g₂ : B × B → B) (h₁ : Measurable g₁) (h₂ : Measurable g₂)
    (e₁ : (μ₁.prod μ₁').map g₁ = ν₁) (e₂ : (μ₂.prod μ₂').map g₂ = ν₂) :
    ((μ₁.prod μ₂).prod (μ₁'.prod μ₂')).map
      (fun p => (g₁ (p.1.1, p.2.1), g₂ (p.1.2, p.2.2))) = ν₁.prod ν₂ := by
  have hmp := BOU_prodRearr_mp μ₁ μ₂ μ₁' μ₂'
  have hf : (fun p : (A × B) × (A × B) => (g₁ (p.1.1, p.2.1), g₂ (p.1.2, p.2.2))) =
      Prod.map g₁ g₂ ∘ (fun p : (A × B) × (A × B) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) := rfl
  rw [hf, ← Measure.map_map (h₁.prodMap h₂) hmp.measurable, hmp.map_eq,
    ← Measure.map_prod_map _ _ h₁ h₂, e₁, e₂]

/-- `coordLaw N L` is a probability measure. -/
private lemma BOU_coordLaw_prob (N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    IsProbabilityMeasure (coordLaw N L) := by
  unfold coordLaw
  infer_instance

/-- The coordinates of one block of the mixed entry laws `L'` are the mixtures
`√(1-σ) h + √σ g` of those of `L` with those of the GUE. -/
private lemma BOU_coord_mix (N : ℕ) {C C' : ℕ → ℝ} (L : EntryLaws C) (L' : EntryLaws C')
    (σ : ℝ) (ho : (L'.νo : Measure ℂ) = mixLaw σ L.νo)
    (hd : (L'.νd : Measure ℝ) = mixLawR σ L.νd) :
    coordLaw N L' = ((coordLaw N L).prod (gueLaw N)).map
      (fun p => Real.sqrt (1 - σ) • p.1 + Real.sqrt σ • p.2) := by
  set a := Real.sqrt (1 - σ) with ha
  set b := Real.sqrt σ with hb
  have hdiag : ((Measure.pi fun _ : Fin N => (L.νd : Measure ℝ)).prod
      (Measure.pi fun _ : Fin N => gaussianReal 0 1)).map
        (fun p : (Fin N → ℝ) × (Fin N → ℝ) => fun i => (fun q : ℝ × ℝ => a * q.1 + b * q.2)
          (p.1 i, p.2 i)) =
      Measure.pi fun _ : Fin N => (L'.νd : Measure ℝ) := by
    rw [hd]
    exact BOU_pi_pair (ι := Fin N) (L.νd : Measure ℝ) (gaussianReal 0 1) _
      (fun q : ℝ × ℝ => a * q.1 + b * q.2) (by fun_prop) rfl
  have hin : ((Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)).prod
      (Measure.pi fun _ : Fin N => (cGauss : Measure ℂ))).map
        (fun p : (Fin N → ℂ) × (Fin N → ℂ) => fun i => (fun q : ℂ × ℂ => (a : ℂ) * q.1 + (b : ℂ) * q.2)
          (p.1 i, p.2 i)) =
      Measure.pi fun _ : Fin N => (L'.νo : Measure ℂ) := by
    rw [ho]
    exact BOU_pi_pair (ι := Fin N) (L.νo : Measure ℂ) (cGauss : Measure ℂ) _
      (fun q : ℂ × ℂ => (a : ℂ) * q.1 + (b : ℂ) * q.2) (by fun_prop) rfl
  have hout := BOU_pi_pair (ι := Fin N) (Measure.pi fun _ : Fin N => (L.νo : Measure ℂ))
    (Measure.pi fun _ : Fin N => (cGauss : Measure ℂ))
    (Measure.pi fun _ : Fin N => (L'.νo : Measure ℂ))
    (fun p : (Fin N → ℂ) × (Fin N → ℂ) => fun i => (fun q : ℂ × ℂ => (a : ℂ) * q.1 + (b : ℂ) * q.2)
          (p.1 i, p.2 i)) (by fun_prop) hin
  have hpair := BOU_prod_pair (Measure.pi fun _ : Fin N => (L.νd : Measure ℝ))
    (Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (Measure.pi fun _ : Fin N => (L'.νd : Measure ℝ))
    (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ))
    (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (cGauss : Measure ℂ))
    (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L'.νo : Measure ℂ))
    (fun p : (Fin N → ℝ) × (Fin N → ℝ) => fun i => (fun q : ℝ × ℝ => a * q.1 + b * q.2)
          (p.1 i, p.2 i))
    (fun p : (Fin N → Fin N → ℂ) × (Fin N → Fin N → ℂ) => fun i =>
      (fun p : (Fin N → ℂ) × (Fin N → ℂ) => fun i =>
        (fun q : ℂ × ℂ => (a : ℂ) * q.1 + (b : ℂ) * q.2) (p.1 i, p.2 i)) (p.1 i, p.2 i))
    (by fun_prop) (by fun_prop) hdiag hout
  unfold coordLaw gueLaw
  rw [← hpair]
  congr 1

/-- The blocks of the mixed entry laws `L'` are the mixtures of those of `L` with the GUE blocks. -/
private lemma BOU_blockLaw_mix (D N : ℕ) {C C' : ℕ → ℝ} (L : EntryLaws C) (L' : EntryLaws C')
    (σ : ℝ) (ho : (L'.νo : Measure ℂ) = mixLaw σ L.νo)
    (hd : (L'.νd : Measure ℝ) = mixLawR σ L.νd) :
    blockLaw D N L' = ((blockLaw D N L).prod (gueBlocks D N)).map
      (fun p => Real.sqrt (1 - σ) • p.1 + Real.sqrt σ • p.2) := by
  have := BOU_coordLaw_prob N L
  have hm : Measurable fun q : Coords N × Coords N =>
      Real.sqrt (1 - σ) • q.1 + Real.sqrt σ • q.2 := by fun_prop
  have h := BOU_pi_pair (ι := Fin D) (coordLaw N L) (gueLaw N) (coordLaw N L')
    (fun q : Coords N × Coords N => Real.sqrt (1 - σ) • q.1 + Real.sqrt σ • q.2) hm
    (BOU_coord_mix N L L' σ ho hd).symm
  unfold blockLaw gueBlocks
  exact h.symm

/-- `a • w + b • v` is a measurable function of the pair of block coordinates. -/
private lemma BOU_measurable_mixA (D N : ℕ) (a b : ℝ) :
    Measurable fun p : (Fin D → Coords N) × (Fin D → Coords N) => a • p.1 + b • p.2 := by
  refine measurable_pi_iff.mpr fun k => ?_
  have h1 : Measurable fun p : (Fin D → Coords N) × (Fin D → Coords N) => p.1 k :=
    (measurable_pi_apply k).comp measurable_fst
  have h2 : Measurable fun p : (Fin D → Coords N) × (Fin D → Coords N) => p.2 k :=
    (measurable_pi_apply k).comp measurable_snd
  exact (h1.const_smul a).add (h2.const_smul b)

/-- The array `e^{-s/2} h + √(1 - e^{-s}) H^{(g)}` is a measurable function of `(h, w)`. -/
private lemma BOU_measurable_blockOU (D N : ℕ) (a b : ℝ) :
    Measurable fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
      a • p.1 + b • Matrix.of.symm (blockH D N p.2) := by
  have hg : Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) :=
    measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => BOU_measurable_blockH D N p q
  have e : (fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
      a • p.1 + b • Matrix.of.symm (blockH D N p.2)) =
      (BOU_comb D N a b) ∘ (fun p => (p.1, Matrix.of.symm (blockH D N p.2))) := by
    funext p
    exact BOU_comb_eq_smul D N a b (p.1, Matrix.of.symm (blockH D N p.2))
  rw [e]
  exact (BOU_comb_measurable D N a b).comp (measurable_fst.prodMk (hg.comp measurable_snd))

/-- The image of the product of an image law and a second law. -/
private lemma BOU_map_left {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (μ : Measure α) (ν : Measure γ) [SFinite μ]
    [SFinite ν] {f : α → β} {Θ : β × γ → δ} (hf : Measurable f) (hΘ : Measurable Θ) :
    ((μ.map f).prod ν).map Θ = (μ.prod ν).map (Θ ∘ Prod.map f id) := by
  rw [← Measure.map_map hΘ (hf.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id]


/-! ### The theorems -/

/-- The block-OU law of a class member is a class member: `θ' = e^{-s} θ + 1 - e^{-s}`, with
moment constants depending on `C` only, uniformly in `s ≥ 0`, `θ ∈ [0, 1]` and `N`. -/
theorem llClass_blockOU (D : ℕ) (C : ℕ → ℝ) :
    ∃ C' : ℕ → ℝ, ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)) (s : ℝ),
      0 ≤ θ → θ ≤ 1 → 0 ≤ s → LLClass D N C θ μ →
      LLClass D N C' (Real.exp (-s) * θ + 1 - Real.exp (-s)) (blockOULaw D N μ s) := by
  refine ⟨fun k => 2 ^ k * (|C k| + |BOU_m k|), ?_⟩
  intro N θ μ s hθ0 hθ1 hs hμ
  have := hμ.prob
  obtain ⟨h1, h2, h3⟩ := BOU_coef hs
  have hα2 : Real.exp (-s / 2) ^ 2 = Real.exp (-s) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hβ2 : Real.sqrt (1 - Real.exp (-s)) ^ 2 = 1 - Real.exp (-s) := by
    have : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact Real.sq_sqrt (by linarith)
  have h := BOU_class_comb D N hμ (BOU_class_gue D N) _ _ h1 h2 h3
  rw [BOU_blockOU_eq D N μ s]
  have e : Real.exp (-s) * θ + 1 - Real.exp (-s) =
      Real.exp (-s / 2) ^ 2 * θ + Real.sqrt (1 - Real.exp (-s)) ^ 2 * 1 := by
    rw [hα2, hβ2]
    ring
  rw [e]
  exact h

/-- The Gaussian mixtures `√(1-σ) h + √σ g` of the entry laws of Assumption 1 [main_assm] are
again entry laws, with constants depending on `C` only, for `σ ∈ (0, 1/2]`: the matrix (3.34)
[Gcom_a] satisfies Assumption 1 [main_assm]. -/
theorem entryLaws_mix (C : ℕ → ℝ) :
    ∃ C' : ℕ → ℝ, ∀ (L : EntryLaws C) (σ : ℝ), 0 < σ → σ ≤ 1 / 2 →
      ∃ L' : EntryLaws C', (L'.νo : Measure ℂ) = mixLaw σ L.νo ∧
        (L'.νd : Measure ℝ) = mixLawR σ L.νd := by
  refine ⟨fun k => 2 ^ k * (|C k| + BOU_m k), ?_⟩
  intro L σ hσ hσ'
  exact BOU_mix_exists L σ hσ.le (by linarith)

/-- The Lindeberg hybrids of Lemma 3.13 [main_lemma_com]: two class members with the same `θ`
and constants give a class member for every replacement set `Γ`. -/
theorem llClass_hybrid (D N : ℕ) (C : ℕ → ℝ) (θ : ℝ) (μ μ' : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N C θ μ) (hμ' : LLClass D N C θ μ') (Γ : Set (Idx D N × Idx D N)) :
    LLClass D N C θ ((μ.prod μ').map (hybridArr Γ)) := by
  have := hμ.prob
  have := hμ'.prob
  have hH := BOU_hybridArr_measurable Γ
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ae_map_iff hH.aemeasurable (BOU_measurableSet_herm D N)]
    have e1 : ∀ᵐ p ∂(μ.prod μ'), (Matrix.of p.1).IsHermitian :=
      (measurePreserving_fst (μ := μ) (ν := μ')).quasiMeasurePreserving.ae hμ.herm
    have e2 : ∀ᵐ p ∂(μ.prod μ'), (Matrix.of p.2).IsHermitian :=
      (measurePreserving_snd (μ := μ) (ν := μ')).quasiMeasurePreserving.ae hμ'.herm
    filter_upwards [e1, e2] with p hp1 hp2
    refine Matrix.IsHermitian.ext fun i j => ?_
    by_cases h : (i, j) ∈ Γ ∨ (j, i) ∈ Γ
    · have h' : (j, i) ∈ Γ ∨ (i, j) ∈ Γ := h.symm
      simp only [Matrix.of_apply, hybridArr, h, h', ↓reduceIte]
      exact hp1.apply i j
    · have h' : ¬ ((j, i) ∈ Γ ∨ (i, j) ∈ Γ) := fun h2 => h h2.symm
      simp only [Matrix.of_apply, hybridArr, h, h', ↓reduceIte]
      exact hp2.apply i j
  · have hu : ∀ q : {q : Idx D N × Idx D N // toLex q.1 ≤ toLex q.2},
        Measurable (fun h : Idx D N → Idx D N → ℂ => h q.1.1 q.1.2) := fun q =>
      (measurable_pi_apply q.1.2).comp (measurable_pi_apply q.1.1)
    exact BOU_iIndepFun_map hH hu (BOU_iIndep_select hu hu hμ.indep hμ'.indep
      (fun q => (q.1.1, q.1.2) ∈ Γ ∨ (q.1.2, q.1.1) ∈ Γ))
  · intro k i j
    exact BOU_hyb_integrable Γ i j (fun z : ℂ => ‖z‖ ^ k) (by fun_prop)
      (hμ.integrable k i j) (hμ'.integrable k i j)
  · intro i j
    rw [BOU_hyb_integral Γ i j (fun z : ℂ => z) continuous_id]
    split_ifs
    · exact hμ.mean i j
    · exact hμ'.mean i j
  · intro i j
    rw [BOU_hyb_integral Γ i j (fun z : ℂ => ‖z‖ ^ 2) (continuous_norm.pow 2)]
    split_ifs
    · exact hμ.var i j
    · exact hμ'.var i j
  · intro i j hij
    rw [BOU_hyb_integral Γ i j (fun z : ℂ => z ^ 2) (continuous_pow 2)]
    split_ifs
    · exact hμ.pseudo i j hij
    · exact hμ'.pseudo i j hij
  · intro k i j
    rw [BOU_hyb_integral Γ i j (fun z : ℂ => ‖z‖ ^ k) (continuous_norm.pow k)]
    split_ifs
    · exact hμ.moments k i j
    · exact hμ'.moments k i j

/-- At `t = 0` the law (4.3) [eq:eq_in_law_H] is the law of the block matrix `H` of (1.3)
[matrix_H]. -/
theorem ouMatLaw_zero (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    ouMatLaw D N L 0 = (blockLaw D N L).map fun w => Matrix.of.symm (blockH D N w) := by
  rw [BOU_ouMatLaw_eq D N L 0]
  have hf : Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) :=
    measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => BOU_measurable_blockH D N p q
  have e : BOU_Θ D N 0 =
      (fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w)) ∘ Prod.fst := by
    funext ω p q
    simp [BOU_Θ]
  rw [e, ← Measure.map_map hf measurable_fst, Measure.map_fst_prod]
  simp

/-- The Gaussian-divisible form of the law of `H_t`: if the entry laws `L'` are the mixtures
`√(1-σ) h + √σ g` of `L`, then for `θ = e^{-t}` the law of `H_t` built on `L'` is the block-OU
law, at the time `s` with `e^{-s} = 1 - θσ`, of the law of `H_{t₀}` built on `L`, with
`e^{-t₀} = θ(1 - σ)/(1 - θσ)`. -/
theorem ouMatLaw_mix_eq (D N : ℕ) {C C' : ℕ → ℝ} (L : EntryLaws C) (L' : EntryLaws C') (σ t : ℝ)
    (hσ : 0 < σ) (hσ' : σ ≤ 1 / 2) (ht : 0 ≤ t) (ho : (L'.νo : Measure ℂ) = mixLaw σ L.νo)
    (hd : (L'.νd : Measure ℝ) = mixLawR σ L.νd) :
    ouMatLaw D N L' t = blockOULaw D N
      (ouMatLaw D N L (-Real.log (Real.exp (-t) * (1 - σ) / (1 - Real.exp (-t) * σ))))
      (-Real.log (1 - Real.exp (-t) * σ)) := by
  have hθ0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hθ1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hσ1 : 0 < 1 - σ := by linarith
  have hθσ : 0 < 1 - Real.exp (-t) * σ := by nlinarith
  have hr0 : 0 < Real.exp (-t) * (1 - σ) / (1 - Real.exp (-t) * σ) := by positivity
  set θ := Real.exp (-t) with hθ
  set r := θ * (1 - σ) / (1 - θ * σ) with hr
  set s := -Real.log (1 - θ * σ) with hs
  set t₀ := -Real.log r with ht₀
  have hes : Real.exp (-s) = 1 - θ * σ := by rw [hs, neg_neg, Real.exp_log hθσ]
  have het : Real.exp (-t₀) = r := by rw [ht₀, neg_neg, Real.exp_log hr0]
  have hrr : (1 - θ * σ) * r = θ * (1 - σ) := by rw [hr]; field_simp
  have hαt : Real.exp (-t / 2) = Real.sqrt θ := Real.exp_half (-t)
  have hαs : Real.exp (-s / 2) = Real.sqrt (1 - θ * σ) := by rw [Real.exp_half (-s), hes]
  have hα0 : Real.exp (-t₀ / 2) = Real.sqrt r := by rw [Real.exp_half (-t₀), het]
  have hβs : 1 - Real.exp (-s) = θ * σ := by rw [hes]; ring
  have c1 : Real.exp (-t / 2) * Real.sqrt (1 - σ) =
      Real.exp (-s / 2) * Real.exp (-t₀ / 2) := by
    rw [hαt, hαs, hα0, ← Real.sqrt_mul hθ0.le, ← Real.sqrt_mul hθσ.le, hrr]
  have c2 : Real.exp (-t / 2) * Real.sqrt σ = Real.sqrt (1 - Real.exp (-s)) := by
    rw [hαt, hβs, ← Real.sqrt_mul hθ0.le]
  have c3 : Real.sqrt (1 - Real.exp (-t)) =
      Real.exp (-s / 2) * Real.sqrt (1 - Real.exp (-t₀)) := by
    rw [hαs, het, ← Real.sqrt_mul hθσ.le]
    congr 1
    have : (1 - θ * σ) * (1 - r) = (1 - θ * σ) - (1 - θ * σ) * r := by ring
    rw [this, hrr]
    ring
  have c1' : ((Real.exp (-t / 2) : ℝ) : ℂ) * (Real.sqrt (1 - σ) : ℝ) =
      ((Real.exp (-s / 2) : ℝ) : ℂ) * (Real.exp (-t₀ / 2) : ℝ) := by exact_mod_cast c1
  have c2' : ((Real.exp (-t / 2) : ℝ) : ℂ) * (Real.sqrt σ : ℝ) =
      ((Real.sqrt (1 - Real.exp (-s)) : ℝ) : ℂ) := by exact_mod_cast c2
  have c3' : ((Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ) =
      ((Real.exp (-s / 2) : ℝ) : ℂ) * (Real.sqrt (1 - Real.exp (-t₀)) : ℝ) := by
    exact_mod_cast c3
  have hΘt := BOU_measurable_Θ D N t
  have hΘ0 := BOU_measurable_Θ D N t₀
  have hA := BOU_measurable_mixA D N (Real.sqrt (1 - σ)) (Real.sqrt σ)
  have hΦ := BOU_measurable_blockOU D N (Real.exp (-s / 2)) (Real.sqrt (1 - Real.exp (-s)))
  rw [BOU_ouMatLaw_eq D N L' t, BOU_blockLaw_mix D N L L' σ ho hd, BOU_ouMatLaw_eq D N L t₀]
  unfold blockOULaw
  rw [BOU_map_left _ _ hA hΘt, BOU_map_left _ _ hΘ0 hΦ]
  have hE : MeasurePreserving
      (fun x : ((Fin D → Coords N) × Coords (D * N)) × (Fin D → Coords N) => ((x.1.1, x.2), x.1.2))
      (((blockLaw D N L).prod (gueLaw (D * N))).prod (gueBlocks D N))
      (((blockLaw D N L).prod (gueBlocks D N)).prod (gueLaw (D * N))) := by
    have h1 := measurePreserving_prodAssoc (blockLaw D N L) (gueLaw (D * N)) (gueBlocks D N)
    have h2 : MeasurePreserving
        (Prod.map (id : (Fin D → Coords N) → (Fin D → Coords N))
          (Prod.swap : Coords (D * N) × (Fin D → Coords N) → (Fin D → Coords N) × Coords (D * N)))
        ((blockLaw D N L).prod ((gueLaw (D * N)).prod (gueBlocks D N)))
        ((blockLaw D N L).prod ((gueBlocks D N).prod (gueLaw (D * N)))) :=
      (MeasurePreserving.id _).prod Measure.measurePreserving_swap
    have h3 := (measurePreserving_prodAssoc (blockLaw D N L) (gueBlocks D N)
      (gueLaw (D * N))).symm
    exact h3.comp (h2.comp h1)
  rw [← hE.map_eq, Measure.map_map (hΘt.comp (hA.prodMap measurable_id)) hE.measurable]
  congr 1
  funext x
  obtain ⟨⟨w, W⟩, v⟩ := x
  funext p q
  simp only [Function.comp_apply, Prod.map_apply, id, BOU_Θ, Pi.add_apply, Pi.smul_apply,
    Complex.real_smul, Matrix.of_symm_apply]
  rw [BOU_blockH_comb]
  linear_combination (blockH D N w p q) * c1' + (blockH D N v p q) * c2' +
    (wig (D * N) W (finProdFinEquiv p) (finProdFinEquiv q)) * c3'

end RBMTransitionEdge

end
