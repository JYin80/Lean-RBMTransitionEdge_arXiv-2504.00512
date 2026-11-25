module

public import RBMTransitionEdge.LocalLaw.OU
public import RBMTransitionEdge.Prob.GridA
public import RBMTransitionEdge.Prob.GridMartingale

@[expose] public section

/-!
# Martingale tools on the grid with an arbitrary initial law

Independence of the increments, the conditional
sub-Gaussian bound and the Azuma–Hoeffding bound for the stopped linear martingale part on the
grid of the flow (3.12) [eq:Ht] started from a full array, and the single-step expansion on arrays
that replaces the Itô formula (3.47) [Ito].
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal
open Filter
open scoped ENNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Measurability, independence and the law of one increment -/

/-- The array `Matrix.of.symm (blockH D N w)` of a block-GUE coordinate vector `w`. -/
private abbrev GAM_arr (D N : ℕ) (w : Fin D → Coords N) : Idx D N → Idx D N → ℂ :=
  Matrix.of.symm (blockH D N w)

/-- `GAM_arr` is additive (`wig_add` entrywise). -/
private theorem GAM_arr_add (D N : ℕ) (v w : Fin D → Coords N) :
    GAM_arr D N (v + w) = GAM_arr D N v + GAM_arr D N w := by
  ext p q
  simp only [GAM_arr, blockH, Pi.add_apply, wig_add, Matrix.add_apply, Matrix.of_symm_apply]
  split_ifs <;> simp

/-- `GAM_arr` is real-homogeneous (`wig_smul` entrywise). -/
private theorem GAM_arr_smul (D N : ℕ) (c : ℝ) (w : Fin D → Coords N) :
    GAM_arr D N (c • w) = c • GAM_arr D N w := by
  ext p q
  simp only [GAM_arr, blockH, Pi.smul_apply, wig_smul, Matrix.smul_apply, Matrix.of_symm_apply]
  split_ifs <;> simp [Complex.real_smul]

/-- The generating map of `gridFiltrA D N K k`: the initial array and the increments `X_{j+1}`,
`j < k`, with the others set to `0`. -/
private def GAM_mask (D N K k : ℕ) (ω : GridΩA D N K) : GridΩA D N K :=
  (ω.1, fun j : Fin K => if (j : ℕ) < k then ω.2 j else 0)

/-- Coordinates of a product measure that are functions of disjoint sets of factors are
independent. -/
private theorem GAM_pi_indep (K : ℕ) {E : Type*} [MeasurableSpace E] [Zero E] (ν : Measure E)
    [IsProbabilityMeasure ν] (k : ℕ) (hk : k < K) :
    IndepFun (fun x : Fin K → E => fun j : Fin K => if (j : ℕ) < k then x j else 0)
      (fun x : Fin K → E => x ⟨k, hk⟩) (Measure.pi fun _ : Fin K => ν) := by
  have hind : iIndepFun (fun (j : Fin K) (x : Fin K → E) => x j) (Measure.pi fun _ : Fin K => ν) :=
    iIndepFun_pi (X := fun _ => (id : E → E)) (fun _ => aemeasurable_id)
  set S : Finset (Fin K) := Finset.univ.filter fun j => (j : ℕ) < k with hS
  set T : Finset (Fin K) := {⟨k, hk⟩} with hT
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro j hj hjT
    simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hj hjT
    subst hjT
    exact lt_irrefl _ hj
  have h1 := hind.indepFun_finset S T hST fun j => measurable_pi_apply j
  have hφ1 : Measurable fun y : S → E => fun j : Fin K => if h : j ∈ S then y ⟨j, h⟩ else 0 := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hj : j ∈ S
    · simp only [hj, ↓reduceDIte]
      exact measurable_pi_apply _
    · simp only [hj, ↓reduceDIte]
      exact measurable_const
  have hφ2 : Measurable fun y : T → E => y ⟨⟨k, hk⟩, Finset.mem_singleton_self _⟩ :=
    measurable_pi_apply _
  have h2 := h1.comp hφ1 hφ2
  have e1 : (fun x : Fin K → E => fun j : Fin K => if (j : ℕ) < k then x j else 0) =
      (fun y : S → E => fun j : Fin K => if h : j ∈ S then y ⟨j, h⟩ else 0) ∘
        fun (a : Fin K → E) (i : S) => a i := by
    funext x j
    by_cases hj : (j : ℕ) < k
    · simp [hj, hS]
    · simp [hj, hS]
  have e2 : (fun x : Fin K → E => x ⟨k, hk⟩) =
      (fun y : T → E => y ⟨⟨k, hk⟩, Finset.mem_singleton_self _⟩) ∘
        fun (a : Fin K → E) (i : T) => a i := rfl
  rw [e1, e2]
  exact h2

/-- If `U` and `V` are independent under `ν`, then `(a, b) ↦ (a, U b)` and `(a, b) ↦ V b` are
independent under `P ⊗ ν`. -/
private theorem GAM_prod_indepFun {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (P : Measure α) (ν : Measure β)
    [IsProbabilityMeasure P] [IsProbabilityMeasure ν] {U : β → γ} {V : β → δ}
    (hU : Measurable U) (hV : Measurable V) (h : IndepFun U V ν) :
    IndepFun (fun p : α × β => (p.1, U p.2)) (fun p : α × β => V p.2) (P.prod ν) := by
  have hg : Measurable fun b => (U b, V b) := hU.prodMk hV
  have hUV : ν.map (fun b => (U b, V b)) = (ν.map U).prod (ν.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 h
  have m1 : (P.prod ν).map (fun p : α × β => (p.1, U p.2)) = P.prod (ν.map U) := by
    have := Measure.map_prod_map P ν (f := id) (g := U) measurable_id hU
    rw [Measure.map_id] at this
    exact this.symm
  have m2 : (P.prod ν).map (fun p : α × β => V p.2) = ν.map V := by
    have : (fun p : α × β => V p.2) = V ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map hV measurable_snd, Measure.map_snd_prod]
    simp
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), m1, m2]
  have m3 : (P.prod ν).map (fun p : α × β => ((p.1, U p.2), V p.2)) =
      (P.prod (ν.map fun b => (U b, V b))).map MeasurableEquiv.prodAssoc.symm := by
    have := Measure.map_prod_map P ν (f := id) (g := fun b => (U b, V b)) measurable_id hg
    rw [Measure.map_id] at this
    rw [this, Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (measurable_id.prodMap hg)]
    rfl
  rw [m3, hUV]
  exact (MeasurePreserving.symm _ (measurePreserving_prodAssoc P (ν.map U) (ν.map V))).map_eq

/-- The generating map of `𝓕_k` is independent of the increment `X_{k+1}`, for every law `P`
of the initial array. -/
private theorem GAM_prior_indepFun (D N K : ℕ) (P : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure P] (k : ℕ) (hk : k < K) :
    IndepFun (GAM_mask D N K k) (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩)
      (P.prod (Measure.pi fun _ : Fin K => gueBlocks D N)) := by
  have hU : Measurable fun x : Fin K → Fin D → Coords N =>
      fun j : Fin K => if (j : ℕ) < k then x j else 0 := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hj : (j : ℕ) < k
    · simp only [hj, ↓reduceIte]
      exact measurable_pi_apply _
    · simp only [hj, ↓reduceIte]
      exact measurable_const
  exact GAM_prod_indepFun P (Measure.pi fun _ : Fin K => gueBlocks D N) hU
    (measurable_pi_apply _) (GAM_pi_indep K (gueBlocks D N) k hk)

/-- The increment `X_{k+1}` has the law `gueBlocks D N`. -/
private theorem GAM_prior_map_incr (D N K : ℕ) (P : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure P] (k : ℕ) (hk : k < K) :
    (P.prod (Measure.pi fun _ : Fin K => gueBlocks D N)).map
      (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩) = gueBlocks D N := by
  have : (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩) =
      (fun x : Fin K → Fin D → Coords N => x ⟨k, hk⟩) ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply _) measurable_snd, Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  exact (measurePreserving_eval (fun _ : Fin K => gueBlocks D N) ⟨k, hk⟩).map_eq

/-- The map `(x, y) ↦ x + y i` as a continuous linear map. -/
private def GAM_RealPairToC : ℝ × ℝ →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I

/-- `cGauss` is a Gaussian law. -/
instance GAM_CGauss_isGaussian : IsGaussian (cGauss : Measure ℂ) := by
  have : (cGauss : Measure ℂ) =
      ((gaussianReal 0 (1 / 2 : ℝ≥0)).prod (gaussianReal 0 (1 / 2 : ℝ≥0))).map GAM_RealPairToC := by
    have e : (GAM_RealPairToC : ℝ × ℝ → ℂ) =
        fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      funext p; simp [GAM_RealPairToC, Complex.real_smul]
    rw [e]
    rfl
  rw [this]
  infer_instance

/-- A product of copies of a Gaussian law is Gaussian. -/
private instance GAM_IsGaussian_pi {ι X : Type*} [Fintype ι] [NormedAddCommGroup X]
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

/-- The law of the GUE blocks is Gaussian. -/
instance GAM_GueBlocks_isGaussian (D N : ℕ) : IsGaussian (gueBlocks D N) := by
  have : IsGaussian (gueLaw N) := by unfold gueLaw; infer_instance
  unfold gueBlocks
  infer_instance

/-- `x ↦ -x` preserves the GUE blocks. -/
private theorem GAM_GueBlocks_neg (D N : ℕ) :
    MeasurePreserving (fun x : Fin D → Coords N => -x) (gueBlocks D N) (gueBlocks D N) := by
  refine ⟨measurable_neg, ?_⟩
  have := Measure.pi_map_pi (μ := fun _ : Fin D => gueLaw N) (f := fun _ x => -x)
    (fun _ => measurable_neg.aemeasurable)
  simp only [gueLaw_map_neg] at this
  exact this

/-- An odd function has integral `0` under the GUE blocks. -/
private theorem GAM_GueBlocks_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (D N : ℕ)
    (f : (Fin D → Coords N) → E) (hf : ∀ x, f (-x) = -f x) : ∫ x, f x ∂(gueBlocks D N) = 0 := by
  have h := (GAM_GueBlocks_neg D N).integral_comp (MeasurableEquiv.neg _).measurableEmbedding f
  simp only [hf, integral_neg] at h
  have : (2 : ℝ) • ∫ x, f x ∂(gueBlocks D N) = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; simp
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

/-- The mgf of a linear functional under the GUE blocks: `E e^{q L(X)} = e^{q² E L(X)²/2}`. -/
private theorem GAM_GueBlocks_mgf (D N : ℕ) (L : (Fin D → Coords N) →L[ℝ] ℝ) (q : ℝ) :
    Integrable (fun x => Real.exp (q * L x)) (gueBlocks D N) ∧
      ∫ x, Real.exp (q * L x) ∂(gueBlocks D N) =
        Real.exp ((∫ x, (L x) ^ 2 ∂(gueBlocks D N)) * q ^ 2 / 2) := by
  set γ := gueBlocks D N
  have hmean : γ[L] = 0 := GAM_GueBlocks_odd D N (fun x => L x) (fun x => by simp)
  have hvar : Var[L; γ] = ∫ x, (L x) ^ 2 ∂γ :=
    variance_of_integral_eq_zero L.continuous.measurable.aemeasurable hmean
  have hlaw : HasLaw L (gaussianReal (γ[L]) (Var[L; γ]).toNNReal) γ :=
    ⟨L.continuous.measurable.aemeasurable, IsGaussian.map_eq_gaussianReal L⟩
  have hm := mgf_gaussianReal hlaw q
  have hv0 : 0 ≤ Var[L; γ] := variance_nonneg _ _
  rw [hmean, Real.coe_toNNReal _ hv0, hvar, zero_mul, zero_add] at hm
  refine ⟨?_, ?_⟩
  · rw [← mgf_pos_iff, hm]; exact Real.exp_pos _
  · exact hm

/-- Freezing for nonnegative functionals: if `Z` and `X` are independent, then
`E Γ(Z, X) = E ∫ Γ(Z, x) d(law X)(x)` for measurable `Γ ≥ 0`. -/
private theorem GAM_Freeze {Ω U E : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : Ω → U} {X : Ω → E}
    (hZ : Measurable Z) (hX : Measurable X) (hind : IndepFun Z X μ) {Γ : U × E → ℝ≥0∞}
    (hΓ : Measurable Γ) :
    ∫⁻ ω, Γ (Z ω, X ω) ∂μ = ∫⁻ ω, ∫⁻ x, Γ (Z ω, x) ∂(μ.map X) ∂μ := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hX.aemeasurable).1 hind
  calc ∫⁻ ω, Γ (Z ω, X ω) ∂μ = ∫⁻ p, Γ p ∂(μ.map fun ω => (Z ω, X ω)) :=
        (lintegral_map hΓ (hZ.prodMk hX)).symm
    _ = ∫⁻ p, Γ p ∂((μ.map Z).prod (μ.map X)) := by rw [hmap]
    _ = ∫⁻ z, ∫⁻ x, Γ (z, x) ∂(μ.map X) ∂(μ.map Z) := lintegral_prod _ hΓ.aemeasurable
    _ = ∫⁻ ω, ∫⁻ x, Γ (Z ω, x) ∂(μ.map X) ∂μ := lintegral_map hΓ.lintegral_prod_right' hZ

/-- `(ω, x) ↦ a ω x` is measurable for the product of `m` and the Borel σ-algebra. -/
private theorem GAM_Eval_meas {Ω V : Type*} {m : MeasurableSpace Ω} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a : Ω → V →L[ℝ] ℝ} (ha : StronglyMeasurable[m] a) :
    Measurable[m.prod inferInstance] fun p : Ω × V => a p.1 p.2 := by
  have h1 : StronglyMeasurable[m.prod inferInstance] fun p : Ω × V => (a p.1, p.2) :=
    (ha.comp_measurable measurable_fst).prodMk measurable_snd.stronglyMeasurable
  have h2 : Continuous fun q : (V →L[ℝ] ℝ) × V => q.1 q.2 := continuous_fst.clm_apply continuous_snd
  exact (h2.comp_stronglyMeasurable h1).measurable

/-- Taylor's formula of order `n` with the remainder bounded by `B ‖y‖^{n+1}`. -/
private theorem GAM_Taylor {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] (f : E → W) (n : ℕ)
    (hf : ContDiff ℝ (n + 1) f) (B : ℝ) (hB : ∀ z, ‖iteratedFDeriv ℝ (n + 1) f z‖ ≤ B)
    (x y : E) :
    ‖f (x + y) - ∑ k ∈ Finset.range (n + 1),
        ((k.factorial : ℝ))⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y)‖ ≤ B * ‖y‖ ^ (n + 1) := by
  rw [map_add_eq_sum_add_integral_iteratedFDeriv (fun t _ => hf.contDiffAt), add_sub_cancel_left]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
  have hint : ‖∫ t in (0 : ℝ)..1,
      (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤
        B * ‖y‖ ^ (n + 1) * |1 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have h1 : ‖(1 - t) ^ n‖ ≤ 1 := by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
    have h2 : ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤ B * ‖y‖ ^ (n + 1) := by
      refine ((iteratedFDeriv ℝ (n + 1) f (x + t • y)).le_opNorm _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul_of_nonneg_right (hB _) (by positivity)
    rw [norm_smul]
    calc ‖(1 - t) ^ n‖ * ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
        ≤ 1 * (B * ‖y‖ ^ (n + 1)) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = B * ‖y‖ ^ (n + 1) := one_mul _
  rw [sub_zero, abs_one, mul_one] at hint
  rw [norm_smul]
  have hfac : ‖((n.factorial : ℝ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, Real.norm_natCast]
    exact inv_le_one_of_one_le₀
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n))
  calc ‖((n.factorial : ℝ))⁻¹‖ * ‖∫ t in (0 : ℝ)..1,
        (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
      ≤ 1 * (B * ‖y‖ ^ (n + 1)) := mul_le_mul hfac hint (norm_nonneg _) zero_le_one
    _ = B * ‖y‖ ^ (n + 1) := one_mul _

/-- `‖x‖^p` is integrable under the GUE blocks. -/
private theorem GAM_Int_pow (D N p : ℕ) :
    Integrable (fun x : Fin D → Coords N => ‖x‖ ^ p) (gueBlocks D N) :=
  (IsGaussian.memLp_id (gueBlocks D N) p (by simp)).integrable_norm_pow'

/-- `‖x‖⁴ ≤ Σ_i ‖x_i‖⁴` for the sup norm of a finite product. -/
private theorem GAM_Pi_pow4 {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (x : ι → E) :
    ‖x‖ ^ 4 ≤ ∑ i, ‖x i‖ ^ 4 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim x 0]
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖)
      Finset.univ_nonempty
    have h : ‖x‖ ≤ ‖x i₀‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hi₀ i (Finset.mem_univ _)
    calc ‖x‖ ^ 4 ≤ ‖x i₀‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h 4
      _ ≤ ∑ i, ‖x i‖ ^ 4 := Finset.single_le_sum (f := fun i => ‖x i‖ ^ 4)
          (fun i _ => by positivity) (Finset.mem_univ i₀)

/-- `‖(u, v)‖⁴ ≤ ‖u‖⁴ + ‖v‖⁴` for the sup norm of a product. -/
private theorem GAM_Prod_pow4 {E G : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup G]
    (p : E × G) : ‖p‖ ^ 4 ≤ ‖p.1‖ ^ 4 + ‖p.2‖ ^ 4 := by
  rw [Prod.norm_def]
  rcases le_total ‖p.1‖ ‖p.2‖ with h | h
  · rw [max_eq_right h]; have := pow_nonneg (norm_nonneg p.1) 4; linarith
  · rw [max_eq_left h]; have := pow_nonneg (norm_nonneg p.2) 4; linarith

/-- The fourth moment of the GUE blocks: `E‖X‖⁴ ≤ (DN + DN²)(m₄ + m₄')`, with `m₄` and `m₄'` the
fourth absolute moments of `N(0, 1)` and of the standard complex Gaussian. -/
private theorem GAM_Moment4 (D N : ℕ) :
    ∫ x, ‖x‖ ^ 4 ∂(gueBlocks D N) ≤ ((D : ℝ) * N + D * N * N) *
      ((∫ y, ‖y‖ ^ 4 ∂(gaussianReal 0 1)) + ∫ z, ‖z‖ ^ 4 ∂(cGauss : Measure ℂ)) := by
  set γ := gueBlocks D N with hγ
  set mR := ∫ y, ‖y‖ ^ 4 ∂(gaussianReal 0 1) with hmR
  set mC := ∫ z, ‖z‖ ^ 4 ∂(cGauss : Measure ℂ) with hmC
  have hmR0 : 0 ≤ mR := integral_nonneg fun y => by positivity
  have hmC0 : 0 ≤ mC := integral_nonneg fun z => by positivity
  have iR : Integrable (fun y : ℝ => ‖y‖ ^ 4) (gaussianReal 0 1) :=
    (IsGaussian.memLp_id (gaussianReal 0 1) 4 (by simp)).integrable_norm_pow'
  have iC : Integrable (fun z : ℂ => ‖z‖ ^ 4) (cGauss : Measure ℂ) :=
    (IsGaussian.memLp_id (cGauss : Measure ℂ) 4 (by simp)).integrable_norm_pow'
  have mpD : ∀ (a : Fin D) (i : Fin N), MeasurePreserving
      (fun x : Fin D → Coords N => (x a).1 i) γ (gaussianReal 0 1) := by
    intro a i
    have h2 : MeasurePreserving (Prod.fst : Coords N → Fin N → ℝ) (gueLaw N)
        (Measure.pi fun _ : Fin N => gaussianReal 0 1) := measurePreserving_fst
    exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).comp
      (h2.comp (measurePreserving_eval (fun _ : Fin D => gueLaw N) a))
  have mpA : ∀ (a : Fin D) (i j : Fin N), MeasurePreserving
      (fun x : Fin D → Coords N => (x a).2 i j) γ (cGauss : Measure ℂ) := by
    intro a i j
    have h2 : MeasurePreserving (Prod.snd : Coords N → Fin N → Fin N → ℂ) (gueLaw N)
        (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (cGauss : Measure ℂ)) :=
      measurePreserving_snd
    have h3 := measurePreserving_eval
      (fun _ : Fin N => Measure.pi fun _ : Fin N => (cGauss : Measure ℂ)) i
    have h4 := measurePreserving_eval (fun _ : Fin N => (cGauss : Measure ℂ)) j
    exact h4.comp (h3.comp (h2.comp (measurePreserving_eval (fun _ : Fin D => gueLaw N) a)))
  have iDc : ∀ (a : Fin D) (i : Fin N),
      Integrable (fun x : Fin D → Coords N => ‖(x a).1 i‖ ^ 4) γ :=
    fun a i => by
      have := (mpD a i).integrable_comp_of_integrable (g := fun y : ℝ => ‖y‖ ^ 4) iR
      exact this
  have iAc : ∀ (a : Fin D) (i j : Fin N),
      Integrable (fun x : Fin D → Coords N => ‖(x a).2 i j‖ ^ 4) γ :=
    fun a i j => by
      have := (mpA a i j).integrable_comp_of_integrable (g := fun z : ℂ => ‖z‖ ^ 4) iC
      exact this
  have eD : ∀ (a : Fin D) (i : Fin N), ∫ x, ‖(x a).1 i‖ ^ 4 ∂γ = mR := by
    intro a i
    have := integral_map (μ := γ) (mpD a i).measurable.aemeasurable
      (continuous_norm.pow 4).aestronglyMeasurable (f := fun y : ℝ => ‖y‖ ^ 4)
    rw [(mpD a i).map_eq] at this
    exact this.symm
  have eA : ∀ (a : Fin D) (i j : Fin N), ∫ x, ‖(x a).2 i j‖ ^ 4 ∂γ = mC := by
    intro a i j
    have := integral_map (μ := γ) (mpA a i j).measurable.aemeasurable
      (continuous_norm.pow 4).aestronglyMeasurable (f := fun z : ℂ => ‖z‖ ^ 4)
    rw [(mpA a i j).map_eq] at this
    exact this.symm
  have hpt : ∀ x : Fin D → Coords N, ‖x‖ ^ 4 ≤
      ∑ a, ((∑ i, ‖(x a).1 i‖ ^ 4) + ∑ i, ∑ j, ‖(x a).2 i j‖ ^ 4) := by
    intro x
    refine (GAM_Pi_pow4 x).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (GAM_Prod_pow4 (x a)).trans (add_le_add (GAM_Pi_pow4 _) ?_)
    exact (GAM_Pi_pow4 _).trans (Finset.sum_le_sum fun i _ => GAM_Pi_pow4 _)
  have iS : ∀ a : Fin D, Integrable (fun x : Fin D → Coords N =>
      (∑ i, ‖(x a).1 i‖ ^ 4) + ∑ i, ∑ j, ‖(x a).2 i j‖ ^ 4) γ := fun a =>
    (integrable_finsetSum _ fun i _ => iDc a i).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iAc a i j)
  calc ∫ x, ‖x‖ ^ 4 ∂γ ≤ ∫ x, ∑ a, ((∑ i, ‖(x a).1 i‖ ^ 4) + ∑ i, ∑ j, ‖(x a).2 i j‖ ^ 4) ∂γ :=
        integral_mono (GAM_Int_pow D N 4) (integrable_finsetSum _ fun a _ => iS a) hpt
    _ = ∑ a : Fin D, ((∑ i : Fin N, mR) + ∑ i : Fin N, ∑ j : Fin N, mC) := by
        rw [integral_finsetSum _ fun a _ => iS a]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_add (integrable_finsetSum _ fun i _ => iDc a i)
          (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iAc a i j),
          integral_finsetSum _ fun i _ => iDc a i,
          integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iAc a i j]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => eD a i
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum _ fun j _ => iAc a i j]
          exact Finset.sum_congr rfl fun j _ => eA a i j
    _ = (D : ℝ) * N * mR + D * N * N * mC := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ ((D : ℝ) * N + D * N * N) * (mR + mC) := by
        have h1 : (0 : ℝ) ≤ D * N * mC := by positivity
        have h2 : (0 : ℝ) ≤ D * N * N * mR := by positivity
        have e : ((D : ℝ) * N + D * N * N) * (mR + mC) =
            (D : ℝ) * N * mR + D * N * N * mC + (D * N * mC + D * N * N * mR) := by ring
        linarith

/-- The increment `X_{k+1}` is `𝓕_{k+1}`-measurable. -/
private theorem GAM_incr_meas (D N K k : ℕ) (hk : k < K) :
    Measurable[gridFiltrA D N K (k + 1)] fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩ := by
  have e : (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩) = (fun u : GridΩA D N K => u.2 ⟨k, hk⟩) ∘
      (fun ω : GridΩA D N K =>
        (ω.1, fun j : Fin K => if (j : ℕ) < k + 1 then ω.2 j else 0)) := by
    funext ω
    simp
  rw [e]
  exact ((measurable_pi_apply _).comp measurable_snd).comp (comap_measurable _)

/-- The increment `X_{k+1}` is independent of `𝓕_k` on the grid with initial law `μ₀`. -/
theorem gridIncrA_indep (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] (k : ℕ) (hk : k < K) :
    Indep (gridFiltrA D N K k)
      (MeasurableSpace.comap (fun ω : GridΩA D N K => ω.2 ⟨k, hk⟩) inferInstance)
      (gridLawA D N K μ₀) :=
  (IndepFun_iff_Indep _ _ _).1 (GAM_prior_indepFun D N K μ₀ k hk)

/-- The frozen-Gaussian lemma on the grid with initial law `μ₀`: for an `𝓕_k`-measurable linear
functional `a` and an `𝓕_k`-measurable event `S` on which `E_X (a X)² ≤ c`, the increment
`1_S a(X_{k+1})` is conditionally sub-Gaussian with the constant `c`. -/
theorem gridCondSubGA (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] (k : ℕ) (hk : k < K)
    (a : GridΩA D N K → (Fin D → Coords N) →L[ℝ] ℝ) (ha : StronglyMeasurable[gridFiltrA D N K k] a)
    (S : Set (GridΩA D N K)) (hS : MeasurableSet[gridFiltrA D N K k] S) (c : ℝ≥0)
    (hc : ∀ ω ∈ S, ∫ x, (a ω x) ^ 2 ∂(gueBlocks D N) ≤ c) :
    HasCondSubgaussianMGF (gridFiltrA D N K k) ((gridFiltrationA D N K).le k)
      (S.indicator fun ω => a ω (ω.2 ⟨k, hk⟩)) c (gridLawA D N K μ₀) := by
  change HasCondSubgaussianMGF (gridFiltrA D N K k) ((gridFiltrA_mono D N K).2 k)
    (S.indicator fun ω => a ω (ω.2 ⟨k, hk⟩)) c (gridLawA D N K μ₀)
  set μ := gridLawA D N K μ₀ with hμ
  have hm : gridFiltrA D N K k ≤ _ := (gridFiltrA_mono D N K).2 k
  set Z : GridΩA D N K → GridΩA D N K :=
    fun ω => (ω.1, fun j : Fin K => if (j : ℕ) < k then ω.2 j else 0) with hZdef
  have hZ : Measurable Z := by
    refine measurable_fst.prodMk (measurable_pi_iff.mpr fun j => ?_)
    by_cases hj : (j : ℕ) < k
    · simp only [hj, ↓reduceIte]
      fun_prop
    · simp [hj]
  have hmZ : gridFiltrA D N K k = MeasurableSpace.comap Z inferInstance := rfl
  set X : GridΩA D N K → Fin D → Coords N := fun ω => ω.2 ⟨k, hk⟩ with hXdef
  have hX : Measurable X := (measurable_pi_apply _).comp measurable_snd
  have hmI : μ.map X = gueBlocks D N := GAM_prior_map_incr D N K μ₀ k hk
  have hind : IndepFun Z X μ := by
    rw [IndepFun_iff_Indep, ← hmZ]
    exact gridIncrA_indep D N K μ₀ k hk
  have ha' : StronglyMeasurable[MeasurableSpace.comap Z inferInstance] a := ha
  obtain ⟨g, hg, hga⟩ := ha'.exists_eq_measurable_comp
  have hS' : MeasurableSet[MeasurableSpace.comap Z inferInstance] S := hS
  obtain ⟨S', hS'm, hS'eq⟩ := hS'
  set Y := S.indicator fun ω => a ω (X ω) with hYdef
  set Φ : GridΩA D N K × (Fin D → Coords N) → ℝ := fun p => S'.indicator (fun u => g u p.2) p.1
    with hΦdef
  have hΦ : Measurable Φ := by
    simp only [Φ, Set.indicator_apply]
    exact Measurable.ite (measurable_fst hS'm) (GAM_Eval_meas hg) measurable_const
  have hYΦ : ∀ ω, Y ω = Φ (Z ω, X ω) := by
    intro ω
    simp only [Y, Φ, Set.indicator_apply, ← hS'eq, Set.mem_preimage, hga, Function.comp]
  have hYm : Measurable Y := by
    have : Y = fun ω => Φ (Z ω, X ω) := funext hYΦ
    rw [this]
    exact hΦ.comp (hZ.prodMk hX)
  -- the frozen bound for one value of `q`
  have key : ∀ (q : ℝ) (T : Set (GridΩA D N K)), MeasurableSet[gridFiltrA D N K k] T →
      ∫⁻ ω in T, ENNReal.ofReal (Real.exp (q * Y ω)) ∂μ ≤
        ENNReal.ofReal (Real.exp (c * q ^ 2 / 2)) * μ T := by
    intro q T hT
    have hT' : MeasurableSet[MeasurableSpace.comap Z inferInstance] T := hT
    obtain ⟨T', hT'm, hT'eq⟩ := hT'
    set Γ : GridΩA D N K × (Fin D → Coords N) → ℝ≥0∞ := fun p =>
      T'.indicator (fun _ => ENNReal.ofReal (Real.exp (q * Φ p))) p.1 with hΓdef
    have hΓ : Measurable Γ := by
      have h1 : Measurable fun p : GridΩA D N K × (Fin D → Coords N) =>
          ENNReal.ofReal (Real.exp (q * Φ p)) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hΦ.const_mul q))
      simp only [Γ, Set.indicator_apply]
      exact Measurable.ite (measurable_fst hT'm) h1 measurable_const
    have hfr := GAM_Freeze μ hZ hX hind hΓ
    rw [hmI] at hfr
    have e1 : ∫⁻ ω in T, ENNReal.ofReal (Real.exp (q * Y ω)) ∂μ = ∫⁻ ω, Γ (Z ω, X ω) ∂μ := by
      rw [← lintegral_indicator (hm _ hT)]
      refine lintegral_congr fun ω => ?_
      simp only [Γ, Set.indicator_apply, ← hT'eq, Set.mem_preimage, hYΦ]
    have hin : ∀ ω, ∫⁻ x, Γ (Z ω, x) ∂(gueBlocks D N) ≤
        T.indicator (fun _ => ENNReal.ofReal (Real.exp (c * q ^ 2 / 2))) ω := by
      intro ω
      by_cases hωT : ω ∈ T
      · have hZT : Z ω ∈ T' := by rw [← hT'eq] at hωT; exact hωT
        simp only [Γ, Set.indicator_of_mem hZT, Set.indicator_of_mem hωT]
        by_cases hωS : ω ∈ S
        · have hZS : Z ω ∈ S' := by rw [← hS'eq] at hωS; exact hωS
          simp only [Φ, Set.indicator_of_mem hZS]
          have hgω : g (Z ω) = a ω := by rw [hga]; rfl
          rw [hgω]
          obtain ⟨hi, he⟩ := GAM_GueBlocks_mgf D N (a ω) q
          rw [← ofReal_integral_eq_lintegral_ofReal hi
            (ae_of_all _ fun x => (Real.exp_pos _).le), he]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have := hc ω hωS
          have hq : 0 ≤ q ^ 2 / 2 := by positivity
          nlinarith
        · have hZS : Z ω ∉ S' := by rw [← hS'eq] at hωS; exact hωS
          simp only [Φ, Set.indicator_of_notMem hZS, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
            lintegral_const, measure_univ, mul_one]
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
      · have hZT : Z ω ∉ T' := by rw [← hT'eq] at hωT; exact hωT
        simp [Γ, Set.indicator_of_notMem hZT, Set.indicator_of_notMem hωT]
    rw [e1, hfr]
    calc ∫⁻ ω, ∫⁻ x, Γ (Z ω, x) ∂(gueBlocks D N) ∂μ
        ≤ ∫⁻ ω, T.indicator (fun _ => ENNReal.ofReal (Real.exp (c * q ^ 2 / 2))) ω ∂μ :=
          lintegral_mono hin
      _ = ENNReal.ofReal (Real.exp (c * q ^ 2 / 2)) * μ T := lintegral_indicator_const (hm _ hT) _
  have hint : ∀ q : ℝ, Integrable (fun ω => Real.exp (q * Y ω)) μ := by
    intro q
    refine ⟨(Real.measurable_exp.comp (hYm.const_mul q)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => (Real.exp_pos _).le)]
    have := key q Set.univ MeasurableSet.univ
    rw [Measure.restrict_univ] at this
    exact this.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  have hsetint : ∀ (q : ℝ) (T : Set (GridΩA D N K)), MeasurableSet[gridFiltrA D N K k] T →
      ∫ ω in T, Real.exp (q * Y ω) ∂μ ≤ ∫ ω in T, Real.exp (c * q ^ 2 / 2) ∂μ := by
    intro q T hT
    rw [setIntegral_const, smul_eq_mul, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun ω => (Real.exp_pos _).le) (hint q).1.restrict]
    have := key q T hT
    have hfin : ENNReal.ofReal (Real.exp (c * q ^ 2 / 2)) * μ T ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    have := ENNReal.toReal_mono hfin this
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
    simpa [Measure.real, mul_comm] using this
  refine Kernel.HasSubgaussianMGF.of_rat ?_ fun q => ?_
  · intro t
    rw [condExpKernel_comp_trim]
    exact hint t
  · have h_eq := condExp_ae_eq_trim_integral_condExpKernel hm (hint q)
    have hle : μ[fun ω => Real.exp (q * Y ω) | gridFiltrA D N K k] ≤ᵐ[μ.trim hm]
        fun _ => Real.exp (c * (q : ℝ) ^ 2 / 2) := by
      have hfi : Integrable (μ[fun ω => Real.exp (q * Y ω) | gridFiltrA D N K k]) (μ.trim hm) :=
        integrable_condExp.trim hm stronglyMeasurable_condExp
      refine @ae_le_of_forall_setIntegral_le _ (gridFiltrA D N K k) _ _ _ hfi (integrable_const _)
        fun T hT _ => ?_
      rw [← setIntegral_trim hm stronglyMeasurable_condExp hT,
        setIntegral_condExp hm (hint q) hT, ← setIntegral_trim hm stronglyMeasurable_const hT]
      exact hsetint q T hT
    filter_upwards [h_eq, hle] with ω h1 h2
    rw [mgf, ← h1]
    exact h2

/-- The generator of the flow (3.12) [eq:Ht] with the drift on all entries, on arrays:
`𝓛F(H) = -½ DF(H)[H] + ½ E D²F(H)[X, X]`, `X` block-diagonal GUE. -/
def genA {D N : ℕ} (F : (Idx D N → Idx D N → ℂ) → ℂ) (H : Idx D N → Idx D N → ℂ) : ℂ :=
  -(1 / 2 : ℂ) * fderiv ℝ F H H + (1 / 2 : ℂ) * ∫ x, iteratedFDeriv ℝ 2 F H
    ![Matrix.of.symm (blockH D N x), Matrix.of.symm (blockH D N x)] ∂(gueBlocks D N)

/-! ### Arrays of the block coordinates as a continuous linear map -/

/-- `GAM_arr` as a real-linear map. -/
private def GAM_arrL (D N : ℕ) : (Fin D → Coords N) →ₗ[ℝ] (Idx D N → Idx D N → ℂ) where
  toFun := GAM_arr D N
  map_add' := GAM_arr_add D N
  map_smul' c w := by simpa using GAM_arr_smul D N c w

/-- `GAM_arr` is continuous (a linear map of finite-dimensional spaces). -/
private theorem GAM_arr_continuous (D N : ℕ) : Continuous (GAM_arr D N) :=
  (GAM_arrL D N).continuous_of_finiteDimensional

/-- `GAM_arr` is odd. -/
private theorem GAM_arr_neg (D N : ℕ) (x : Fin D → Coords N) :
    GAM_arr D N (-x) = -GAM_arr D N x := by
  have := GAM_arr_smul D N (-1) x
  simpa using this

/-- An entry of `wig n c` is bounded by the sup norm of the coordinates `c`. -/
private theorem GAM_wig_norm_le (n : ℕ) (c : Coords n) (i j : Fin n) : ‖wig n c i j‖ ≤ ‖c‖ := by
  have hn : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Fin.pos i) (by norm_num)
  have h1 : ‖c.1 i‖ ≤ ‖c‖ := (norm_le_pi_norm c.1 i).trans (norm_fst_le c)
  have h2 : ∀ a b, ‖c.2 a b‖ ≤ ‖c‖ := fun a b =>
    ((norm_le_pi_norm (c.2 a) b).trans (norm_le_pi_norm c.2 a)).trans (norm_snd_le c)
  unfold wig
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmain : ‖(if i = j then ((c.1 i : ℝ) : ℂ) else if i < j then c.2 i j
      else star (c.2 j i))‖ ≤ ‖c‖ := by
    split_ifs
    · simpa using h1
    · exact h2 i j
    · rw [norm_star]
      exact h2 j i
  calc _ ≤ 1 * ‖c‖ := mul_le_mul hn hmain (norm_nonneg _) zero_le_one
    _ = ‖c‖ := one_mul _

/-- The array of a block-GUE coordinate vector has sup norm at most that of the coordinates. -/
private theorem GAM_arr_norm_le (D N : ℕ) (w : Fin D → Coords N) : ‖GAM_arr D N w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun p =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun q => ?_
  simp only [GAM_arr, blockH, Matrix.of_symm_apply]
  split_ifs
  · exact (GAM_wig_norm_le N (w p.1) p.2 q.2).trans (norm_le_pi_norm w p.1)
  · simp

/-! ### Homogeneity and bounds of the multilinear maps `D^j F(c)` on constant arguments -/

/-- A multilinear map on a constant argument is homogeneous of degree `n`. -/
private theorem GAM_iter_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) (s : ℝ) (v : E) :
    L (fun _ => s • v) = s ^ n • L (fun _ => v) := by
  have := L.map_smul_univ (fun _ => s) (fun _ => v)
  simpa [Finset.prod_const] using this

/-- A multilinear map on a constant argument is bounded by `‖L‖ ‖v‖^n`. -/
private theorem GAM_iter_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) (v : E) :
    ‖L (fun _ => v)‖ ≤ ‖L‖ * ‖v‖ ^ n := by
  refine (L.le_opNorm _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The second derivative `D²F(c)[A x, A x]` is continuous in `x`. -/
private theorem GAM_Q_cont (D N : ℕ) (F : (Idx D N → Idx D N → ℂ) → ℂ)
    (c : Idx D N → Idx D N → ℂ) :
    Continuous fun x : Fin D → Coords N => iteratedFDeriv ℝ 2 F c (fun _ => GAM_arr D N x) :=
  (iteratedFDeriv ℝ 2 F c).cont.comp (continuous_pi fun _ => GAM_arr_continuous D N)

/-- `‖D²F(c)[A x, A x]‖ ≤ B ‖x‖²`. -/
private theorem GAM_Q_bound (D N : ℕ) (F : (Idx D N → Idx D N → ℂ) → ℂ) (B : ℝ)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ v, ‖iteratedFDeriv ℝ j F v‖ ≤ B)
    (c : Idx D N → Idx D N → ℂ) (x : Fin D → Coords N) :
    ‖iteratedFDeriv ℝ 2 F c (fun _ => GAM_arr D N x)‖ ≤ B * ‖x‖ ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 le_rfl (by norm_num) c)
  exact (GAM_iter_norm_le _ _).trans (mul_le_mul (hB 2 (by norm_num) (by norm_num) c)
    (pow_le_pow_left₀ (norm_nonneg _) (GAM_arr_norm_le D N x) 2) (by positivity) hB0)

/-- `x ↦ D²F(c)[A x, A x]` is integrable under the GUE blocks. -/
private theorem GAM_Q_int (D N : ℕ) (F : (Idx D N → Idx D N → ℂ) → ℂ) (B : ℝ)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ v, ‖iteratedFDeriv ℝ j F v‖ ≤ B)
    (c : Idx D N → Idx D N → ℂ) :
    Integrable (fun x : Fin D → Coords N => iteratedFDeriv ℝ 2 F c (fun _ => GAM_arr D N x))
      (gueBlocks D N) :=
  Integrable.mono' ((GAM_Int_pow D N 2).const_mul B) (GAM_Q_cont D N F c).aestronglyMeasurable
    (ae_of_all _ fun x => GAM_Q_bound D N F B hB c x)

/-- `D²F` is Lipschitz with constant `B` when `‖D³F‖ ≤ B`. -/
private theorem GAM_D2_lip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → ℂ)
    (B : ℝ) (hF : ContDiff ℝ 4 F)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ v, ‖iteratedFDeriv ℝ j F v‖ ≤ B) (u c : V) :
    ‖iteratedFDeriv ℝ 2 F u - iteratedFDeriv ℝ 2 F c‖ ≤ B * ‖u - c‖ := by
  have hc : ContDiff ℝ (0 + 1) (iteratedFDeriv ℝ 2 F) := hF.iteratedFDeriv_right (by norm_num)
  have := GAM_Taylor (iteratedFDeriv ℝ 2 F) 0 hc B (fun z => by
    have h3 := hB 3 (by norm_num) (by norm_num) z
    rw [← norm_fderiv_iteratedFDeriv (n := 2)] at h3
    rw [zero_add, norm_iteratedFDeriv_one]
    exact h3) c (u - c)
  simpa using this

/-! ### The fourth-order expansion at a fixed array -/

/-- The expansion at `c` of `E F(c + s A(X))`, `0 ≤ s ≤ 1`:
`|E F(c + s A(X)) - F(c) - (s²/2) E D²F(c)[A X, A X]| ≤ B s⁴ E‖X‖⁴`. -/
private theorem GAM_T1 (D N : ℕ) (F : (Idx D N → Idx D N → ℂ) → ℂ) (B : ℝ) (hF : ContDiff ℝ 4 F)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ v, ‖iteratedFDeriv ℝ j F v‖ ≤ B)
    (c : Idx D N → Idx D N → ℂ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖(∫ x, F (c + s • GAM_arr D N x) ∂(gueBlocks D N)) - F c -
        ((s ^ 2 / 2 : ℝ) : ℂ) * ∫ x, iteratedFDeriv ℝ 2 F c (fun _ => GAM_arr D N x)
          ∂(gueBlocks D N)‖ ≤ B * s ^ 4 * ∫ x, ‖x‖ ^ 4 ∂(gueBlocks D N) := by
  set γ := gueBlocks D N with hγ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 le_rfl (by norm_num) c)
  have h4 : ∀ z, ‖iteratedFDeriv ℝ (3 + 1) F z‖ ≤ B := hB 4 (by norm_num) (by norm_num)
  have h0 : ∀ z, ‖iteratedFDeriv ℝ (0 + 1) F z‖ ≤ B := hB 1 (by norm_num) (by norm_num)
  set Q : (Fin D → Coords N) → ℂ :=
    fun x => iteratedFDeriv ℝ 2 F c (fun _ => GAM_arr D N x) with hQ
  set Od : (Fin D → Coords N) → ℂ := fun x =>
    iteratedFDeriv ℝ 1 F c (fun _ => s • GAM_arr D N x) +
      ((1 / 6 : ℝ) : ℂ) * iteratedFDeriv ℝ 3 F c (fun _ => s • GAM_arr D N x) with hOd
  set P : (Fin D → Coords N) → ℂ := fun x => ∑ k ∈ Finset.range (3 + 1),
    ((k.factorial : ℝ))⁻¹ • iteratedFDeriv ℝ k F c (fun _ => s • GAM_arr D N x) with hPdef
  have hP : ∀ x, P x = F c + ((s ^ 2 / 2 : ℝ) : ℂ) * Q x + Od x := by
    intro x
    have e2 : iteratedFDeriv ℝ 2 F c (fun _ => s • GAM_arr D N x) = (s ^ 2) • Q x :=
      GAM_iter_smul _ s _
    simp only [P, Od, Finset.sum_range_succ, Finset.sum_range_zero, iteratedFDeriv_zero_apply, e2]
    simp [Nat.factorial, Complex.real_smul]
    ring
  have hAx : ∀ x : Fin D → Coords N, ‖s • GAM_arr D N x‖ ≤ s * ‖x‖ := fun x => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left (GAM_arr_norm_le D N x) hs0
  have hsx : ∀ x : Fin D → Coords N, ‖s • GAM_arr D N x‖ ≤ ‖x‖ := fun x =>
    (hAx x).trans (mul_le_of_le_one_left (norm_nonneg _) hs1)
  have tay : ∀ x, ‖F (c + s • GAM_arr D N x) - P x‖ ≤ B * ‖s • GAM_arr D N x‖ ^ 4 := fun x =>
    GAM_Taylor F 3 hF B h4 c (s • GAM_arr D N x)
  have hcontv : ∀ n : ℕ, Continuous fun x : Fin D → Coords N =>
      iteratedFDeriv ℝ n F c (fun _ => s • GAM_arr D N x) := fun n =>
    (iteratedFDeriv ℝ n F c).cont.comp
      (continuous_pi fun _ => (GAM_arr_continuous D N).const_smul s)
  have hbn : ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ x : Fin D → Coords N,
      ‖iteratedFDeriv ℝ n F c (fun _ => s • GAM_arr D N x)‖ ≤ B * ‖x‖ ^ n := fun n h1 h4 x =>
    (GAM_iter_norm_le _ _).trans (mul_le_mul (hB n h1 h4 c)
      (pow_le_pow_left₀ (norm_nonneg _) (hsx x) n) (by positivity) hB0)
  -- integrability
  have iX1 := GAM_Int_pow D N 1
  have iX2 := GAM_Int_pow D N 2
  have iX3 := GAM_Int_pow D N 3
  have iX4 := GAM_Int_pow D N 4
  have iF : Integrable (fun x => F (c + s • GAM_arr D N x)) γ := by
    have hcont : Continuous fun x : Fin D → Coords N => F (c + s • GAM_arr D N x) :=
      hF.continuous.comp (continuous_const.add ((GAM_arr_continuous D N).const_smul s))
    refine Integrable.mono' ((integrable_const ‖F c‖).add (iX1.const_mul B))
      hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have := GAM_Taylor F 0 (hF.of_le (by norm_num)) B h0 c (s • GAM_arr D N x)
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.factorial_zero,
      Nat.cast_one, inv_one, iteratedFDeriv_zero_apply, one_smul, pow_one] at this
    calc ‖F (c + s • GAM_arr D N x)‖ ≤ ‖F c‖ + ‖F (c + s • GAM_arr D N x) - F c‖ := by
          have := norm_add_le (F c) (F (c + s • GAM_arr D N x) - F c)
          simpa using this
      _ ≤ ‖F c‖ + B * ‖x‖ ^ 1 := by
          rw [pow_one]
          exact add_le_add le_rfl (this.trans (mul_le_mul_of_nonneg_left (hsx x) hB0))
  have iQ : Integrable Q γ := GAM_Q_int D N F B hB c
  have iOd : Integrable Od γ := by
    have hcont : Continuous Od := (hcontv 1).add (continuous_const.mul (hcontv 3))
    refine Integrable.mono' ((iX1.const_mul B).add (iX3.const_mul B))
      hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have b1 := hbn 1 le_rfl (by norm_num) x
    have b3 : ‖((1 / 6 : ℝ) : ℂ) * iteratedFDeriv ℝ 3 F c (fun _ => s • GAM_arr D N x)‖ ≤
        B * ‖x‖ ^ 3 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      have := hbn 3 (by norm_num) (by norm_num) x
      have hT0 : 0 ≤ ‖iteratedFDeriv ℝ 3 F c (fun _ => s • GAM_arr D N x)‖ := norm_nonneg _
      linarith
    exact (norm_add_le _ _).trans (add_le_add b1 b3)
  have zOd : ∫ x, Od x ∂γ = 0 := by
    refine GAM_GueBlocks_odd D N Od fun x => ?_
    have hodd : ∀ n : ℕ, ∀ y : Fin D → Coords N,
        iteratedFDeriv ℝ n F c (fun _ => s • GAM_arr D N (-y)) =
          (-1 : ℝ) ^ n • iteratedFDeriv ℝ n F c (fun _ => s • GAM_arr D N y) := by
      intro n y
      have e : (fun _ : Fin n => s • GAM_arr D N (-y)) =
          fun _ => (-1 : ℝ) • (s • GAM_arr D N y) := by
        funext _
        simp [GAM_arr_neg]
      rw [e, GAM_iter_smul]
    simp only [Od, hodd]
    simp [Complex.real_smul]
    ring
  have iQ' : Integrable (fun x => ((s ^ 2 / 2 : ℝ) : ℂ) * Q x) γ := iQ.const_mul _
  have iC : Integrable (fun _ : Fin D → Coords N => F c) γ := integrable_const _
  have iCQ : Integrable (fun x => F c + ((s ^ 2 / 2 : ℝ) : ℂ) * Q x) γ := iC.add iQ'
  have iP : Integrable P γ := by
    have : P = fun x => F c + ((s ^ 2 / 2 : ℝ) : ℂ) * Q x + Od x := funext hP
    rw [this]
    exact iCQ.add iOd
  have hIP : ∫ x, P x ∂γ = F c + ((s ^ 2 / 2 : ℝ) : ℂ) * ∫ x, Q x ∂γ := by
    simp only [hP]
    rw [integral_add iCQ iOd, zOd, integral_add iC iQ', integral_const_mul, integral_const,
      probReal_univ, one_smul, add_zero]
  have e : (∫ x, F (c + s • GAM_arr D N x) ∂γ) - F c - ((s ^ 2 / 2 : ℝ) : ℂ) * ∫ x, Q x ∂γ =
      ∫ x, (F (c + s • GAM_arr D N x) - P x) ∂γ := by
    rw [integral_sub iF iP, hIP]
    ring
  rw [e, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (iX4.const_mul _) (ae_of_all _ fun x => (tay x).trans ?_)
  calc B * ‖s • GAM_arr D N x‖ ^ 4 ≤ B * (s * ‖x‖) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hAx x) 4) hB0
    _ = B * s ^ 4 * ‖x‖ ^ 4 := by ring

set_option maxHeartbeats 1000000 in
/-- The single-step expansion of the flow (3.12) [eq:Ht] on arrays:
`E F(e^{-h/2} H + √(1-e^{-h}) X) = F(H) + h 𝓛F(H) + O(h²)` with the remainder
`K B h² (1 + ‖H‖)⁴ (DN + 1)⁴`, `K` absolute. -/
theorem gaussStepA_expansion : ∃ K : ℝ, ∀ (D N : ℕ) (F : (Idx D N → Idx D N → ℂ) → ℂ) (B h : ℝ),
    ContDiff ℝ 4 F → (∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ v, ‖iteratedFDeriv ℝ j F v‖ ≤ B) →
    0 < h → h ≤ 1 → ∀ H : Idx D N → Idx D N → ℂ,
      ‖(∫ x, F (Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) •
            Matrix.of.symm (blockH D N x)) ∂(gueBlocks D N)) - F H - h * genA F H‖ ≤
        K * B * h ^ 2 * (1 + ‖H‖) ^ 4 * ((D : ℝ) * N + 1) ^ 4 := by
  set M := (∫ y, ‖y‖ ^ 4 ∂(gaussianReal 0 1)) + ∫ z, ‖z‖ ^ 4 ∂(cGauss : Measure ℂ) with hM
  have hM0 : 0 ≤ M := add_nonneg (integral_nonneg fun y => by positivity)
    (integral_nonneg fun z => by positivity)
  refine ⟨6 * M + 4, fun D N F B h hF hB hh0 hh1 H => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 le_rfl (by norm_num) H)
  have h1 : ∀ x, ‖fderiv ℝ F x‖ ≤ B := fun x => by
    have := hB 1 le_rfl (by norm_num) x
    rwa [norm_iteratedFDeriv_one] at this
  set γ := gueBlocks D N with hγ
  set α := Real.exp (-h / 2) with hα
  set s := Real.sqrt (1 - Real.exp (-h)) with hs
  set c := α • H with hc
  set nc : ℝ := (D : ℝ) * N + D * N * N with hnc
  have hnc0 : 0 ≤ nc := by positivity
  -- elementary bounds on the coefficients
  have hE1 : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hs2 : s ^ 2 = 1 - Real.exp (-h) := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsh : s ^ 2 ≤ h := by rw [hs2]; linarith [Real.add_one_le_exp (-h)]
  have hs1 : s ≤ 1 := by nlinarith
  have hs4 : s ^ 4 ≤ h ^ 2 := by
    have : s ^ 4 = (s ^ 2) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) hsh 2
  have habs : |(-h)| ≤ 1 := by rw [abs_neg, abs_of_pos hh0]; exact hh1
  have habs2 : |(-h / 2)| ≤ 1 := by rw [abs_div, abs_neg, abs_of_pos hh0]; norm_num; linarith
  have hsd : |s ^ 2 - h| ≤ h ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le habs
    rw [hs2]
    calc |1 - Real.exp (-h) - h| = |Real.exp (-h) - 1 - -h| := by
          rw [← abs_neg]; ring_nf
      _ ≤ (-h) ^ 2 := this
      _ = h ^ 2 := by ring
  have hα1 : |α - 1| ≤ h := by
    have := Real.abs_exp_sub_one_le habs2
    rw [abs_div, abs_neg, abs_of_pos hh0] at this
    linarith
  have hα2 : |α - 1 + h / 2| ≤ h ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le habs2
    have e : α - 1 + h / 2 = Real.exp (-h / 2) - 1 - -h / 2 := by rw [hα]; ring
    calc |α - 1 + h / 2| = |Real.exp (-h / 2) - 1 - -h / 2| := by rw [e]
      _ ≤ (-h / 2) ^ 2 := this
      _ ≤ h ^ 2 := by nlinarith
  -- the moments
  set m2 : ℝ := ∫ x, ‖x‖ ^ 2 ∂γ with hm2
  have hm2_0 : 0 ≤ m2 := integral_nonneg fun x => by positivity
  have hm4 : ∫ x, ‖x‖ ^ 4 ∂γ ≤ nc * M := GAM_Moment4 D N
  have hm2le : m2 ≤ 1 + nc * M := by
    calc m2 ≤ ∫ x, (1 + ‖x‖ ^ 4) ∂γ := by
          refine integral_mono (GAM_Int_pow D N 2) ((integrable_const 1).add (GAM_Int_pow D N 4))
            fun x => ?_
          have h4 : ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 := by ring
          simp only [h4]
          nlinarith [sq_nonneg (‖x‖ ^ 2 - 1), sq_nonneg ‖x‖]
      _ = 1 + ∫ x, ‖x‖ ^ 4 ∂γ := by
          rw [integral_add (integrable_const 1) (GAM_Int_pow D N 4)]
          simp
          rfl
      _ ≤ 1 + nc * M := by linarith
  -- the second-order terms
  set QH : ℂ := ∫ x, iteratedFDeriv ℝ 2 F H (fun _ => GAM_arr D N x) ∂γ with hQH
  set Qc : ℂ := ∫ x, iteratedFDeriv ℝ 2 F c (fun _ => GAM_arr D N x) ∂γ with hQc
  have hvec : ∀ v : Idx D N → Idx D N → ℂ,
      (![v, v] : Fin 2 → Idx D N → Idx D N → ℂ) = fun _ => v := by
    intro v
    funext i
    fin_cases i <;> rfl
  have hgen : genA F H = -(1 / 2 : ℂ) * fderiv ℝ F H H + (1 / 2 : ℂ) * QH := by
    simp only [genA, hvec]
    rfl
  have hQcb : ‖Qc‖ ≤ B * m2 := by
    rw [hQc, hm2, ← integral_const_mul]
    exact norm_integral_le_of_norm_le ((GAM_Int_pow D N 2).const_mul B)
      (ae_of_all _ fun x => GAM_Q_bound D N F B hB c x)
  have hcH : ‖c - H‖ ≤ h * ‖H‖ := by
    have : c - H = (α - 1) • H := by rw [hc, sub_smul, one_smul]
    rw [this, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hα1 (norm_nonneg _)
  have hQd : ‖Qc - QH‖ ≤ B * (h * ‖H‖) * m2 := by
    have hLip := GAM_D2_lip F B hF hB c H
    have pt : ∀ x : Fin D → Coords N,
        ‖iteratedFDeriv ℝ 2 F c (fun _ => GAM_arr D N x) -
          iteratedFDeriv ℝ 2 F H (fun _ => GAM_arr D N x)‖ ≤ (B * (h * ‖H‖)) * ‖x‖ ^ 2 := by
      intro x
      have e : iteratedFDeriv ℝ 2 F c (fun _ => GAM_arr D N x) -
          iteratedFDeriv ℝ 2 F H (fun _ => GAM_arr D N x) =
          (iteratedFDeriv ℝ 2 F c - iteratedFDeriv ℝ 2 F H) (fun _ => GAM_arr D N x) := rfl
      rw [e]
      refine (GAM_iter_norm_le _ _).trans ?_
      have hL : ‖iteratedFDeriv ℝ 2 F c - iteratedFDeriv ℝ 2 F H‖ ≤ B * (h * ‖H‖) :=
        hLip.trans (mul_le_mul_of_nonneg_left hcH hB0)
      exact mul_le_mul hL (pow_le_pow_left₀ (norm_nonneg _) (GAM_arr_norm_le D N x) 2)
        (by positivity) (by positivity)
    rw [hQc, hQH, ← integral_sub (GAM_Q_int D N F B hB c) (GAM_Q_int D N F B hB H), hm2,
      ← integral_const_mul]
    exact norm_integral_le_of_norm_le ((GAM_Int_pow D N 2).const_mul _)
      (ae_of_all _ fun x => pt x)
  -- the pieces
  have hT1 := GAM_T1 D N F B hF hB c s hs0 hs1
  have hmom : ∫ x, ‖x‖ ^ 4 ∂γ ≤ nc * M := hm4
  have T1' : ‖(∫ x, F (c + s • GAM_arr D N x) ∂γ) - F c - ((s ^ 2 / 2 : ℝ) : ℂ) * Qc‖ ≤
      h ^ 2 * (B * (nc * M)) := by
    refine hT1.trans ?_
    calc B * s ^ 4 * ∫ x, ‖x‖ ^ 4 ∂γ ≤ B * h ^ 2 * (nc * M) := by
          gcongr
      _ = h ^ 2 * (B * (nc * M)) := by ring
  have T2 : ‖F c - F H - ((α - 1 : ℝ) : ℂ) * fderiv ℝ F H H‖ ≤ B * (h ^ 2 * ‖H‖ ^ 2) := by
    have := GAM_Taylor F 1 (hF.of_le (by norm_num)) B (hB 2 (by norm_num) (by norm_num)) H
      ((α - 1) • H)
    have ec : H + (α - 1) • H = c := by rw [hc, sub_smul, one_smul]; abel
    simp only [ec, Finset.sum_range_succ, Finset.sum_range_zero, iteratedFDeriv_zero_apply,
      iteratedFDeriv_one_apply, map_smul] at this
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul, zero_add,
      Complex.real_smul] at this
    refine (le_of_eq_of_le ?_ this).trans ?_
    · rw [sub_sub]
    · rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      have : (α - 1) ^ 2 ≤ h ^ 2 := by
        have := sq_le_sq' (abs_le.1 hα1).1 (abs_le.1 hα1).2
        exact this
      have := mul_le_mul_of_nonneg_right this (sq_nonneg ‖H‖)
      exact mul_le_mul_of_nonneg_left this hB0
  have hDH : ‖fderiv ℝ F H H‖ ≤ B * ‖H‖ :=
    ((fderiv ℝ F H).le_opNorm H).trans (mul_le_mul_of_nonneg_right (h1 H) (norm_nonneg _))
  have T3 : ‖((α - 1 + h / 2 : ℝ) : ℂ) * fderiv ℝ F H H‖ ≤ h ^ 2 * (B * ‖H‖) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hα2 hDH (norm_nonneg _) (by positivity)
  have T4 : ‖(((s ^ 2 - h) / 2 : ℝ) : ℂ) * Qc‖ ≤ h ^ 2 * (B * m2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    calc |s ^ 2 - h| / 2 * ‖Qc‖ ≤ h ^ 2 * ‖Qc‖ := by
          gcongr
          linarith [abs_nonneg (s ^ 2 - h)]
      _ ≤ h ^ 2 * (B * m2) := mul_le_mul_of_nonneg_left hQcb (by positivity)
  have T5 : ‖((h / 2 : ℝ) : ℂ) * (Qc - QH)‖ ≤ h ^ 2 * (B * (‖H‖ * m2)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    calc h / 2 * ‖Qc - QH‖ ≤ h / 2 * (B * (h * ‖H‖) * m2) := by
          gcongr
      _ ≤ h ^ 2 * (B * (‖H‖ * m2)) := by
          have : 0 ≤ B * (‖H‖ * m2) := by positivity
          nlinarith
  -- assembly
  have e : (∫ x, F (c + s • GAM_arr D N x) ∂γ) - F H - h * genA F H =
      ((∫ x, F (c + s • GAM_arr D N x) ∂γ) - F c - ((s ^ 2 / 2 : ℝ) : ℂ) * Qc) +
      (F c - F H - ((α - 1 : ℝ) : ℂ) * fderiv ℝ F H H) +
      ((α - 1 + h / 2 : ℝ) : ℂ) * fderiv ℝ F H H +
      (((s ^ 2 - h) / 2 : ℝ) : ℂ) * Qc +
      ((h / 2 : ℝ) : ℂ) * (Qc - QH) := by
    rw [hgen]
    push_cast
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add T1' T2)) T3)) T4)) T5).trans ?_
  set W := (1 + ‖H‖) ^ 4 with hW
  set P4 := ((D : ℝ) * N + 1) ^ 4 with hP4
  have hw0 : 0 ≤ ‖H‖ := norm_nonneg H
  have hW1 : 1 ≤ W := one_le_pow₀ (by linarith)
  have hWw : ‖H‖ ≤ W := by
    calc ‖H‖ ≤ 1 + ‖H‖ := by linarith
      _ ≤ (1 + ‖H‖) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hWw2 : ‖H‖ ^ 2 ≤ W := by
    calc ‖H‖ ^ 2 ≤ (1 + ‖H‖) ^ 2 := pow_le_pow_left₀ hw0 (by linarith) 2
      _ ≤ (1 + ‖H‖) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hDN0 : (0 : ℝ) ≤ D * N := by positivity
  have hP1 : 1 ≤ P4 := one_le_pow₀ (by linarith)
  have hncP : nc ≤ 2 * P4 := by
    have hn1 : D * N ≤ (D * N + 1) ^ 4 :=
      (Nat.le_succ _).trans (Nat.le_self_pow (by norm_num) _)
    have hn2 : D * N * N ≤ (D * N + 1) ^ 4 := by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · simp [hD]
      · calc D * N * N ≤ (D * N) * (D * N) :=
              Nat.mul_le_mul_left (D * N) (Nat.le_mul_of_pos_left N hD)
          _ ≤ (D * N + 1) * (D * N + 1) := Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
          _ = (D * N + 1) ^ 2 := by ring
          _ ≤ (D * N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have r1 : (D : ℝ) * N ≤ P4 := by rw [hP4]; exact_mod_cast hn1
    have r2 : (D : ℝ) * N * N ≤ P4 := by rw [hP4]; exact_mod_cast hn2
    rw [hnc]
    linarith
  have hX : 0 ≤ B * h ^ 2 := by positivity
  have hP0 : 0 ≤ P4 := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hWP : W ≤ W * P4 := le_mul_of_one_le_right hW0 hP1
  have hPW : P4 ≤ W * P4 := le_mul_of_one_le_left hP0 hW1
  have hWP1 : 1 ≤ W * P4 := hP1.trans hPW
  have i1 : nc * M ≤ 2 * M * (W * P4) := by
    have a1 : nc * M ≤ 2 * P4 * M := mul_le_mul_of_nonneg_right hncP hM0
    have a2 : 2 * P4 * M ≤ 2 * (W * P4) * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    linarith
  have i2 : ‖H‖ ^ 2 ≤ W * P4 := hWw2.trans hWP
  have i3 : ‖H‖ ≤ W * P4 := hWw.trans hWP
  have i4 : m2 ≤ (1 + 2 * M) * (W * P4) := by linarith
  have i5 : nc * ‖H‖ ≤ 2 * (W * P4) := by
    have : nc * ‖H‖ ≤ 2 * P4 * W := mul_le_mul hncP hWw hw0 (by positivity)
    linarith
  have i6 : ‖H‖ * m2 ≤ (1 + 2 * M) * (W * P4) := by
    have a1 : ‖H‖ * m2 ≤ ‖H‖ * (1 + nc * M) := mul_le_mul_of_nonneg_left hm2le hw0
    have a2 : M * (nc * ‖H‖) ≤ M * (2 * (W * P4)) := mul_le_mul_of_nonneg_left i5 hM0
    linarith
  have hin : nc * M + ‖H‖ ^ 2 + ‖H‖ + m2 + ‖H‖ * m2 ≤ (6 * M + 4) * (W * P4) := by
    linarith
  calc h ^ 2 * (B * (nc * M)) + B * (h ^ 2 * ‖H‖ ^ 2) + h ^ 2 * (B * ‖H‖) + h ^ 2 * (B * m2) +
        h ^ 2 * (B * (‖H‖ * m2))
      = (B * h ^ 2) * (nc * M + ‖H‖ ^ 2 + ‖H‖ + m2 + ‖H‖ * m2) := by ring
    _ ≤ (B * h ^ 2) * ((6 * M + 4) * (W * P4)) := mul_le_mul_of_nonneg_left hin hX
    _ = (6 * M + 4) * B * h ^ 2 * W * P4 := by ring

/-- Azuma–Hoeffding for the stopped linear martingale part on the grid with initial law `μ₀`:
with `σ` a grid stopping time and `E_X (a_k X)² ≤ c_k` on `{k < σ}`,
`P(Σ_{k<n} 1_{k<σ} a_k(X_{k+1}) ≥ ε) ≤ exp(-ε²/(2 Σ c_k))`. -/
theorem gridAzumaA_stopped (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] (a : ℕ → GridΩA D N K → (Fin D → Coords N) →L[ℝ] ℝ)
    (ha : ∀ k, StronglyMeasurable[gridFiltrA D N K k] (a k)) (σ : GridΩA D N K → WithTop ℕ)
    (hσ : IsStoppingTime (gridFiltrationA D N K) σ) (c : ℕ → ℝ≥0)
    (hc : ∀ (k : ℕ) ω, (k : WithTop ℕ) < σ ω → ∫ x, (a k ω x) ^ 2 ∂(gueBlocks D N) ≤ c k)
    (n : ℕ) (hn : n ≤ K) (ε : ℝ) (hε : 0 ≤ ε) :
    (gridLawA D N K μ₀).real {ω | ε ≤ ∑ k ∈ Finset.range n,
        if hk : k < K then (if (k : WithTop ℕ) < σ ω then a k ω (ω.2 ⟨k, hk⟩) else 0) else 0} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ k ∈ Finset.range n, (c k : ℝ))) := by
  set μ := gridLawA D N K μ₀ with hμ
  rcases Nat.eq_zero_or_pos K with hK | hK
  · have hn0 : n = 0 := by omega
    subst hn0
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, div_zero, Real.exp_zero]
    exact measureReal_le_one
  set Y : ℕ → GridΩA D N K → ℝ := fun k ω =>
    if hk : k < K then (if (k : WithTop ℕ) < σ ω then a k ω (ω.2 ⟨k, hk⟩) else 0) else 0
    with hYdef
  have hYind : ∀ k (hk : k < K), Y k =
      {ω | (k : WithTop ℕ) < σ ω}.indicator fun ω => a k ω (ω.2 ⟨k, hk⟩) := by
    intro k hk
    funext ω
    simp only [Y, hk, ↓reduceDIte, Set.indicator_apply, Set.mem_ofPred_eq]
  set ℱ : Filtration ℕ (inferInstance : MeasurableSpace (GridΩA D N K)) :=
    ⟨fun i => gridFiltrA D N K (i + 1), fun i j hij => (gridFiltrA_mono D N K).1 (by omega),
      fun i => (gridFiltrA_mono D N K).2 (i + 1)⟩ with hℱ
  have hadapt : StronglyAdapted ℱ Y := by
    intro i
    change StronglyMeasurable[gridFiltrA D N K (i + 1)] (Y i)
    by_cases hi : i < K
    · rw [hYind i hi]
      have hle : gridFiltrA D N K i ≤ gridFiltrA D N K (i + 1) :=
        (gridFiltrA_mono D N K).1 (by omega)
      have h1 : StronglyMeasurable[gridFiltrA D N K (i + 1)] fun ω => (a i ω, ω.2 ⟨i, hi⟩) :=
        ((ha i).mono hle).prodMk (GAM_incr_meas D N K i hi).stronglyMeasurable
      have h2 : Continuous fun q : ((Fin D → Coords N) →L[ℝ] ℝ) × (Fin D → Coords N) => q.1 q.2 :=
        continuous_fst.clm_apply continuous_snd
      exact (h2.comp_stronglyMeasurable h1).indicator (hle _ (hσ.measurableSet_gt i))
    · have : Y i = fun _ => 0 := funext fun ω => by simp only [Y, hi, ↓reduceDIte]
      rw [this]
      exact stronglyMeasurable_const
  have hsub : ∀ k (hk : k < K), HasCondSubgaussianMGF (gridFiltrA D N K k)
      ((gridFiltrA_mono D N K).2 k) (Y k) (c k) μ := by
    intro k hk
    rw [hYind k hk]
    exact gridCondSubGA D N K μ₀ k hk (a k) (ha k) _ (hσ.measurableSet_gt k) (c k)
      fun ω hω => hc k ω hω
  have h0 : HasSubgaussianMGF (Y 0) (c 0) μ := by
    have hm0 := (gridFiltrA_mono D N K).2 0
    have : IsProbabilityMeasure (μ.trim hm0) :=
      ⟨by rw [trim_measurableSet_eq hm0 MeasurableSet.univ, measure_univ]⟩
    have := HasSubgaussianMGF.add_of_hasCondSubgaussianMGF hm0
      (HasSubgaussianMGF.zero (μ := μ.trim hm0)) (hsub 0 hK)
    simpa using this
  have hsubG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (c (i + 1)) μ :=
    fun i hi => hsub (i + 1) (by omega)
  have := measure_sum_ge_le_of_hasCondSubgaussianMGF hadapt h0 n hsubG hε
  simpa [Y, NNReal.coe_sum] using this

end RBMTransitionEdge

end
