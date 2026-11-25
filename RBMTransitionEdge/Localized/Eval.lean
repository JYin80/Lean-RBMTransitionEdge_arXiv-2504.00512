module

public import RBMTransitionEdge.LocalLaw.Wigner
public import RBMTransitionEdge.Localized.Pathwise
public import RBMTransitionEdge.Localized.QuantIncrement
public import RBMTransitionEdge.Localized.Reflect
public import RBMTransitionEdge.Tools.EigDeriv
public import RBMTransitionEdge.Localized.LocalLaw
public import RBMTransitionEdge.Det.QuantSpacing

@[expose] public section

/-!
# Theorem 2.5 on the half range

Theorem 2.5 [theorem_localized_eigenvalue] for `2k ≤ DN + 1`: the eigenvalue `λ_k` of
`H_Λ` moves by the shift `Δ` up to a small error ((2.10), (2.11)), and the local correlation
functions near the edge are those of the blocks, from Lemma 5.4
[lemma_localized_eigenvalue_local_law] along the line `t ↦ H + tΛ`, rigidity and the quantile
increments.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

section Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖X‖ ≤ ‖X‖_HS`. -/
private lemma Ev_op_le_hs (X : Matrix ι ι ℂ) : opNorm X ≤ hsNorm X := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  obtain ⟨x, rfl⟩ : ∃ x : ι → ℂ, v = WithLp.toLp 2 x := ⟨v.ofLp, rfl⟩
  rw [Matrix.toEuclideanCLM_toLp]
  have hsq : ‖(WithLp.toLp 2 (X *ᵥ x) : EuclideanSpace ℂ ι)‖ ^ 2 ≤
      (hsNorm X * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, hsNorm,
      Real.sq_sqrt (by positivity), Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => ?_
    have h1 : ‖(X *ᵥ x) p‖ ≤ ∑ q, ‖X p q‖ * ‖x q‖ := by
      simp only [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun q => ‖X p q‖) (fun q => ‖x q‖)
    calc ‖(X *ᵥ x) p‖ ^ 2 ≤ (Real.sqrt (∑ q, ‖X p q‖ ^ 2) * Real.sqrt (∑ q, ‖x q‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
      _ = (∑ q, ‖X p q‖ ^ 2) * ∑ q, ‖x q‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    two_ne_zero).1 hsq

/-- `|⟨X⟩| ≤ ‖X‖`. -/
private lemma Ev_ntr_le (X : Matrix ι ι ℂ) : ‖ntr X‖ ≤ opNorm X := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp [ntr, Matrix.trace, opNorm]
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    unfold ntr Matrix.trace
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, X.diag i‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, opNorm X := by
          gcongr
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun i _ => norm_apply_le_opNorm X i i)
      _ = opNorm X := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

/-- The operator norm is submultiplicative. -/
private lemma Ev_opNorm_mul (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  unfold opNorm
  rw [map_mul]
  exact norm_mul_le _ _

/-- The matrix inverse is a measurable map. -/
private lemma Ev_meas_inv : Measurable (fun A : Matrix ι ι ℂ => A⁻¹) := by
  have h : (fun A : Matrix ι ι ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (continuous_id.matrix_det.measurable.inv).mul
    (continuous_id.matrix_adjugate.measurable.eval_matrix)

/-- `X ↦ λ_k(X)` along a continuous family of Hermitian matrices is continuous (Weyl). -/
private lemma Ev_eigK_cont {α : Type*} [TopologicalSpace α] (M : α → Matrix ι ι ℂ)
    (hM : Continuous M) (hH : ∀ x, (M x).IsHermitian) (k : ℕ) :
    Continuous fun x => eigK (M x) k := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Continuous fun y => hsNorm (M y - M x) := by
    unfold hsNorm
    fun_prop
  have h0 : hsNorm (M x - M x) = 0 := by simp [hsNorm]
  refine squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) (h0 ▸ hc.tendsto x)
  rw [Real.dist_eq]
  have := eigK_add_sub_le (M x) (M y - M x) (hH x) ((hH y).sub (hH x)) k
  rw [add_sub_cancel] at this
  exact this.trans (Ev_op_le_hs _)

/-- The eigenvalues `λ_1 ≥ λ_2 ≥ ⋯` of a Hermitian matrix are ordered. -/
private lemma Ev_eigK_anti (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i ≤ j) (hj : j ≤ Fintype.card ι) : eigK X j ≤ eigK X i := by
  have hi' : i - 1 < Fintype.card ι := by omega
  have hj' : j - 1 < Fintype.card ι := by omega
  simp only [eigK, hi', hj', dite_true, eigs, hX]
  exact hX.eigenvalues₀_antitone (show (⟨i - 1, hi'⟩ : Fin _) ≤ ⟨j - 1, hj'⟩ by
    simp only [Fin.mk_le_mk]; omega)

omit [DecidableEq ι] in
/-- A Hermitian matrix on a nonempty index set has a unit eigenvector. -/
private lemma Ev_unit_eigvec [Nonempty ι] (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    ∃ μ : ℝ, ∃ u : ι → ℂ, IsUnitEigvec X μ u := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨hX.eigenvalues i, ⇑(hX.eigenvectorBasis i), ?_, ?_⟩
  · rw [hX.mulVec_eigenvectorBasis i]
    rfl
  · have h1 := (hX.eigenvectorBasis.orthonormal).1 i
    rw [EuclideanSpace.norm_eq] at h1
    have h2 : Real.sqrt (∑ j, ‖(hX.eigenvectorBasis i) j‖ ^ 2) ^ 2 = 1 := by rw [h1]; norm_num
    rwa [Real.sq_sqrt (by positivity)] at h2

/-- `Re ⟨Im G B Im G B⟩ ≥ 0` for Hermitian `X`, `B`, `G = (X - γ - iη)⁻¹`, `η > 0`: the right
side of the first inequality of (5.26) [bdwgy] dominates a square. -/
private lemma Ev_loop_nonneg [Nonempty ι] (X B : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (hB : B.IsHermitian) (γ η : ℝ) (hη : 0 < η) :
    0 ≤ (ntr (imRes X ((γ : ℂ) + (η : ℂ) * Complex.I) * B *
      imRes X ((γ : ℂ) + (η : ℂ) * Complex.I) * B)).re := by
  obtain ⟨μ, u, hu⟩ := Ev_unit_eigvec X hX
  have h := eig_form_sq_le X B hX hB μ u hu γ η hη
  have hf : 0 < ((μ - γ) ^ 2 + η ^ 2) ^ 2 / η ^ 2 := by positivity
  have htr : 0 ≤ (Matrix.trace (imRes X ((γ : ℂ) + (η : ℂ) * Complex.I) * B *
      imRes X ((γ : ℂ) + (η : ℂ) * Complex.I) * B)).re := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hf hneg
    linarith [sq_nonneg ‖star u ⬝ᵥ (B *ᵥ u)‖]
  unfold ntr
  rw [show ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  positivity

end Mat

/-- The quantiles (2.20) [eq:gammak] of a probability density decrease in the index. -/
private lemma Ev_quant_anti (ρ : ℝ → ℝ) (hnn : ∀ x, 0 ≤ ρ x) (hint : Integrable ρ)
    (hmass : ∫ x, ρ x = 1) (Mc i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ Mc) :
    quant ρ Mc j ≤ quant ρ Mc i := by
  have hMc : (0 : ℝ) < Mc := by exact_mod_cast (show 0 < Mc by omega)
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hj' : (j : ℝ) ≤ Mc := by exact_mod_cast hj
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hpi : 0 < ((i : ℝ) - 1 / 2) / Mc := div_pos (by linarith) hMc
  have hpj : ((j : ℝ) - 1 / 2) / Mc < 1 := by rw [div_lt_one hMc]; linarith
  have hpij : ((i : ℝ) - 1 / 2) / Mc ≤ ((j : ℝ) - 1 / 2) / Mc := by gcongr
  have hFanti : ∀ x y : ℝ, x ≤ y → ∫ E in Set.Ioi y, ρ E ≤ ∫ E in Set.Ioi x, ρ E :=
    fun x y hxy => setIntegral_mono_set hint.integrableOn (ae_of_all _ fun _ => hnn _)
      (Filter.Eventually.of_forall fun z hz => Set.Ioi_subset_Ioi hxy hz)
  have h1 : Tendsto (fun n : ℕ => ∫ E in Set.Ioi (-(n : ℝ)), ρ E) atTop (𝓝 1) := by
    have := tendsto_setIntegral_of_monotone (μ := volume) (f := ρ)
      (s := fun n : ℕ => Set.Ioi (-(n : ℝ))) (fun _ => measurableSet_Ioi)
      (fun a b hab => Set.Ioi_subset_Ioi (by simp only [neg_le_neg_iff]; exact_mod_cast hab))
      hint.integrableOn
    have hU : (⋃ n : ℕ, Set.Ioi (-(n : ℝ))) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_Ioi, Set.mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact ⟨n, by linarith⟩
    rwa [hU, Measure.restrict_univ, hmass] at this
  have h0 : Tendsto (fun n : ℕ => ∫ E in Set.Ioi (n : ℝ), ρ E) atTop (𝓝 0) := by
    have := tendsto_setIntegral_of_antitone (μ := volume) (f := ρ)
      (s := fun n : ℕ => Set.Ioi (n : ℝ)) (fun _ => measurableSet_Ioi)
      (fun a b hab => Set.Ioi_subset_Ioi (by exact_mod_cast hab)) ⟨0, hint.integrableOn⟩
    have hI : (⋂ n : ℕ, Set.Ioi (n : ℝ)) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_forall,
        not_lt]
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact ⟨n, hn.le⟩
    rwa [hI, Measure.restrict_empty, integral_zero_measure] at this
  obtain ⟨n1, hn1⟩ := (h1.eventually (lt_mem_nhds hpj)).exists
  obtain ⟨n0, hn0⟩ := (h0.eventually (gt_mem_nhds hpi)).exists
  unfold quant
  apply csSup_le_csSup
  · refine ⟨n0, fun x hx => ?_⟩
    by_contra h
    push Not at h
    have := hFanti _ _ h.le
    simp only [Set.mem_ofPred_eq] at hx
    linarith
  · exact ⟨-(n1 : ℝ), by simp only [Set.mem_ofPred_eq]; exact hn1.le⟩
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    linarith

/-- The block matrix `H` of (1.3) [matrix_H] depends continuously on the coordinates. -/
private lemma Ev_blockH_cont (D N : ℕ) : Continuous (blockH D N) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [blockH, wig]
  split_ifs <;> fun_prop

/-- `Λ(0) = 0`. -/
private lemma Ev_lam_zero (D N : ℕ) : lam D N (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
  ext p q
  simp [lam]

/-- The block matrix `H` is Hermitian. -/
private lemma Ev_blockH_herm (D N : ℕ) (w : Fin D → Coords N) : (blockH D N w).IsHermitian := by
  have h := HLam_isHermitian D N 0 w
  rwa [HLam, Ev_lam_zero, add_zero] at h

/-- `t Λ` is Hermitian for real `t`. -/
private lemma Ev_smul_herm {ι : Type*} {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) (t : ℝ) : ((t : ℂ) • X).IsHermitian :=
  hX.smul (Complex.conj_ofReal t)

/-- `Λ - d` is Hermitian for real `d`. -/
private lemma Ev_sub_herm {ι : Type*} [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) (d : ℝ) : (X - (d : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian :=
  hX.sub (Ev_smul_herm isHermitian_one d)

/-- The card of the index set is `DN`. -/
private lemma Ev_card (D N : ℕ) : Fintype.card (Idx D N) = D * N := by
  simp [Idx]

/-- Cauchy–Schwarz on `(0, 1]`: `(∫ φ)² ≤ ∫ φ²`. -/
private lemma Ev_cs (φ : ℝ → ℝ) (h1 : IntegrableOn φ (Set.Ioc 0 1))
    (h2 : IntegrableOn (fun t => φ t ^ 2) (Set.Ioc 0 1)) :
    (∫ t in Set.Ioc (0 : ℝ) 1, φ t) ^ 2 ≤ ∫ t in Set.Ioc (0 : ℝ) 1, φ t ^ 2 := by
  set m := ∫ t in Set.Ioc (0 : ℝ) 1, φ t
  have h0 : 0 ≤ ∫ t in Set.Ioc (0 : ℝ) 1, (φ t - m) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
  have hc : IntegrableOn (fun _ : ℝ => m ^ 2) (Set.Ioc 0 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have e : ∀ t, (φ t - m) ^ 2 = (φ t ^ 2 - 2 * m * φ t) + m ^ 2 := fun t => by ring
  have hA : IntegrableOn (fun t => φ t ^ 2 - 2 * m * φ t) (Set.Ioc 0 1) := h2.sub (h1.const_mul _)
  simp_rw [e] at h0
  rw [integral_add hA hc, integral_sub h2 (h1.const_mul _), integral_const_mul,
    setIntegral_const] at h0
  simp only [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one, one_smul,
    measureReal_def] at h0
  nlinarith

/-- `Re tr B = n Re ⟨B⟩`. -/
private lemma Ev_trace_re {ι : Type*} [Fintype ι] [Nonempty ι] (B : Matrix ι ι ℂ) :
    (Matrix.trace B).re = (Fintype.card ι : ℝ) * (ntr B).re := by
  have hc : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Matrix.trace B = (Fintype.card ι : ℂ) * ntr B := by
    unfold ntr
    field_simp
  rw [this, show ((Fintype.card ι : ℂ)) = ((Fintype.card ι : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul]

/-- The pathwise inequality behind (5.24) [ygfyz] and (5.26) [bdwgy]: along `t ↦ H + tΛ`, with
a bounded integrable shift `Δ`, `(λ_k(H + Λ) - λ_k(H) - ∫₀¹ Δ)²` is at most the time integral of
`4η² n ⟨Im G_t Λ̂_t Im G_t Λ̂_t⟩`, `G_t = (H + tΛ - γ(t) - iη)⁻¹`, `Λ̂_t = Λ - Δ(t)`, plus
`(‖Λ‖ + sup |Δ|)²` at the times where `|λ_k(H + tΛ) - γ(t)| > η`. -/
private lemma Ev_path {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H Λ : Matrix ι ι ℂ) (hH : H.IsHermitian) (hΛ : Λ.IsHermitian) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card ι) (Δ γ : ℝ → ℝ) (η K₂ : ℝ) (hη : 0 < η)
    (hΔi : IntegrableOn Δ (Set.Ioc 0 1)) (hΔb : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |Δ t| ≤ K₂) :
    ENNReal.ofReal ((eigK (H + Λ) k - eigK H k - ∫ t in Set.Ioc (0 : ℝ) 1, Δ t) ^ 2) ≤
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, (ENNReal.ofReal (4 * η ^ 2 * (Fintype.card ι : ℝ) *
          (ntr (imRes (H + (t : ℂ) • Λ) ((γ t : ℂ) + (η : ℂ) * Complex.I) *
            (Λ - (Δ t : ℂ) • (1 : Matrix ι ι ℂ)) *
            imRes (H + (t : ℂ) • Λ) ((γ t : ℂ) + (η : ℂ) * Complex.I) *
            (Λ - (Δ t : ℂ) • (1 : Matrix ι ι ℂ)))).re) +
        ENNReal.ofReal ((opNorm Λ + K₂) ^ 2) *
          Set.indicator {t : ℝ | η < |eigK (H + (t : ℂ) • Λ) k - γ t|} 1 t) := by
  set f : ℝ → ℝ := fun s => eigK (H + (s : ℂ) • Λ) k with hf
  have hn : 0 ≤ opNorm Λ := norm_nonneg _
  have hlip : LipschitzWith (Real.toNNReal (opNorm Λ)) f := by
    refine LipschitzWith.of_dist_le_mul fun s s' => ?_
    have := eigK_line_lipschitz H Λ hH hΛ k s s'
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hn]
    linarith [mul_comm |s - s'| (opNorm Λ)]
  have hdb : ∀ t, |deriv f t| ≤ opNorm Λ := fun t => by
    have := norm_deriv_le_of_lipschitz (x₀ := t) hlip
    rwa [Real.norm_eq_abs, Real.coe_toNNReal _ hn] at this
  have hdi : IntegrableOn (deriv f) (Set.Ioc 0 1) :=
    Measure.integrableOn_of_bounded (M := opNorm Λ) measure_Ioc_lt_top.ne
      (measurable_deriv f).aestronglyMeasurable
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hdb t)
  have hftc := eigK_line_ftc H Λ hH hΛ k
  rw [intervalIntegral.integral_of_le zero_le_one] at hftc
  set φ : ℝ → ℝ := fun t => deriv f t - Δ t with hφ
  have hφi : IntegrableOn φ (Set.Ioc 0 1) := hdi.sub hΔi
  have hY : eigK (H + Λ) k - eigK H k - ∫ t in Set.Ioc (0 : ℝ) 1, Δ t =
      ∫ t in Set.Ioc (0 : ℝ) 1, φ t := by
    rw [hftc, hφ, integral_sub hdi hΔi]
  have hφb : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |φ t| ≤ opNorm Λ + K₂ := fun t ht =>
    (abs_sub _ _).trans (add_le_add (hdb t) (hΔb t ht))
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc 0 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hφ2i : IntegrableOn (fun t => φ t ^ 2) (Set.Ioc 0 1) := by
    refine Integrable.of_bound (hφi.aestronglyMeasurable.pow 2) ((opNorm Λ + K₂) ^ 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hφb t ht) 2
  rw [hY]
  calc ENNReal.ofReal ((∫ t in Set.Ioc (0 : ℝ) 1, φ t) ^ 2)
      ≤ ENNReal.ofReal (∫ t in Set.Ioc (0 : ℝ) 1, φ t ^ 2) :=
        ENNReal.ofReal_le_ofReal (Ev_cs φ hφi hφ2i)
    _ = ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (φ t ^ 2) :=
        ofReal_integral_eq_lintegral_ofReal hφ2i (ae_of_all _ fun _ => sq_nonneg _)
    _ ≤ _ := by
      refine lintegral_mono_ae ?_
      have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), DifferentiableAt ℝ f t :=
        hlip.ae_differentiableAt_real
      filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hdiff] with t ht hdt
      obtain ⟨u, hu, hd⟩ := eigK_line_deriv H Λ hH hΛ k hk1 hk t (deriv f t) hdt.hasDerivAt
      have hX : (H + (t : ℂ) • Λ).IsHermitian := hH.add (Ev_smul_herm hΛ t)
      have hB := Ev_sub_herm hΛ (Δ t)
      have huu : star u ⬝ᵥ u = (1 : ℂ) := by
        have h2 := hu.2
        simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
        have h3 := congrArg (fun r : ℝ => (r : ℂ)) h2
        push_cast at h3
        exact h3
      have hφu : φ t = (star u ⬝ᵥ ((Λ - (Δ t : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ u)).re := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
          dotProduct_smul, huu, Complex.sub_re, smul_eq_mul, mul_one, Complex.ofReal_re, ← hd]
      have hle := eig_form_sq_le _ _ hX hB _ u hu (γ t) η hη
      rw [Ev_trace_re] at hle
      set T := (ntr (imRes (H + (t : ℂ) • Λ) ((γ t : ℂ) + (η : ℂ) * Complex.I) *
            (Λ - (Δ t : ℂ) • (1 : Matrix ι ι ℂ)) *
            imRes (H + (t : ℂ) • Λ) ((γ t : ℂ) + (η : ℂ) * Complex.I) *
            (Λ - (Δ t : ℂ) • (1 : Matrix ι ι ℂ)))).re with hT
      have hsq : φ t ^ 2 ≤ ‖star u ⬝ᵥ ((Λ - (Δ t : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ u)‖ ^ 2 := by
        rw [hφu, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
      by_cases hr : η < |eigK (H + (t : ℂ) • Λ) k - γ t|
      · have hind : Set.indicator {t : ℝ | η < |eigK (H + (t : ℂ) • Λ) k - γ t|} (1 : ℝ → ENNReal) t
            = 1 := Set.indicator_of_mem hr _
        rw [hind, mul_one]
        refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hφb t ht) 2
      · push Not at hr
        refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
        have hf0 : 0 < ((eigK (H + (t : ℂ) • Λ) k - γ t) ^ 2 + η ^ 2) ^ 2 / η ^ 2 := by
          positivity
        have hT0 : 0 ≤ (Fintype.card ι : ℝ) * T := by
          by_contra hneg
          push Not at hneg
          have := mul_neg_of_pos_of_neg hf0 hneg
          nlinarith [sq_nonneg ‖star u ⬝ᵥ ((Λ - (Δ t : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ u)‖]
        have hfac : ((eigK (H + (t : ℂ) • Λ) k - γ t) ^ 2 + η ^ 2) ^ 2 / η ^ 2 ≤ 4 * η ^ 2 := by
          rw [div_le_iff₀ (by positivity)]
          have h1 : (eigK (H + (t : ℂ) • Λ) k - γ t) ^ 2 ≤ η ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr 2
          nlinarith [sq_nonneg (eigK (H + (t : ℂ) • Λ) k - γ t)]
        calc φ t ^ 2 ≤ _ := hsq.trans hle
          _ ≤ 4 * η ^ 2 * ((Fintype.card ι : ℝ) * T) := mul_le_mul_of_nonneg_right hfac hT0
          _ = _ := by ring

/-- The clamp `t ↦ min (max t 0) 1` onto `[0, 1]`. -/
private abbrev Ev_cl (t : ℝ) : ℝ := (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)

private lemma Ev_cl_cont : Continuous Ev_cl :=
  continuous_subtype_val.comp continuous_projIcc

private lemma Ev_cl_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : Ev_cl t = t := by
  simp only [Ev_cl, Set.projIcc_of_mem _ ht]

private lemma Ev_cl_mem (t : ℝ) : Ev_cl t ∈ Set.Icc (0 : ℝ) 1 :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one t).prop

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Definition 2.10 [def_moving_Lambda] for the clamped family `s Λ`, `s ∈ [0, 1]`: the
quantiles `γ_k(s)` of (2.20) [eq:gammak] and `m_s(z)` depend continuously on `s`. -/
private lemma Ev_family (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    (∀ Mc k : ℕ, 1 ≤ k → k ≤ Mc →
      Continuous fun t => quant (rho (((Ev_cl t : ℝ) : ℂ) • Λ)) Mc k) ∧
    ContinuousOn (fun p : ℝ × ℂ => mSol (((Ev_cl p.1 : ℝ) : ℂ) • Λ) p.2)
      {p : ℝ × ℂ | 0 < p.2.im} := by
  have hc : Continuous fun t => ((Ev_cl t : ℝ) : ℂ) • Λ :=
    (Complex.continuous_ofReal.comp Ev_cl_cont).smul continuous_const
  have hH : ∀ t, (((Ev_cl t : ℝ) : ℂ) • Λ).IsHermitian := fun t => Ev_smul_herm hΛ _
  have hn : ∀ t, opNorm (((Ev_cl t : ℝ) : ℂ) • Λ) ≤ 1 / 10 := by
    intro t
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := Ev_cl_mem t
    rw [abs_of_nonneg h1.1]
    have : 0 ≤ opNorm Λ := norm_nonneg _
    nlinarith [h1.2]
  obtain ⟨-, -, hq, hm⟩ := moving_continuous _ hc hH hn
  exact ⟨hq, hm⟩

omit [DecidableEq ι] [Nonempty ι] in
/-- `M ↦ Re(⟨M Λ M^*⟩ / ⟨M M^*⟩)` is measurable. -/
private lemma Ev_meas_ratio (Λ : Matrix ι ι ℂ) :
    Measurable fun M : Matrix ι ι ℂ => (ntr (M * Λ * Mᴴ) / ntr (M * Mᴴ)).re := by
  have h1 : Continuous fun M : Matrix ι ι ℂ => ntr (M * Λ * Mᴴ) := by
    unfold ntr
    exact continuous_const.mul
      ((continuous_id.matrix_mul continuous_const).matrix_mul
        continuous_id.matrix_conjTranspose).matrix_trace
  have h2 : Continuous fun M : Matrix ι ι ℂ => ntr (M * Mᴴ) := by
    unfold ntr
    exact continuous_const.mul
      (continuous_id.matrix_mul continuous_id.matrix_conjTranspose).matrix_trace
  exact Complex.measurable_re.comp (h1.measurable.div h2.measurable)

end Family

/-- `Im z₁ = η` for `z₁` of (5.1) [eq:z1]. -/
private lemma Ev_zOne_im {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (k : ℕ) (ε : ℝ) :
    (zOne Λ k ε).im = etaK D N k ε := by
  simp only [zOne, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]

/-- The shift `Δ(s)` of (5.19) [definition_shift_eigenvalue] at the clamped time is a measurable
function of `t`. -/
private lemma Ev_shiftT_meas (D N : ℕ) [Nonempty (Idx D N)] (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ D * N)
    (ε : ℝ) (hη : 0 < etaK D N k ε) :
    Measurable fun t : ℝ => shiftT Λ k ε (Ev_cl t) := by
  obtain ⟨hq, hm⟩ := Ev_family Λ hΛ hℓ
  have hzc : Continuous fun t : ℝ => zOne (((Ev_cl t : ℝ) : ℂ) • Λ) k ε := by
    unfold zOne
    exact (Complex.continuous_ofReal.comp (hq (D * N) k hk1 hk)).add continuous_const
  have hzi : ∀ t : ℝ, 0 < (zOne (((Ev_cl t : ℝ) : ℂ) • Λ) k ε).im := fun t => by
    rw [Ev_zOne_im]; exact hη
  have hmc : Continuous fun t : ℝ =>
      mSol (((Ev_cl t : ℝ) : ℂ) • Λ) (zOne (((Ev_cl t : ℝ) : ℂ) • Λ) k ε) :=
    hm.comp_continuous (f := fun t : ℝ => ((t, zOne (((Ev_cl t : ℝ) : ℂ) • Λ) k ε) : ℝ × ℂ))
      (continuous_id.prodMk hzc) fun t => hzi t
  have hc : Continuous fun t : ℝ => ((Ev_cl t : ℝ) : ℂ) • Λ -
      (zOne (((Ev_cl t : ℝ) : ℂ) • Λ) k ε +
        mSol (((Ev_cl t : ℝ) : ℂ) • Λ) (zOne (((Ev_cl t : ℝ) : ℂ) • Λ) k ε)) •
      (1 : Matrix (Idx D N) (Idx D N) ℂ) :=
    ((Complex.continuous_ofReal.comp Ev_cl_cont).smul continuous_const).sub
      ((hzc.add hmc).smul continuous_const)
  have heq : (fun t : ℝ => shiftT Λ k ε (Ev_cl t)) =
      (fun M : Matrix (Idx D N) (Idx D N) ℂ => (ntr (M * Λ * Mᴴ) / ntr (M * Mᴴ)).re) ∘
        (fun M : Matrix (Idx D N) (Idx D N) ℂ => M⁻¹) ∘ (fun t : ℝ => ((Ev_cl t : ℝ) : ℂ) • Λ -
          (zOne (((Ev_cl t : ℝ) : ℂ) • Λ) k ε +
            mSol (((Ev_cl t : ℝ) : ℂ) • Λ) (zOne (((Ev_cl t : ℝ) : ℂ) • Λ) k ε)) •
          (1 : Matrix (Idx D N) (Idx D N) ℂ)) := by
    funext t
    simp only [Function.comp_apply, shiftT, MExt, mExt, ite_eq_left (hzi t)]
  rw [heq]
  exact (Ev_meas_ratio Λ).comp (Ev_meas_inv.comp hc.measurable)

/-- The integrand of (5.23) [estimate_localized_eigenvalue_local_law] at the clamped time is a
jointly measurable function of the coordinates and the time. -/
private lemma Ev_evalLoop_meas (D N : ℕ) [Nonempty (Idx D N)] (A : Matrix (Fin N) (Fin N) ℂ)
    (hℓ : opNorm (lam D N A) ≤ 1 / 10) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ D * N) (ε : ℝ)
    (hη : 0 < etaK D N k ε) :
    Measurable fun p : (Fin D → Coords N) × ℝ => evalLoop D N A k ε (Ev_cl p.2) p.1 := by
  set Λ := lam D N A with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N A
  obtain ⟨hq, -⟩ := Ev_family Λ hΛ hℓ
  have hd : Measurable fun p : (Fin D → Coords N) × ℝ => shiftT Λ k ε (Ev_cl p.2) :=
    (Ev_shiftT_meas D N Λ hΛ hℓ k hk1 hk ε hη).comp measurable_snd
  have hzc : Continuous fun t : ℝ => zOne (((Ev_cl t : ℝ) : ℂ) • Λ) k ε := by
    simp only [zOne]
    exact (Complex.continuous_ofReal.comp (hq (D * N) k hk1 hk)).add continuous_const
  have hR : Measurable fun p : (Fin D → Coords N) × ℝ =>
      res (blockH D N p.1 + ((Ev_cl p.2 : ℝ) : ℂ) • Λ) (zOne (((Ev_cl p.2 : ℝ) : ℂ) • Λ) k ε) := by
    refine Ev_meas_inv.comp (Continuous.measurable ?_)
    exact (((Ev_blockH_cont D N).comp continuous_fst).add
      ((Complex.continuous_ofReal.comp (Ev_cl_cont.comp continuous_snd)).smul continuous_const)).sub
      ((hzc.comp continuous_snd).smul continuous_const)
  have hΨ : Continuous fun q : Matrix (Idx D N) (Idx D N) ℂ × ℝ =>
      (ntr ((2 * Complex.I)⁻¹ • (q.1 - q.1ᴴ) *
        (Λ - (q.2 : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
        ((2 * Complex.I)⁻¹ • (q.1 - q.1ᴴ)) *
        (Λ - (q.2 : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))).re := by
    unfold ntr
    have hA : Continuous fun q : Matrix (Idx D N) (Idx D N) ℂ × ℝ =>
        (2 * Complex.I)⁻¹ • (q.1 - q.1ᴴ) :=
      by fun_prop
    have hB : Continuous fun q : Matrix (Idx D N) (Idx D N) ℂ × ℝ =>
        Λ - (q.2 : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ) :=
      continuous_const.sub ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_const)
    exact Complex.continuous_re.comp (continuous_const.mul
      (((hA.matrix_mul hB).matrix_mul hA).matrix_mul hB).matrix_trace)
  have heq : (fun p : (Fin D → Coords N) × ℝ => evalLoop D N A k ε (Ev_cl p.2) p.1) =
      (fun q : Matrix (Idx D N) (Idx D N) ℂ × ℝ =>
        (ntr ((2 * Complex.I)⁻¹ • (q.1 - q.1ᴴ) *
          (Λ - (q.2 : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
          ((2 * Complex.I)⁻¹ • (q.1 - q.1ᴴ)) *
          (Λ - (q.2 : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))).re) ∘
      (fun p : (Fin D → Coords N) × ℝ =>
        (res (blockH D N p.1 + ((Ev_cl p.2 : ℝ) : ℂ) • Λ) (zOne (((Ev_cl p.2 : ℝ) : ℂ) • Λ) k ε),
          shiftT Λ k ε (Ev_cl p.2))) := by
    funext p
    simp only [evalLoop, imRes, Function.comp, hΛdef]
  rw [heq]
  exact hΨ.measurable.comp (hR.prodMk hd)

/-- The integrand of (5.23) [estimate_localized_eigenvalue_local_law] at a fixed clamped time is
measurable in the coordinates. -/
private lemma Ev_evalLoop_meas_t (D N : ℕ) [Nonempty (Idx D N)] (A : Matrix (Fin N) (Fin N) ℂ)
    (hℓ : opNorm (lam D N A) ≤ 1 / 10) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ D * N) (ε : ℝ)
    (hη : 0 < etaK D N k ε) (t : ℝ) :
    Measurable fun w : Fin D → Coords N => evalLoop D N A k ε (Ev_cl t) w := by
  have h := (Ev_evalLoop_meas D N A hℓ k hk1 hk ε hη).comp (measurable_prodMk_right (y := t))
  simp only [Function.comp_def] at h
  exact h

/-- Eventually `K ≤ N^a`, for `a > 0`. -/
private lemma Ev_ev (a K : ℝ) (ha : 0 < a) : ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) ^ a :=
  ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop K)

/-- `𝔯(k) = k` of (1.4) [eq:rk] for `2k ≤ DN + 1`. -/
private lemma Ev_rk_half (D N k : ℕ) (hk : 2 * k ≤ D * N + 1) : rk D N k = k := by
  unfold rk
  rw [min_eq_left (by omega)]

/-- The integrand `⟨Im G_t Λ̂_t Im G_t Λ̂_t⟩` of (5.23) [estimate_localized_eigenvalue_local_law] is
nonnegative. -/
private lemma Ev_evalLoop_nonneg (D N : ℕ) [Nonempty (Idx D N)] (A : Matrix (Fin N) (Fin N) ℂ)
    (k : ℕ) (ε t : ℝ) (hη : 0 < etaK D N k ε) (w : Fin D → Coords N) :
    0 ≤ evalLoop D N A k ε t w :=
  Ev_loop_nonneg _ _ ((Ev_blockH_herm D N w).add (Ev_smul_herm (lam_isHermitian D N A) t))
    (Ev_sub_herm (lam_isHermitian D N A) _) _ _ hη

/-- `‖A‖_HS = 0` forces `A = 0`. -/
private lemma Ev_hs_zero {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (h : hsNorm A = 0) : A = 0 := by
  unfold hsNorm at h
  rw [Real.sqrt_eq_zero'] at h
  have h0 : ∑ i, ∑ j, ‖A i j‖ ^ 2 = 0 := le_antisymm h (by positivity)
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h0 i
    (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h1 j
    (Finset.mem_univ _)
  simpa using h2

/-- The shift `X` of Theorem 2.5 [theorem_localized_eigenvalue] vanishes at `A = 0`. -/
private lemma Ev_shiftX_zero (D N : ℕ) [Nonempty (Idx D N)] (k : ℕ) (w : Fin D → Coords N) :
    shiftX D N 0 k w = 0 := by
  unfold shiftX HLam
  rw [Ev_lam_zero, add_zero, (rho_zero (ι := Idx D N)).2.1]
  ring

set_option maxHeartbeats 1600000 in -- one long assembly of the estimate
/-- (2.10) [eq:local_eigenvalue_perturb] of Theorem 2.5 [theorem_localized_eigenvalue] for
`2k ≤ DN + 1`, from Lemma 5.4 [lemma_localized_eigenvalue_local_law] along `t ↦ H + tΛ`,
(5.24)–(5.26) [ygfyz] [bdwgy], rigidity (2.24) [eq:rigidity] and (A.35)
[modification_shift_eigenvalue]. -/
private lemma Ev_210 (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (C : ℕ → ℝ) (ε ε₀ : ℝ) (hε : 0 < ε) (_hε₀ : 0 < ε₀) (hεε : ε₀ < 2 * ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | (N : ℝ) ^ (-1 + ε) * hsNorm A < |shiftX D N A k w|} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-ε₀)) := by
  obtain ⟨C₅, hC₅, ε₁, hε₁, hLL⟩ := localized_eigenvalue_local_law D hD δA εA hδA hεA C
  set δ : ℝ := 2 * ε - ε₀ with hδdef
  have hδ : 0 < δ := by linarith
  set εL : ℝ := min (min (ε₁ / 2) (εA / 2)) (min (1 / 2) (δ / (4 * (C₅ + 2)))) with hεLdef
  have hεL : 0 < εL :=
    lt_min (lt_min (by linarith) (by linarith)) (lt_min (by norm_num) (by positivity))
  have hεL1 : εL < ε₁ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have hεL2 : εL ≤ εA / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hεL3 : εL ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεL4 : (C₅ + 2) * εL ≤ δ / 4 := by
    have h : εL ≤ δ / (4 * (C₅ + 2)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨N₁, hN₁⟩ := hLL εL hεL hεL1 (δ / 4) (by positivity)
  obtain ⟨Cr, hCr, N₂, hN₂⟩ :=
    regular_estimate_localized_eigenvalue D hD δA εA εL hδA hεA hεL (by linarith)
  obtain ⟨Cm, hCm, N₃, hN₃⟩ :=
    modification_shift_eigenvalue D hD δA εA εL hδA hεA hεL (by linarith)
  obtain ⟨N₄, hN₄⟩ := rigidity D (by omega) δA hδA C εL hεL 3 (by norm_num)
  set K' : ℝ := 2 + 4 * Cr with hK'
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.1 ((Ev_ev δA 20 hδA).and ((Ev_ev ε (4 * Cm) hε).and
    ((Ev_ev (δ / 2) (32 * D) (by positivity)).and (Ev_ev 1 (8 * K' ^ 2 + 2) one_pos))))
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) N₅, fun N hN L A hA k hk1 hk hhs => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hN1', hN2'⟩, hN3', hN4'⟩, hN5'⟩ := hN
  obtain ⟨h20, h4C, h32, hK8⟩ := hN₅ N hN5'
  rw [Real.rpow_one] at hK8
  have hN2 : (2 : ℝ) ≤ N := by nlinarith [sq_nonneg K']
  have hN0 : (0 : ℝ) < N := by linarith
  have hNnat : 1 ≤ N := by exact_mod_cast (by linarith : (1 : ℝ) ≤ N)
  have hkM : k ≤ D * N := by omega
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hrk : rk D N k = k := Ev_rk_half D N k hk
  have hk0 : (1 : ℝ) ≤ rk D N k := by rw [hrk]; exact_mod_cast hk1
  set Λ := lam D N A with hΛdef
  have hΛH : Λ.IsHermitian := lam_isHermitian D N A
  have hδN : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
    rw [Real.rpow_neg hN0.le]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  have hAop : opNorm A ≤ 1 / 20 := hA.trans hδN
  have hop0 : 0 ≤ opNorm A := norm_nonneg _
  have hℓ : opNorm Λ ≤ 1 / 10 := (opNorm_lam_le D N A).trans (by linarith)
  set η := etaK D N k εL with hηdef
  have hη : 0 < η := mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos (by linarith) _)
  set hs := hsNorm A with hhsdef
  have hs0 : 0 ≤ hs := Real.sqrt_nonneg _
  set K₂ := Cr * avgSq Λ with hK₂
  have hΔb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |shiftT Λ k εL t| ≤ K₂ := fun t ht =>
    (hN₂ N hN2' A hA k hk1 hkM hhs t ht).1
  have hAhs : opNorm A ≤ hs := Ev_op_le_hs A
  have hΛop : opNorm Λ ≤ 2 * opNorm A := opNorm_lam_le D N A
  have havg : avgSq Λ ≤ 4 * hs := by
    unfold avgSq
    calc (ntr (Λ * Λ)).re ≤ ‖ntr (Λ * Λ)‖ := Complex.re_le_norm _
      _ ≤ opNorm (Λ * Λ) := Ev_ntr_le _
      _ ≤ opNorm Λ * opNorm Λ := Ev_opNorm_mul _ _
      _ ≤ (2 * opNorm A) * (2 * opNorm A) :=
          mul_le_mul hΛop hΛop (norm_nonneg _) (by linarith)
      _ ≤ 4 * hs := by nlinarith
  have hKb : opNorm Λ + K₂ ≤ K' * hs := by
    have := mul_le_mul_of_nonneg_left havg hCr.le
    rw [hK']
    nlinarith
  have hK0 : 0 ≤ opNorm Λ + K₂ := by
    have : 0 ≤ K₂ := (abs_nonneg _).trans (hΔb 0 ⟨le_rfl, zero_le_one⟩)
    have : 0 ≤ opNorm Λ := norm_nonneg _
    linarith
  -- the shift is integrable on `(0, 1]`
  have hΔm := Ev_shiftT_meas D N Λ hΛH hℓ k hk1 hkM εL hη
  have hfin : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc 0 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hΔi : IntegrableOn (shiftT Λ k εL) (Set.Ioc 0 1) := by
    have hcongr : (fun t => shiftT Λ k εL (Ev_cl t)) =ᵐ[(volume : Measure ℝ).restrict (Set.Ioc 0 1)]
        shiftT Λ k εL := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Ev_cl_of_mem (Set.Ioc_subset_Icc_self ht)]
    refine Integrable.of_bound (hΔm.aestronglyMeasurable.congr hcongr) K₂ ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hΔb t (Set.Ioc_subset_Icc_self ht)
  -- the integrand in `(w, t)`
  set γ : ℝ → ℝ := fun t => quant (rho ((t : ℂ) • Λ)) (D * N) k with hγ
  set S : Set ((Fin D → Coords N) × ℝ) := {p | η < |eigK (blockH D N p.1 +
    ((Ev_cl p.2 : ℝ) : ℂ) • Λ) k - γ (Ev_cl p.2)|} with hSdef
  have hSm : MeasurableSet S := by
    obtain ⟨hq, -⟩ := Ev_family Λ hΛH hℓ
    have h1 : Continuous fun p : (Fin D → Coords N) × ℝ =>
        eigK (blockH D N p.1 + ((Ev_cl p.2 : ℝ) : ℂ) • Λ) k :=
      Ev_eigK_cont _ (((Ev_blockH_cont D N).comp continuous_fst).add
        ((Complex.continuous_ofReal.comp (Ev_cl_cont.comp continuous_snd)).smul
          continuous_const))
        (fun p => (Ev_blockH_herm D N p.1).add (Ev_smul_herm hΛH _)) k
    have h2 : Continuous fun p : (Fin D → Coords N) × ℝ => γ (Ev_cl p.2) :=
      (hq (D * N) k hk1 hkM).comp continuous_snd
    exact measurableSet_lt measurable_const (h1.sub h2).abs.measurable
  set F : (Fin D → Coords N) × ℝ → ENNReal := fun p =>
    ENNReal.ofReal (4 * η ^ 2 * ((D * N : ℕ) : ℝ) * evalLoop D N A k εL (Ev_cl p.2) p.1) +
      ENNReal.ofReal ((opNorm Λ + K₂) ^ 2) * S.indicator 1 p with hFdef
  have hFm : Measurable F :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Ev_evalLoop_meas D N A hℓ k hk1 hkM εL hη))).add
      (measurable_const.mul (measurable_one.indicator hSm))
  -- the pathwise bound
  have hpath : ∀ w, ENNReal.ofReal ((eigK (blockH D N w + Λ) k - eigK (blockH D N w) k -
      shiftE Λ k εL) ^ 2) ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, F (w, t) := by
    intro w
    have h := Ev_path (blockH D N w) Λ (Ev_blockH_herm D N w) hΛH k hk1
      (by rw [Ev_card]; exact hkM) (shiftT Λ k εL) γ η K₂ hη hΔi
      (fun t ht => hΔb t (Set.Ioc_subset_Icc_self ht))
    rw [shiftE, intervalIntegral.integral_of_le zero_le_one]
    refine h.trans (le_of_eq (setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_))
    have hct := Ev_cl_of_mem (Set.Ioc_subset_Icc_self ht)
    simp only [hFdef, hSdef, hct, Ev_card, Set.indicator_apply, Set.mem_ofPred_eq]
    rfl
  -- the expectation of the time integral
  set B : ℝ := 4 * η ^ 2 * ((D * N : ℕ) : ℝ) * ((N : ℝ) ^ (δ / 4 + C₅ * εL) *
      ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hs ^ 2)) +
    (opNorm Λ + K₂) ^ 2 * (N : ℝ) ^ (-(3 : ℝ)) with hBdef
  have hEΦ : ∫⁻ w, (∫⁻ t in Set.Ioc (0 : ℝ) 1, F (w, t)) ∂(blockLaw D N L) ≤
      ENNReal.ofReal B := by
    rw [lintegral_lintegral_swap (μ := blockLaw D N L)
      (ν := (volume : Measure ℝ).restrict (Set.Ioc 0 1)) (f := fun w t => F (w, t))
      hFm.aemeasurable]
    calc ∫⁻ t in Set.Ioc (0 : ℝ) 1, ∫⁻ w, F (w, t) ∂(blockLaw D N L)
        ≤ ∫⁻ _t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal B :=
          setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
      _ = ENNReal.ofReal B := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
    have ht' := Set.Ioc_subset_Icc_self ht
    have hct := Ev_cl_of_mem ht'
    obtain ⟨hint, -, hle⟩ := hN₁ N hN1' L A hA k hk1 hk hhs t ht'
    have hm1 : Measurable fun w => ENNReal.ofReal (4 * η ^ 2 * ((D * N : ℕ) : ℝ) *
        evalLoop D N A k εL (Ev_cl t) w) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul
        (Ev_evalLoop_meas_t D N A hℓ k hk1 hkM εL hη t))
    have hSt : MeasurableSet ((fun w => (w, t)) ⁻¹' S) :=
      hSm.preimage (measurable_prodMk_right (y := t))
    have hsplit : ∫⁻ w, F (w, t) ∂(blockLaw D N L) =
        ENNReal.ofReal (4 * η ^ 2 * ((D * N : ℕ) : ℝ) *
          ∫ w, evalLoop D N A k εL t w ∂(blockLaw D N L)) +
        ENNReal.ofReal ((opNorm Λ + K₂) ^ 2) * blockLaw D N L ((fun w => (w, t)) ⁻¹' S) := by
      rw [hFdef]
      simp only []
      rw [lintegral_add_left hm1]
      simp_rw [show ∀ a, S.indicator (1 : (Fin D → Coords N) × ℝ → ENNReal) (a, t) =
        ((fun w => (w, t)) ⁻¹' S).indicator 1 a from fun a => rfl]
      rw [lintegral_const_mul _ (measurable_one.indicator hSt),
        lintegral_indicator_one hSt, hct, ← integral_const_mul,
        ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
          (ae_of_all _ fun w => mul_nonneg (by positivity) (Ev_evalLoop_nonneg D N A k εL t hη w))]
    have hrig : blockLaw D N L ((fun w => (w, t)) ⁻¹' S) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(3 : ℝ))) := by
      have hf : Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) :=
        (Ev_blockH_cont D N).measurable
      have hA' : opNorm ((t : ℂ) • A) ≤ (N : ℝ) ^ (-δA) := by
        rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]
        nlinarith [ht'.2]
      have hR := hN₄ N hN4' 1 zero_le_one le_rfl _ (llClass_blockH D N C L) ((t : ℂ) • A) hA'
      refine le_trans (measure_mono ?_) ((Measure.le_map_apply hf.aemeasurable _).trans hR)
      intro w hw
      simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq, hct] at hw
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Equiv.apply_symm_apply, ← lam_smul]
      refine ⟨k, hk1, hkM, lt_of_le_of_lt (le_of_eq ?_) hw⟩
      rw [hηdef, etaK, Real.rpow_add hN0]
      ring
    rw [hsplit, hBdef, ENNReal.ofReal_add (by positivity) (by positivity)]
    refine add_le_add (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hle (by positivity))) ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    gcongr
  -- the deterministic part, (A.35) [modification_shift_eigenvalue]
  have hr0 : 0 < rk D N k := by linarith
  have hdet : |shiftE Λ k εL - (quant (rho Λ) (D * N) k - quant rhoSc (D * N) k)| ≤
      (N : ℝ) ^ (-1 + ε) * hs / 2 := by
    refine (hN₃ N hN3' A hA k hk1 hkM hhs).2.1.trans ?_
    have hrm : rk D N k ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hk0 (by norm_num)
    have hP0 : 0 ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) := Real.rpow_nonneg hN0.le _
    have hP : (N : ℝ) ^ ((1 / 3 : ℝ) - εA) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h1 : hs ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
      hhs.trans ((mul_le_of_le_one_right hP0 hrm).trans hP)
    have h2 : rk D N k ^ (1 / 3 : ℝ) * hs ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) := by
      have e : rk D N k ^ (1 / 3 : ℝ) * rk D N k ^ (-(1 / 3 : ℝ)) = 1 := by
        rw [← Real.rpow_add hr0]; norm_num
      calc rk D N k ^ (1 / 3 : ℝ) * hs
          ≤ rk D N k ^ (1 / 3 : ℝ) * ((N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hhs (by positivity)
        _ = (N : ℝ) ^ ((1 / 3 : ℝ) - εA) := by
            rw [mul_comm ((N : ℝ) ^ _) _, ← mul_assoc, e, one_mul]
    have hN13 : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    have hT1 : hs ^ 4 / (N : ℝ) ^ 2 ≤ hs / N := by
      have h3 : hs ^ 3 ≤ N := (pow_le_pow_left₀ hs0 h1 3).trans hN13.le
      rw [div_le_div_iff₀ (by positivity) hN0]
      have : hs ^ 4 * N = hs * hs ^ 3 * N := by ring
      rw [this]
      have : hs * (N : ℝ) ^ 2 = hs * N * N := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hs0) hN0.le
    have hT2 : rk D N k ^ (1 / 3 : ℝ) * hs ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - εL / 2) ≤ hs / N := by
      have hE : (N : ℝ) ^ ((1 / 3 : ℝ) - εA) ≤ (N : ℝ) ^ ((4 / 3 : ℝ) - εL / 2) / N := by
        rw [← Real.rpow_sub_one hN0.ne']
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      rw [div_le_div_iff₀ (by positivity) hN0]
      calc rk D N k ^ (1 / 3 : ℝ) * hs ^ 2 * N = hs * (rk D N k ^ (1 / 3 : ℝ) * hs) * N := by ring
        _ ≤ hs * ((N : ℝ) ^ ((4 / 3 : ℝ) - εL / 2) / N) * N := by
            gcongr
            exact h2.trans hE
        _ = hs * (N : ℝ) ^ ((4 / 3 : ℝ) - εL / 2) := by field_simp
    have hNε : 4 * Cm / N ≤ (N : ℝ) ^ (-1 + ε) := by
      rw [Real.rpow_add hN0, Real.rpow_neg_one, div_eq_mul_inv, mul_comm ((N : ℝ)⁻¹)]
      exact mul_le_mul_of_nonneg_right h4C (by positivity)
    calc Cm * (hs ^ 4 / (N : ℝ) ^ 2 + rk D N k ^ (1 / 3 : ℝ) * hs ^ 2 /
          (N : ℝ) ^ ((4 / 3 : ℝ) - εL / 2))
        ≤ Cm * (hs / N + hs / N) := by gcongr
      _ = (4 * Cm / N) * hs / 2 := by ring
      _ ≤ (N : ℝ) ^ (-1 + ε) * hs / 2 := by gcongr
  -- `A = 0`: the event is empty
  by_cases hs_zero : hs = 0
  · have hA0 : A = 0 := Ev_hs_zero A hs_zero
    have hempty : {w | (N : ℝ) ^ (-1 + ε) * hs < |shiftX D N A k w|} = ∅ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hA0, Ev_shiftX_zero, abs_zero, hs_zero, mul_zero]
    rw [hempty, measure_empty]
    exact bot_le
  have hs_pos : 0 < hs := lt_of_le_of_ne hs0 (Ne.symm hs_zero)
  set a : ℝ := ((N : ℝ) ^ (-1 + ε) * hs / 2) ^ 2 with hadef
  have ha : 0 < a := by positivity
  have hsub : {w | (N : ℝ) ^ (-1 + ε) * hs < |shiftX D N A k w|} ⊆
      {w | ENNReal.ofReal a ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, F (w, t)} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hpath w)
    have hXY : shiftX D N A k w - (eigK (blockH D N w + Λ) k - eigK (blockH D N w) k -
        shiftE Λ k εL) = shiftE Λ k εL - (quant (rho Λ) (D * N) k - quant rhoSc (D * N) k) := by
      simp only [shiftX, HLam, hΛdef]
      ring
    have h3 := abs_sub_abs_le_abs_sub (shiftX D N A k w)
      (eigK (blockH D N w + Λ) k - eigK (blockH D N w) k - shiftE Λ k εL)
    rw [hXY] at h3
    have h4 : (N : ℝ) ^ (-1 + ε) * hs / 2 ≤
        |eigK (blockH D N w + Λ) k - eigK (blockH D N w) k - shiftE Λ k εL| := by linarith
    rw [hadef, ← sq_abs (eigK (blockH D N w + Λ) k - _ - _)]
    exact pow_le_pow_left₀ (by positivity) h4 2
  have hΦm : Measurable fun w => ∫⁻ t in Set.Ioc (0 : ℝ) 1, F (w, t) :=
    hFm.lintegral_prod_right'
  -- the exponents
  have hQ : η ^ 2 * rk D N k ^ (2 / 3 : ℝ) = ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL)) ^ 2 := by
    have e : (rk D N k ^ (-(1 / 3 : ℝ))) ^ 2 * rk D N k ^ (2 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]; norm_num
    rw [hηdef, etaK, mul_pow]
    calc ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL)) ^ 2 * (rk D N k ^ (-(1 / 3 : ℝ))) ^ 2 *
          rk D N k ^ (2 / 3 : ℝ)
        = ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL)) ^ 2 *
          ((rk D N k ^ (-(1 / 3 : ℝ))) ^ 2 * rk D N k ^ (2 / 3 : ℝ)) := by ring
      _ = _ := by rw [e, mul_one]
  set e1 : ℝ := 1 + ((-(2 / 3 : ℝ) + εL) + (-(2 / 3 : ℝ) + εL)) + (δ / 4 + C₅ * εL) +
    (-(5 / 3 : ℝ)) with he1
  set e2 : ℝ := -ε₀ + ((-1 + ε) + (-1 + ε)) with he2
  have hE1 : (N : ℝ) * ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL)) ^ 2 * (N : ℝ) ^ (δ / 4 + C₅ * εL) *
      (N : ℝ) ^ (-(5 / 3 : ℝ)) = (N : ℝ) ^ e1 := by
    rw [he1]
    simp only [Real.rpow_add hN0, Real.rpow_one]
    ring
  have hE2 : (N : ℝ) ^ (-ε₀) * ((N : ℝ) ^ (-1 + ε)) ^ 2 = (N : ℝ) ^ e2 := by
    rw [he2]
    simp only [Real.rpow_add hN0]
    ring
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have he12 : (N : ℝ) ^ e1 * (32 * D) ≤ (N : ℝ) ^ e2 := by
    have hd : δ / 2 ≤ e2 - e1 := by rw [he1, he2, hδdef] at *; nlinarith
    calc (N : ℝ) ^ e1 * (32 * D) ≤ (N : ℝ) ^ e1 * (N : ℝ) ^ (e2 - e1) :=
          mul_le_mul_of_nonneg_left (h32.trans (Real.rpow_le_rpow_of_exponent_le hN1r hd))
            (by positivity)
      _ = (N : ℝ) ^ e2 := by rw [← Real.rpow_add hN0]; ring_nf
  have he2' : (N : ℝ) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ e2 :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by rw [he2]; linarith)
  have hBa : B / a ≤ (N : ℝ) ^ (-ε₀) := by
    rw [div_le_iff₀ ha]
    have hp1 : 4 * η ^ 2 * ((D * N : ℕ) : ℝ) * ((N : ℝ) ^ (δ / 4 + C₅ * εL) *
        ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hs ^ 2)) =
        4 * D * hs ^ 2 * ((N : ℝ) * ((N : ℝ) ^ (-(2 / 3 : ℝ) + εL)) ^ 2 *
          (N : ℝ) ^ (δ / 4 + C₅ * εL) * (N : ℝ) ^ (-(5 / 3 : ℝ))) := by
      rw [← hQ]
      push_cast
      ring
    have hp2 : (N : ℝ) ^ (-ε₀) * a = hs ^ 2 / 4 * ((N : ℝ) ^ (-ε₀) * ((N : ℝ) ^ (-1 + ε)) ^ 2) := by
      rw [hadef]
      ring
    have hN3 : (N : ℝ) ^ (-(3 : ℝ)) = (N : ℝ)⁻¹ * (N : ℝ) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; norm_num
    have hK2 : (opNorm Λ + K₂) ^ 2 ≤ K' ^ 2 * hs ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hK0 hKb 2
    have hNinv : 8 * K' ^ 2 * (N : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]; linarith
    rw [hBdef, hp1, hE1, hp2, hE2, hN3]
    have hpos2 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ)) := by positivity
    have hpos1 : 0 ≤ (N : ℝ) ^ e1 := by positivity
    calc 4 * D * hs ^ 2 * (N : ℝ) ^ e1 + (opNorm Λ + K₂) ^ 2 * ((N : ℝ)⁻¹ * (N : ℝ) ^ (-(2 : ℝ)))
        ≤ hs ^ 2 / 8 * ((N : ℝ) ^ e1 * (32 * D)) +
          hs ^ 2 / 8 * ((8 * K' ^ 2 * (N : ℝ)⁻¹) * (N : ℝ) ^ (-(2 : ℝ))) := by
          have : (opNorm Λ + K₂) ^ 2 * ((N : ℝ)⁻¹ * (N : ℝ) ^ (-(2 : ℝ))) ≤
              K' ^ 2 * hs ^ 2 * ((N : ℝ)⁻¹ * (N : ℝ) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_right hK2 (by positivity)
          nlinarith
      _ ≤ hs ^ 2 / 8 * (N : ℝ) ^ e2 + hs ^ 2 / 8 * (1 * (N : ℝ) ^ e2) := by
          gcongr
      _ = hs ^ 2 / 4 * (N : ℝ) ^ e2 := by ring
  calc blockLaw D N L {w | (N : ℝ) ^ (-1 + ε) * hs < |shiftX D N A k w|}
      ≤ blockLaw D N L {w | ENNReal.ofReal a ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, F (w, t)} :=
        measure_mono hsub
    _ ≤ (∫⁻ w, (∫⁻ t in Set.Ioc (0 : ℝ) 1, F (w, t)) ∂(blockLaw D N L)) / ENNReal.ofReal a :=
        meas_ge_le_lintegral_div hΦm.aemeasurable (ENNReal.ofReal_pos.2 ha).ne'
          ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal a := by gcongr
    _ = ENNReal.ofReal (B / a) := (ENNReal.ofReal_div_of_pos ha).symm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-ε₀)) := ENNReal.ofReal_le_ofReal hBa

/-- (2.11) [eq:main_perurb] of Theorem 2.5 [theorem_localized_eigenvalue] for `2k ≤ DN + 1`:
(2.10) [eq:local_eigenvalue_perturb] at `ε = ε₀ = ε_A/2` with (2.8) [eq:condA2], `c = ε_A/4`. -/
private lemma Ev_211 (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (C : ℕ → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | (N : ℝ) ^ (-(2 / 3 : ℝ) - c) * rk D N k ^ (-(1 / 3 : ℝ)) ≤
          |shiftX D N A k w|} ≤ ENNReal.ofReal ((N : ℝ) ^ (-c)) := by
  obtain ⟨N₀, hN₀⟩ := Ev_210 D hD δA εA hδA hεA C (εA / 2) (εA / 2) (by positivity)
    (by positivity) (by linarith)
  refine ⟨εA / 4, by positivity, max N₀ 2, fun N hN L A hA k hk1 hk hhs => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hr0 : 0 < rk D N k := by rw [Ev_rk_half D N k hk]; exact_mod_cast hk1
  refine le_trans (measure_mono fun w hw => ?_)
    ((hN₀ N (le_of_max_le_left hN) L A hA k hk1 hk hhs).trans
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))))
  simp only [Set.mem_ofPred_eq] at hw ⊢
  refine lt_of_lt_of_le ?_ hw
  calc (N : ℝ) ^ (-1 + εA / 2) * hsNorm A
      ≤ (N : ℝ) ^ (-1 + εA / 2) * ((N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hhs (by positivity)
    _ = (N : ℝ) ^ (-(2 / 3 : ℝ) - εA / 2) * rk D N k ^ (-(1 / 3 : ℝ)) := by
        rw [← mul_assoc, ← Real.rpow_add hN0]
        congr 2
        ring
    _ < (N : ℝ) ^ (-(2 / 3 : ℝ) - εA / 4) * rk D N k ^ (-(1 / 3 : ℝ)) :=
        mul_lt_mul_of_pos_right (Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith))
          (by positivity)

/-! ### The reflection `h ↦ -h`, `A ↦ -A` -/

/-- `wig n (-w) = -wig n w`. -/
private lemma Ev_wig_neg (n : ℕ) (w : Coords n) : wig n (-w) = -wig n w := by
  ext i j
  simp only [wig, Matrix.neg_apply]
  by_cases h : i = j
  · simp [h]
  · by_cases h' : i < j <;> simp [h, h']

/-- `H(-w) = -H(w)`. -/
private lemma Ev_blockH_neg (D N : ℕ) (w : Fin D → Coords N) :
    blockH D N (-w) = -blockH D N w := by
  ext p q
  simp only [blockH, Matrix.neg_apply, Pi.neg_apply]
  split_ifs <;> simp [Ev_wig_neg]

/-- `Λ(-A) = -Λ(A)`. -/
private lemma Ev_lam_neg (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N (-A) = -lam D N A := by
  ext p q
  simp only [lam, Matrix.neg_apply, star_neg]
  split_ifs <;> simp [add_comm]

/-- `‖-A‖ = ‖A‖`. -/
private lemma Ev_opNorm_neg {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    opNorm (-A) = opNorm A := by
  rw [opNorm, opNorm, map_neg, norm_neg]

/-- `‖-A‖_HS = ‖A‖_HS`. -/
private lemma Ev_hsNorm_neg {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    hsNorm (-A) = hsNorm A := by
  simp [hsNorm]

/-- `𝔯(DN + 1 - k) = 𝔯(k)` for `k ≤ DN + 1`. -/
private lemma Ev_rk_refl (D N k : ℕ) (hk : k ≤ D * N + 1) :
    rk D N (D * N + 1 - k) = rk D N k := by
  unfold rk
  have : D * N + 1 - (D * N + 1 - k) = k := by omega
  rw [this, min_comm]

/-- The shift `X` of Theorem 2.5 [theorem_localized_eigenvalue] changes sign under the
reflection `(A, k, w) ↦ (-A, DN + 1 - k, -w)`. -/
private lemma Ev_shiftX_neg (D N : ℕ) [Nonempty (Idx D N)] (A : Matrix (Fin N) (Fin N) ℂ)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ D * N) (hΛ : opNorm (lam D N A) ≤ 1 / 10)
    (w : Fin D → Coords N) :
    shiftX D N (-A) (D * N + 1 - k) (-w) = -shiftX D N A k w := by
  have hneg : ∀ X : Matrix (Idx D N) (Idx D N) ℂ, X.IsHermitian →
      eigK (-X) (D * N + 1 - k) = -eigK X k := by
    intro X hX
    have := eigK_neg X hX (D * N + 1 - k) (by omega) (by rw [Ev_card]; omega)
    rw [this, Ev_card]
    congr 2
    omega
  unfold shiftX
  rw [HLam, Ev_blockH_neg, Ev_lam_neg, ← neg_add, ← HLam, hneg _ (HLam_isHermitian D N A w),
    hneg _ (Ev_blockH_herm D N w),
    Reflect_quant_neg (lam_isHermitian D N A) hΛ (D * N) k hk1 hk,
    Reflect_quant_sc (D * N) k hk1 hk]
  ring

/-- (2.11) [eq:main_perurb] for every `k ∈ ⟦1, DN⟧`: the indices `2k > DN + 1` by the
reflection. -/
private lemma Ev_211_full (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (C : ℕ → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ i : ℕ, 1 ≤ i → i ≤ D * N →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N i ^ (-(1 / 3 : ℝ)) →
      blockLaw D N L {w | (N : ℝ) ^ (-(2 / 3 : ℝ) - c) * rk D N i ^ (-(1 / 3 : ℝ)) ≤
          |shiftX D N A i w|} ≤ ENNReal.ofReal ((N : ℝ) ^ (-c)) := by
  obtain ⟨c, hc, N₁, hN₁⟩ := Ev_211 D hD δA εA hδA hεA C
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((Ev_ev δA 20 hδA).and (Ev_ev 1 1 one_pos))
  refine ⟨c, hc, max N₁ N₂, fun N hN L A hA i hi1 hi hhs => ?_⟩
  obtain ⟨h20, h1⟩ := hN₂ N (le_of_max_le_right hN)
  rw [Real.rpow_one] at h1
  have hN0 : (0 : ℝ) < N := by linarith
  by_cases hi2 : 2 * i ≤ D * N + 1
  · exact hN₁ N (le_of_max_le_left hN) L A hA i hi1 hi2 hhs
  have hNnat : 1 ≤ N := by exact_mod_cast h1
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hδN : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
    rw [Real.rpow_neg hN0.le]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  have hΛ : opNorm (lam D N A) ≤ 1 / 10 :=
    (opNorm_lam_le D N A).trans (by linarith [hA.trans hδN])
  have h := hN₁ N (le_of_max_le_left hN) (Reflect_negLaws L) (-A) (by rwa [Ev_opNorm_neg])
    (D * N + 1 - i) (by omega) (by omega)
    (by rwa [Ev_hsNorm_neg, Ev_rk_refl D N i (by omega)])
  rw [Ev_rk_refl D N i (by omega)] at h
  have hset : {w | (N : ℝ) ^ (-(2 / 3 : ℝ) - c) * rk D N i ^ (-(1 / 3 : ℝ)) ≤
      |shiftX D N A i w|} = (fun w : Fin D → Coords N => -w) ⁻¹'
      {w | (N : ℝ) ^ (-(2 / 3 : ℝ) - c) * rk D N i ^ (-(1 / 3 : ℝ)) ≤
        |shiftX D N (-A) (D * N + 1 - i) w|} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Ev_shiftX_neg D N A i hi1 hi hΛ, abs_neg]
  rw [hset, ← Reflect_blockLaw_neg] at *
  exact (Measure.le_map_apply measurable_neg.aemeasurable _).trans h

/-! ### The correlation functions -/

/-- On the window `|i - k| ≤ T` (`T ≥ 1`, `2k ≤ DN + 1`), `(k + T)/(4T) ≤ 𝔯(i) ≤ 2Tk` for
`𝔯` of (1.4) [eq:rk]. -/
private lemma Ev_rk_win (D N k i : ℕ) (T : ℝ) (hT : 1 ≤ T) (hk1 : 1 ≤ k)
    (hk : 2 * k ≤ D * N + 1) (hi1 : 1 ≤ i) (hi : i ≤ D * N) (hik : |(i : ℝ) - k| ≤ T) :
    (k + T) / (4 * T) ≤ rk D N i ∧ rk D N i ≤ 2 * T * k := by
  have hcast : rk D N i = min (i : ℝ) ((D * N : ℕ) + 1 - i) := by
    unfold rk
    rw [Nat.cast_min, Nat.cast_sub (by omega)]
    push_cast
    ring_nf
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hir : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have hiM : (i : ℝ) ≤ ((D * N : ℕ) : ℝ) := by exact_mod_cast hi
  have hkM : 2 * (k : ℝ) ≤ ((D * N : ℕ) : ℝ) + 1 := by exact_mod_cast hk
  rw [abs_le] at hik
  rw [hcast]
  have hT0 : 0 < 4 * T := by linarith
  constructor
  · refine le_min ?_ ?_
    · rw [div_le_iff₀ hT0]
      by_cases h3 : (k : ℝ) ≤ 3 * T
      · nlinarith
      · push Not at h3; nlinarith
    · rw [div_le_iff₀ hT0]
      by_cases h3 : (k : ℝ) ≤ 3 * T
      · nlinarith
      · push Not at h3; nlinarith
  · refine (min_le_left _ _).trans ?_
    nlinarith

/-- The index window: under rigidity at every index and the spacing of the quantiles near `k`,
an eigenvalue whose index is farther than `T` from `k` lies at distance more than `r` from
`γ_k`, when the gap `(T/2) g` exceeds `r` plus the rigidity error on the window. -/
private lemma Ev_window (M k : ℕ) (hk1 : 1 ≤ k) (hkM : k ≤ M) (T : ℝ) (hT : 1 ≤ T)
    (ev γ e : ℕ → ℝ) (hev : ∀ i j, 1 ≤ i → i ≤ j → j ≤ M → ev j ≤ ev i)
    (hγ : ∀ i j, 1 ≤ i → i ≤ j → j ≤ M → γ j ≤ γ i)
    (hrig : ∀ i, 1 ≤ i → i ≤ M → |ev i - γ i| ≤ e i) (g : ℝ) (hg : 0 ≤ g)
    (hsp : ∀ i, 1 ≤ i → i ≤ M → |(i : ℝ) - k| ≤ T → |(i : ℝ) - k| * g ≤ |γ i - γ k|)
    (r : ℝ) (hgap : ∀ i, 1 ≤ i → i ≤ M → |(i : ℝ) - k| ≤ T → r + e i < T / 2 * g)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ M) (hik : T < |(i : ℝ) - k|) : r < |ev i - γ k| := by
  set m := ⌊T⌋₊ with hm
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hT)
  have hmT : (m : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hTm : T < m + 1 := Nat.lt_floor_add_one T
  have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hTm2 : T / 2 * g ≤ m * g := mul_le_mul_of_nonneg_right (by linarith) hg
  rcases lt_abs.1 hik with h | h
  · -- `i > k + T`
    have hlt : k + m < i := by
      have : ((k + m : ℕ) : ℝ) < i := by push_cast; linarith
      exact_mod_cast this
    have hi' : |((k + m : ℕ) : ℝ) - k| ≤ T := by
      push_cast
      rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
      exact hmT
    have h1 := hev (k + m) i (by omega) hlt.le hi
    have h2 := (abs_le.1 (hrig (k + m) (by omega) (by omega))).2
    have h3 := hγ k (k + m) hk1 (by omega) (by omega)
    have h4 := hsp (k + m) (by omega) (by omega) hi'
    have h5 := hgap (k + m) (by omega) (by omega) hi'
    have e1 : |((k + m : ℕ) : ℝ) - k| = m := by
      push_cast
      rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
    rw [e1, abs_sub_comm, abs_of_nonneg (by linarith)] at h4
    rw [abs_sub_comm, lt_abs]
    left
    linarith
  · -- `i < k - T`
    have hlt : i + m < k := by
      have : ((i + m : ℕ) : ℝ) < k := by push_cast; linarith
      exact_mod_cast this
    have hi' : |((k - m : ℕ) : ℝ) - k| ≤ T := by
      rw [Nat.cast_sub (by omega), sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
      exact hmT
    have h1 := hev i (k - m) hi1 (by omega) (by omega)
    have h2 := (abs_le.1 (hrig (k - m) (by omega) (by omega))).1
    have h3 := hγ (k - m) k (by omega) (by omega) hkM
    have h4 := hsp (k - m) (by omega) (by omega) hi'
    have h5 := hgap (k - m) (by omega) (by omega) hi'
    have e1 : |((k - m : ℕ) : ℝ) - k| = m := by
      rw [Nat.cast_sub (by omega), sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
    rw [e1, abs_of_nonneg (by linarith)] at h4
    rw [lt_abs]
    left
    linarith

/-- The difference of two pairings of Theorem 2.5 [theorem_localized_eigenvalue]: the terms with an
index outside the window `W` vanish when both configurations are outside the support of `O`
there (`rig`); a term inside the window is at most `L_O δ` when its points are `δ`-close
(`rig` and not `bad`), and at most `2 sup |O|` otherwise. -/
private lemma Ev_pair_bound (M n : ℕ) (s γ γ' : ℝ) (O : (Fin n → ℝ) → ℝ) (R MO LO δ : ℝ)
    (hR : ∀ x, O x ≠ 0 → ∀ j, |x j| ≤ R) (hM : ∀ x, |O x| ≤ MO)
    (hL : ∀ x y, |O x - O y| ≤ LO * ‖x - y‖) (hLO : 0 ≤ LO) (hδ : 0 ≤ δ) (ev ev' : ℕ → ℝ)
    (W : Finset (Fin M)) (bad rig : Prop) [Decidable bad] [Decidable rig]
    (hout : rig → ∀ a : Fin M, a ∉ W →
      R < |s * (ev ((a : ℕ) + 1) - γ)| ∧ R < |s * (ev' ((a : ℕ) + 1) - γ')|)
    (hclose : rig → ¬ bad → ∀ a ∈ W,
      |s * (ev ((a : ℕ) + 1) - γ) - s * (ev' ((a : ℕ) + 1) - γ')| ≤ δ) :
    |corrPairing M n s γ O ev - corrPairing M n s γ' O ev'| ≤
      ((Finset.univ.filter fun F : Fin n ↪ Fin M => ∀ j, F j ∈ W).card : ℝ) *
          (LO * δ + 2 * MO * (if bad then 1 else 0)) +
        (Fintype.card (Fin n ↪ Fin M) : ℝ) * (2 * MO) * (if rig then 0 else 1) := by
  have hM0 : 0 ≤ MO := (abs_nonneg _).trans (hM 0)
  have h2M : ∀ x y, |O x - O y| ≤ 2 * MO := fun x y =>
    (abs_sub _ _).trans (by linarith [hM x, hM y])
  unfold corrPairing
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  by_cases hr : rig
  · simp only [hr, ite_true, mul_zero, add_zero]
    calc ∑ F : Fin n ↪ Fin M, |O (fun j => s * (ev ((F j : ℕ) + 1) - γ)) -
          O (fun j => s * (ev' ((F j : ℕ) + 1) - γ'))|
        ≤ ∑ F : Fin n ↪ Fin M, if (∀ j, F j ∈ W) then
          (LO * δ + 2 * MO * (if bad then 1 else 0)) else 0 := by
          refine Finset.sum_le_sum fun F _ => ?_
          split_ifs with hF hb
          · linarith [h2M (fun j => s * (ev ((F j : ℕ) + 1) - γ))
              (fun j => s * (ev' ((F j : ℕ) + 1) - γ')), mul_nonneg hLO hδ]
          · refine (hL _ _).trans ?_
            rw [mul_zero, add_zero]
            refine mul_le_mul_of_nonneg_left ?_ hLO
            refine (pi_norm_le_iff_of_nonneg hδ).2 fun j => ?_
            rw [Pi.sub_apply, Real.norm_eq_abs]
            exact hclose hr hb (F j) (hF j)
          · push Not at hF
            obtain ⟨j, hj⟩ := hF
            obtain ⟨h1, h2⟩ := hout hr (F j) hj
            have hx : O (fun j => s * (ev ((F j : ℕ) + 1) - γ)) = 0 := by
              by_contra h
              have := hR _ h j
              linarith
            have hy : O (fun j => s * (ev' ((F j : ℕ) + 1) - γ')) = 0 := by
              by_contra h
              have := hR _ h j
              linarith
            rw [hx, hy, sub_zero, abs_zero]
      _ = _ := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  · simp only [hr, ite_false, mul_one]
    calc ∑ F : Fin n ↪ Fin M, |O (fun j => s * (ev ((F j : ℕ) + 1) - γ)) -
          O (fun j => s * (ev' ((F j : ℕ) + 1) - γ'))|
        ≤ ∑ _F : Fin n ↪ Fin M, 2 * MO := Finset.sum_le_sum fun F _ => h2M _ _
      _ = (Fintype.card (Fin n ↪ Fin M) : ℝ) * (2 * MO) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (by positivity)
          (add_nonneg (mul_nonneg hLO hδ) (by split_ifs <;> positivity)))

/-- `(x^{1/3})³ = x` for `x ≥ 0`. -/
private lemma Ev_cbrt {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `a ≤ b` from `a³ ≤ b³` and `b ≥ 0`. -/
private lemma Ev_le_of_cube {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 3 ≤ b ^ 3) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  have := pow_lt_pow_left₀ hlt hb (by norm_num : (3 : ℕ) ≠ 0)
  linarith

/-- `x^{-1/3} = (x^{1/3})⁻¹` for `x ≥ 0`. -/
private lemma Ev_rpow_m13 {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 / 3 : ℝ)) = (x ^ (1 / 3 : ℝ))⁻¹ :=
  Real.rpow_neg hx _

/-- The gap inequality of the index window: with `T = v⁶`, `s = M^{2/3} k^{1/3}` (`M ≥ N`),
`𝔯 ≥ (k + T)/(4T)` and `8 < c v`, `R/s + v³ N^{-2/3} 𝔯^{-1/3} < (T/2) c N^{-2/3} (k + T)^{-1/3}`
(the case `R ≤ v³`). -/
private lemma Ev_gap (Nr Mr kr ri R v cs : ℝ) (hN : 0 < Nr) (hMN : Nr ≤ Mr) (hk : 1 ≤ kr)
    (hv : 1 ≤ v) (hR0 : 0 ≤ R) (hR : R ≤ v ^ 3) (hvc : 8 < cs * v)
    (hri : (kr + v ^ 6) / (4 * v ^ 6) ≤ ri) :
    R / (Mr ^ (2 / 3 : ℝ) * kr ^ (1 / 3 : ℝ)) +
        v ^ 3 * (Nr ^ (-(2 / 3 : ℝ)) * ri ^ (-(1 / 3 : ℝ))) <
      v ^ 6 / 2 * (cs * (Nr ^ (-(2 / 3 : ℝ)) * (kr + v ^ 6) ^ (-(1 / 3 : ℝ)))) := by
  have hv6 : 1 ≤ v ^ 6 := one_le_pow₀ hv
  have hv0 : 0 < v := by linarith
  have hri0 : 0 < ri := lt_of_lt_of_le (by positivity) hri
  have hM0 : 0 < Mr := by linarith
  have hkT : 0 < kr + v ^ 6 := by linarith
  set ν := Nr ^ (-(2 / 3 : ℝ)) with hν
  have hν0 : 0 < ν := Real.rpow_pos_of_pos hN _
  set P := (kr + v ^ 6) ^ (1 / 3 : ℝ) with hP
  set a := ri ^ (1 / 3 : ℝ) with ha
  set b := kr ^ (1 / 3 : ℝ) with hb
  have hP0 : 0 < P := Real.rpow_pos_of_pos hkT _
  have ha0 : 0 < a := Real.rpow_pos_of_pos hri0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos (by linarith) _
  rw [Ev_rpow_m13 hri0.le, Ev_rpow_m13 hkT.le]
  have hPb : P ≤ 2 * v ^ 2 * b := by
    refine Ev_le_of_cube (by positivity) ?_
    rw [hP, Ev_cbrt hkT.le, mul_pow, hb, Ev_cbrt (by linarith)]
    nlinarith
  have hPa : P ≤ 2 * v ^ 2 * a := by
    refine Ev_le_of_cube (by positivity) ?_
    rw [hP, Ev_cbrt hkT.le, mul_pow, ha, Ev_cbrt hri0.le]
    rw [div_le_iff₀ (by positivity)] at hri
    nlinarith
  have hνM : 1 ≤ ν * Mr ^ (2 / 3 : ℝ) := by
    rw [hν, Real.rpow_neg hN.le, ← div_eq_inv_mul, le_div_iff₀ (Real.rpow_pos_of_pos hN _),
      one_mul]
    exact Real.rpow_le_rpow hN.le hMN (by norm_num)
  have h1 : R / (Mr ^ (2 / 3 : ℝ) * b) ≤ 2 * v ^ 2 * R * ν / P := by
    rw [div_le_iff₀ (by positivity)]
    have hy : 1 ≤ 2 * v ^ 2 * b / P := by rw [le_div_iff₀ hP0, one_mul]; exact hPb
    calc R = R * 1 * 1 := by ring
      _ ≤ R * (ν * Mr ^ (2 / 3 : ℝ)) * (2 * v ^ 2 * b / P) := by gcongr
      _ = 2 * v ^ 2 * R * ν / P * (Mr ^ (2 / 3 : ℝ) * b) := by ring
  have h2 : v ^ 3 * (ν * a⁻¹) ≤ 2 * v ^ 5 * ν / P := by
    have : a⁻¹ ≤ 2 * v ^ 2 / P := by
      rw [inv_le_comm₀ ha0 (by positivity), inv_div, div_le_iff₀ (by positivity)]
      linarith
    calc v ^ 3 * (ν * a⁻¹) ≤ v ^ 3 * (ν * (2 * v ^ 2 / P)) := by gcongr
      _ = 2 * v ^ 5 * ν / P := by ring
  have h3 : 2 * v ^ 2 * R * ν / P + 2 * v ^ 5 * ν / P < v ^ 6 / 2 * (cs * (ν * P⁻¹)) := by
    have e1 : 2 * v ^ 2 * R * ν / P + 2 * v ^ 5 * ν / P =
        (2 * v ^ 2 * R + 2 * v ^ 5) * (ν / P) := by
      ring
    have e2 : v ^ 6 / 2 * (cs * (ν * P⁻¹)) = (v ^ 5 * (cs * v) / 2) * (ν / P) := by ring
    rw [e1, e2]
    refine mul_lt_mul_of_pos_right ?_ (by positivity)
    have hv5 : 0 < v ^ 5 := by positivity
    have : 2 * v ^ 2 * R ≤ 2 * v ^ 5 := by
      have := mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ 2 * v ^ 2)
      linarith [show 2 * v ^ 2 * v ^ 3 = 2 * v ^ 5 by ring]
    nlinarith
  linarith

/-- The correlation step for one index: with `s = (DN)^{2/3} k^{1/3}`, `𝔯 ≥ k/(4v⁶)`,
`|X| < N^{-2/3-c'} 𝔯^{-1/3}` and `|Q| ≤ e k^{-1}/s`, `|s(X + Q)| ≤ 2 D v² N^{-c'} + e`. -/
private lemma Ev_close (Dr Nr Mr kr ri v c' X Q e : ℝ) (hD : 1 ≤ Dr) (hN : 0 < Nr)
    (hMr : Mr = Dr * Nr) (hk : 1 ≤ kr) (hv : 1 ≤ v) (hri : kr / (4 * v ^ 6) ≤ ri)
    (hX : |X| < Nr ^ (-(2 / 3 : ℝ) - c') * ri ^ (-(1 / 3 : ℝ)))
    (hQ : |Q| ≤ e * kr ^ (-(1 : ℝ)) / (Mr ^ (2 / 3 : ℝ) * kr ^ (1 / 3 : ℝ))) (he : 0 ≤ e) :
    |Mr ^ (2 / 3 : ℝ) * kr ^ (1 / 3 : ℝ) * (X + Q)| ≤ 2 * Dr * v ^ 2 * Nr ^ (-c') + e := by
  have hv0 : 0 < v := by linarith
  have hri0 : 0 < ri := lt_of_lt_of_le (by positivity) hri
  have hk0 : 0 < kr := by linarith
  set s := Mr ^ (2 / 3 : ℝ) * kr ^ (1 / 3 : ℝ) with hs
  have hM0 : 0 < Mr := by rw [hMr]; nlinarith
  have hs0 : 0 < s := by positivity
  rw [abs_mul, abs_of_pos hs0]
  refine (mul_le_mul_of_nonneg_left (abs_add_le X Q) hs0.le).trans ?_
  rw [mul_add]
  have hQ' : s * |Q| ≤ e := by
    have h1 : s * |Q| ≤ e * kr ^ (-(1 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hQ hs0.le
      rwa [mul_div_cancel₀ _ hs0.ne'] at this
    have h2 : kr ^ (-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk (by norm_num)
    nlinarith
  have hX' : s * |X| ≤ 2 * Dr * v ^ 2 * Nr ^ (-c') := by
    set a := ri ^ (1 / 3 : ℝ) with ha
    set b := kr ^ (1 / 3 : ℝ) with hb
    have ha0 : 0 < a := Real.rpow_pos_of_pos hri0 _
    have hb0 : 0 < b := Real.rpow_pos_of_pos hk0 _
    have hba : b ≤ 2 * v ^ 2 * a := by
      refine Ev_le_of_cube (by positivity) ?_
      rw [hb, Ev_cbrt hk0.le, mul_pow, ha, Ev_cbrt hri0.le]
      rw [div_le_iff₀ (by positivity)] at hri
      nlinarith [one_le_pow₀ (n := 6) hv]
    have hMs : Mr ^ (2 / 3 : ℝ) = Dr ^ (2 / 3 : ℝ) * Nr ^ (2 / 3 : ℝ) := by
      rw [hMr, Real.mul_rpow (by linarith) hN.le]
    have hNe : Nr ^ (-(2 / 3 : ℝ) - c') = (Nr ^ (2 / 3 : ℝ))⁻¹ * Nr ^ (-c') := by
      rw [sub_eq_add_neg, Real.rpow_add hN, Real.rpow_neg hN.le]
    have hD23 : Dr ^ (2 / 3 : ℝ) ≤ Dr := by
      have := Real.rpow_le_rpow_of_exponent_le hD (show (2 / 3 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have hN23 : 0 < Nr ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hN _
    have hc0 : 0 < Nr ^ (-c') := Real.rpow_pos_of_pos hN _
    have hD0 : 0 ≤ Dr ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
    calc s * |X| ≤ s * (Nr ^ (-(2 / 3 : ℝ) - c') * ri ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hX.le hs0.le
      _ = Dr ^ (2 / 3 : ℝ) * Nr ^ (-c') * (b * a⁻¹) := by
          rw [hs, hMs, hNe, Ev_rpow_m13 hri0.le, ← ha]
          field_simp
      _ ≤ Dr * Nr ^ (-c') * (2 * v ^ 2) := by
          have hbi : b * a⁻¹ ≤ 2 * v ^ 2 := by
            rw [mul_inv_le_iff₀ ha0]
            exact hba
          exact mul_le_mul (mul_le_mul_of_nonneg_right hD23 hc0.le) hbi (by positivity)
            (by positivity)
      _ = 2 * Dr * v ^ 2 * Nr ^ (-c') := by ring
  linarith

/-- `hs ≤ N^{1/3-ε_A} k^{-1/3}` gives `hs ≤ N^{1/3-ε_A/2} 𝔯^{-1/3}` when `𝔯 ≤ 2v⁶k` and
`2v² ≤ N^{ε_A/2}`: (2.8) [eq:condA2] at the indices of the window, with `ε_A/2`. -/
private lemma Ev_hs_win (Nr kr ri v εA hs : ℝ) (hN : 0 < Nr) (hk : 0 < kr) (hri0 : 0 < ri)
    (hv : 1 ≤ v) (hri : ri ≤ 2 * v ^ 6 * kr) (hvN : 2 * v ^ 2 ≤ Nr ^ (εA / 2))
    (hhs : hs ≤ Nr ^ ((1 / 3 : ℝ) - εA) * kr ^ (-(1 / 3 : ℝ))) :
    hs ≤ Nr ^ ((1 / 3 : ℝ) - εA / 2) * ri ^ (-(1 / 3 : ℝ)) := by
  have hv0 : 0 < v := by linarith
  set a := ri ^ (1 / 3 : ℝ) with ha
  set b := kr ^ (1 / 3 : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hri0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hk _
  have hab : a ≤ 2 * v ^ 2 * b := by
    refine Ev_le_of_cube (by positivity) ?_
    rw [ha, Ev_cbrt hri0.le, mul_pow, hb, Ev_cbrt hk.le]
    nlinarith [one_le_pow₀ (n := 6) hv]
  have hbinv : b⁻¹ ≤ 2 * v ^ 2 * a⁻¹ := by
    rw [inv_le_comm₀ hb0 (by positivity), mul_inv, inv_inv, ← div_eq_inv_mul,
      div_le_iff₀ (by positivity)]
    calc a ≤ 2 * v ^ 2 * b := hab
      _ = b * (2 * v ^ 2) := by ring
  have hsplit : Nr ^ ((1 / 3 : ℝ) - εA / 2) = Nr ^ ((1 / 3 : ℝ) - εA) * Nr ^ (εA / 2) := by
    rw [← Real.rpow_add hN]; ring_nf
  rw [Ev_rpow_m13 hk.le, ← hb] at hhs
  rw [Ev_rpow_m13 hri0.le, ← ha, hsplit]
  have hP : 0 ≤ Nr ^ ((1 / 3 : ℝ) - εA) := Real.rpow_nonneg hN.le _
  calc hs ≤ Nr ^ ((1 / 3 : ℝ) - εA) * b⁻¹ := hhs
    _ ≤ Nr ^ ((1 / 3 : ℝ) - εA) * (2 * v ^ 2 * a⁻¹) := by gcongr
    _ ≤ Nr ^ ((1 / 3 : ℝ) - εA) * (Nr ^ (εA / 2) * a⁻¹) := by gcongr
    _ = _ := by ring

/-- The window `{a : |a + 1 - k| ≤ T}` of `⟦1, M⟧` has at most `3T` points, `T ≥ 1`. -/
private lemma Ev_win_card (M k : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    ((Finset.univ.filter fun a : Fin M => |((a : ℕ) + 1 : ℝ) - k| ≤ T).card : ℝ) ≤ 3 * T := by
  set m := ⌊T⌋₊ with hm
  have hmT : (m : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hcard : (Finset.univ.filter fun a : Fin M => |((a : ℕ) + 1 : ℝ) - k| ≤ T).card ≤
      2 * m + 1 := by
    calc _ ≤ (Finset.Icc (k - m) (k + m)).card := by
          refine Finset.card_le_card_of_injOn (fun a : Fin M => (a : ℕ) + 1) ?_ ?_
          · intro a ha
            rw [Finset.mem_coe, Finset.mem_filter] at ha
            rw [Finset.mem_coe, Finset.mem_Icc]
            obtain ⟨h1, h2⟩ := abs_le.1 ha.2
            have hu : (a : ℕ) + 1 - k ≤ m := by
              refine Nat.le_floor ?_
              rcases le_or_gt k ((a : ℕ) + 1) with h | h
              · rw [Nat.cast_sub h]; push_cast; linarith
              · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; linarith
            have hl : k - ((a : ℕ) + 1) ≤ m := by
              refine Nat.le_floor ?_
              rcases le_or_gt ((a : ℕ) + 1) k with h | h
              · rw [Nat.cast_sub h]; push_cast; linarith
              · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; linarith
            change k - m ≤ (a : ℕ) + 1 ∧ (a : ℕ) + 1 ≤ k + m
            constructor <;> omega
          · intro a _ b _ h
            simp only at h
            exact Fin.ext (by omega)
      _ ≤ 2 * m + 1 := by rw [Nat.card_Icc]; omega
  calc ((Finset.univ.filter fun a : Fin M => |((a : ℕ) + 1 : ℝ) - k| ≤ T).card : ℝ)
      ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ 3 * T := by push_cast; linarith

/-- The embeddings `Fin n ↪ Fin M` with values in `W` number at most `|W|^n`. -/
private lemma Ev_emb_card (M n : ℕ) (W : Finset (Fin M)) :
    (Finset.univ.filter fun F : Fin n ↪ Fin M => ∀ j, F j ∈ W).card ≤ W.card ^ n := by
  calc _ ≤ (Fintype.piFinset fun _ : Fin n => W).card := by
        refine Finset.card_le_card_of_injOn (fun F : Fin n ↪ Fin M => (⇑F : Fin n → Fin M)) ?_ ?_
        · intro F hF
          rw [Finset.mem_coe, Finset.mem_filter] at hF
          rw [Finset.mem_coe, Fintype.mem_piFinset]
          exact hF.2
        · intro F _ G _ h
          exact DFunLike.coe_injective h
    _ = W.card ^ n := by simp

/-- There are at most `M^n` embeddings `Fin n ↪ Fin M`. -/
private lemma Ev_emb_total (M n : ℕ) : Fintype.card (Fin n ↪ Fin M) ≤ M ^ n := by
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  exact Nat.descFactorial_le_pow M n

/-- The expectation of the indicator of a measurable set of probability at most `b`. -/
private lemma Ev_int_ind {α : Type*} [MeasurableSpace α] (μ : Measure α) {S : Set α}
    (hS : MeasurableSet S) (b : ℝ) (hb : 0 ≤ b) (h : μ S ≤ ENNReal.ofReal b) :
    ∫ w, S.indicator (1 : α → ℝ) w ∂μ ≤ b := by
  rw [integral_indicator_one hS, measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hb h

/-- `|E f - E g| ≤ a + b p₁ + c p₂` from `|f - g| ≤ a + b 1_{S₁} + c 1_{S₂}` and
`P(S_j) ≤ p_j`, for a probability measure. -/
private lemma Ev_int_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (S1 S2 : Set α) (h1 : MeasurableSet S1) (h2 : MeasurableSet S2) (a b c p1 p2 : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hS1 : μ S1 ≤ ENNReal.ofReal p1)
    (hS2 : μ S2 ≤ ENNReal.ofReal p2)
    (hpt : ∀ x, |f x - g x| ≤ a + b * S1.indicator 1 x + c * S2.indicator 1 x) :
    |∫ x, f x ∂μ - ∫ x, g x ∂μ| ≤ a + b * p1 + c * p2 := by
  have hA : Integrable (fun x => a + b * S1.indicator (1 : α → ℝ) x) μ :=
    (integrable_const a).add (((integrable_const (1 : ℝ)).indicator h1).const_mul b)
  have hB : Integrable (fun x => c * S2.indicator (1 : α → ℝ) x) μ :=
    ((integrable_const (1 : ℝ)).indicator h2).const_mul c
  have e1 := integral_add (μ := μ) hA hB
  have e2 := integral_add (μ := μ) (f := fun _ => a)
    (g := fun x => b * S1.indicator (1 : α → ℝ) x) (integrable_const a)
    (((integrable_const (1 : ℝ)).indicator h1).const_mul b)
  have i1 := Ev_int_ind μ h1 p1 hp1 hS1
  have i2 := Ev_int_ind μ h2 p2 hp2 hS2
  rw [← integral_sub hf hg]
  calc |∫ x, (f x - g x) ∂μ| ≤ ∫ x, |f x - g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (a + b * S1.indicator (1 : α → ℝ) x + c * S2.indicator (1 : α → ℝ) x) ∂μ :=
        integral_mono (hf.sub hg).abs (hA.add hB) hpt
    _ = a + b * ∫ x, S1.indicator (1 : α → ℝ) x ∂μ + c * ∫ x, S2.indicator (1 : α → ℝ) x ∂μ := by
        rw [e1, e2, integral_const, integral_const_mul, integral_const_mul, probReal_univ,
          one_smul]
    _ ≤ a + b * p1 + c * p2 := by gcongr

/-- The final count of the correlation comparison: with `P = v^{6(n+1)}`, `x = P^{-4}`,
`K₁ ≤ (3v⁶)^n`, `δ ≤ (2D + C_q) v⁶ x`, `b ≤ 3v⁶ x`, `K₂ r ≤ 2Dⁿ x` and the constant at most `v`,
`K₁ L_O δ + 2 M_O K₁ b + 2 M_O K₂ r ≤ v⁻¹`. -/
private lemma Ev_final (n : ℕ) (v P x K1 K2 LO MO δ Dr Cq b r : ℝ) (hv : 1 ≤ v)
    (hP : P = v ^ (6 * (n + 1))) (hx : x = (P ^ 4)⁻¹)
    (hK1 : K1 ≤ (3 * v ^ 6) ^ n) (hLO : 0 ≤ LO) (hMO : 0 ≤ MO) (hD : 0 ≤ Dr)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ (2 * Dr + Cq) * v ^ 6 * x) (hb0 : 0 ≤ b) (hb : b ≤ 3 * v ^ 6 * x)
    (hr : K2 * r ≤ 2 * Dr ^ n * x)
    (hK : 3 ^ n * (LO * (2 * Dr + Cq) + 6 * MO) + 4 * MO * Dr ^ n ≤ v) :
    K1 * LO * δ + K1 * 2 * MO * b + K2 * 2 * MO * r ≤ v⁻¹ := by
  have hv0 : 0 < v := by linarith
  have hP1 : 1 ≤ P := by rw [hP]; exact one_le_pow₀ hv
  have hvP : v ≤ P := by rw [hP]; exact le_self_pow₀ hv (by omega)
  have hP0 : 0 < P := by linarith
  have hx0 : 0 < x := by rw [hx]; positivity
  have h3T : (3 * v ^ 6) ^ n * v ^ 6 = 3 ^ n * P := by
    rw [hP, mul_pow, ← pow_mul, mul_assoc, ← pow_add]
    ring_nf
  have t1 : K1 * LO * δ ≤ 3 ^ n * P * (LO * (2 * Dr + Cq)) * x := by
    calc K1 * LO * δ ≤ (3 * v ^ 6) ^ n * LO * ((2 * Dr + Cq) * v ^ 6 * x) := by gcongr
      _ = ((3 * v ^ 6) ^ n * v ^ 6) * (LO * (2 * Dr + Cq)) * x := by ring
      _ = _ := by rw [h3T]
  have t2 : K1 * 2 * MO * b ≤ 3 ^ n * P * (6 * MO) * x := by
    calc K1 * 2 * MO * b ≤ (3 * v ^ 6) ^ n * 2 * MO * (3 * v ^ 6 * x) := by gcongr
      _ = ((3 * v ^ 6) ^ n * v ^ 6) * (6 * MO) * x := by ring
      _ = _ := by rw [h3T]
  have t3 : K2 * 2 * MO * r ≤ 4 * MO * Dr ^ n * P * x := by
    calc K2 * 2 * MO * r = 2 * MO * (K2 * r) := by ring
      _ ≤ 2 * MO * (2 * Dr ^ n * x) := by gcongr
      _ = 4 * MO * Dr ^ n * 1 * x := by ring
      _ ≤ 4 * MO * Dr ^ n * P * x := by gcongr
  have hsum : K1 * LO * δ + K1 * 2 * MO * b + K2 * 2 * MO * r ≤
      (3 ^ n * (LO * (2 * Dr + Cq) + 6 * MO) + 4 * MO * Dr ^ n) * P * x := by
    nlinarith
  have hv3P : v ^ 3 ≤ P ^ 3 := pow_le_pow_left₀ hv0.le hvP 3
  calc K1 * LO * δ + K1 * 2 * MO * b + K2 * 2 * MO * r
      ≤ (3 ^ n * (LO * (2 * Dr + Cq) + 6 * MO) + 4 * MO * Dr ^ n) * P * x := hsum
    _ ≤ v * P * x := by gcongr
    _ = v / P ^ 3 := by rw [hx]; field_simp
    _ ≤ v / v ^ 3 := div_le_div_of_nonneg_left hv0.le (by positivity) hv3P
    _ = (v ^ 2)⁻¹ := by field_simp
    _ ≤ v⁻¹ := inv_anti₀ hv0 (by nlinarith)

set_option maxHeartbeats 1600000 in -- one long assembly of the estimate
/-- The correlation functions of Theorem 2.5 [theorem_localized_eigenvalue] for `2k ≤ DN + 1`,
in the normalization of `ρ^(n)`: rigidity (2.24) [eq:rigidity] of `H_Λ` and of `H` and the
spacing of the quantiles restrict both pairings to the indices `|i - k| ≤ N^τ`; there (2.11)
[eq:main_perurb] and the quantile increments give the comparison. -/
private lemma Ev_corr (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (C : ℕ → ℝ) (n : ℕ) (O : (Fin n → ℝ) → ℝ) (hOcont : Continuous O)
    (hOc : HasCompactSupport O) (hOL : ∃ K, LipschitzWith K O) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : EntryLaws C, ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      |(∫ w, corrPairing (D * N) n (((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * rk D N k ^ (1 / 3 : ℝ))
            (quant (rho (lam D N A)) (D * N) k) O (eigK (HLam D N A w)) ∂(blockLaw D N L)) -
        (∫ w, corrPairing (D * N) n (((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * rk D N k ^ (1 / 3 : ℝ))
            (quant rhoSc (D * N) k) O (eigK (blockH D N w)) ∂(blockLaw D N L))| ≤
        (N : ℝ) ^ (-c) := by
  -- the test function: support in `[-R, R]^n`, `|O| ≤ MO`, Lipschitz constant `LO`
  obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin n → ℝ)).1
    hOc.isCompact.isBounded
  set R : ℝ := max R0 0 with hRdef
  have hR0' : 0 ≤ R := le_max_right _ _
  have hR : ∀ x, O x ≠ 0 → ∀ j, |x j| ≤ R := fun x hx j => by
    have h2 := hR0 (subset_tsupport O hx)
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm x j).trans (h2.trans (le_max_left _ _))
  obtain ⟨MO, hMO'⟩ := hOcont.bounded_above_of_compact_support hOc
  have hM : ∀ x, |O x| ≤ MO := fun x => by rw [← Real.norm_eq_abs]; exact hMO' x
  have hMO : 0 ≤ MO := (abs_nonneg _).trans (hM 0)
  obtain ⟨LO', hLO'⟩ := hOL
  set LO : ℝ := (LO' : ℝ) with hLOdef
  have hLO : 0 ≤ LO := NNReal.coe_nonneg LO'
  have hL : ∀ x y, |O x - O y| ≤ LO * ‖x - y‖ := fun x y => by
    have := hLO'.dist_le_mul x y
    rwa [Real.dist_eq, dist_eq_norm] at this
  -- the exponents
  obtain ⟨c', hc', Nb, hNb⟩ := Ev_211_full D hD δA (εA / 2) hδA (by positivity) C
  have hn1 : (0 : ℝ) < 24 * ((n : ℝ) + 1) := by positivity
  set θ : ℝ := min (min c' εA) 1 / (24 * ((n : ℝ) + 1)) with hθdef
  have hθ : 0 < θ := div_pos (lt_min (lt_min hc' hεA) one_pos) hn1
  have hθm : 24 * ((n : ℝ) + 1) * θ = min (min c' εA) 1 := by
    rw [hθdef]; field_simp
  have hθc : 24 * ((n : ℝ) + 1) * θ ≤ c' := hθm ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hθe : 24 * ((n : ℝ) + 1) * θ ≤ εA := hθm ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hθ1 : 24 * ((n : ℝ) + 1) * θ ≤ 1 := hθm ▸ min_le_right _ _
  have hθ24 : 24 * θ ≤ 24 * ((n : ℝ) + 1) * θ := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  set τ : ℝ := 6 * θ with hτdef
  have hτ : 0 < τ := by positivity
  have hτ1 : τ < 1 := by linarith
  have hτA : τ < εA / 2 := by linarith
  obtain ⟨cs1, Cs1, hcs1, hCs1, Ns1, hNs1⟩ := quant_spacing D hD δA τ hδA hτ hτ1
  obtain ⟨cs2, Cs2, hcs2, hCs2, Ns2, hNs2⟩ := quant_spacing_sc D hD τ hτ hτ1
  obtain ⟨Cq, hCq, Nq, hNq⟩ := quant_increment D hD δA εA τ hδA hεA hτ hτA
  obtain ⟨Nr, hNr⟩ := rigidity D (by omega) δA hδA C (3 * θ) (by positivity) ((n : ℝ) + 2)
    (by positivity)
  set K : ℝ := 3 ^ n * (LO * (2 * D + Cq) + 6 * MO) + 4 * MO * (D : ℝ) ^ n with hKdef
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.1 ((Ev_ev δA 20 hδA).and ((Ev_ev 1 1 one_pos).and
    ((Ev_ev (3 * θ) R (by positivity)).and ((Ev_ev θ (8 / cs1 + 8 / cs2 + 1) hθ).and
    ((Ev_ev (εA / 2 - 2 * θ) 2 (by linarith)).and (Ev_ev θ K hθ))))))
  refine ⟨θ, hθ, max (max (max Nb Ns1) (max Ns2 Nq)) (max Nr N₅),
    fun N hN L A hA k hk1 hk hhs => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hNb', hNs1'⟩, hNs2', hNq'⟩, hNr', hN5'⟩ := hN
  obtain ⟨h20, h1N, hRv, hcv, h2v, hKv⟩ := hN₅ N hN5'
  rw [Real.rpow_one] at h1N
  have hN0 : (0 : ℝ) < N := by linarith
  have hNnat : 1 ≤ N := by exact_mod_cast h1N
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hμ := blockLaw_isProbabilityMeasure D N L
  have hDN : 2 ≤ D * N := le_trans hD (Nat.le_mul_of_pos_right D hNnat)
  have hkM : k ≤ D * N := by omega
  have hrk : rk D N k = k := Ev_rk_half D N k hk
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
  have hNM : (N : ℝ) ≤ ((D * N : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hM0 : (0 : ℝ) < ((D * N : ℕ) : ℝ) := by linarith
  -- `v = N^θ`
  set v : ℝ := (N : ℝ) ^ θ with hvdef
  have hv1 : 1 ≤ v := Real.one_le_rpow h1N hθ.le
  have hv0 : 0 < v := by linarith
  have hpow : ∀ m : ℕ, (N : ℝ) ^ ((m : ℝ) * θ) = v ^ m := fun m => by
    rw [mul_comm, Real.rpow_mul_natCast hN0.le]
  have hT : (N : ℝ) ^ τ = v ^ 6 := by
    rw [hτdef, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, hpow]
  have hv3 : (N : ℝ) ^ (3 * θ) = v ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, hpow]
  have hvN : 2 * v ^ 2 ≤ (N : ℝ) ^ (εA / 2) := by
    have e : (N : ℝ) ^ (εA / 2) = (N : ℝ) ^ (εA / 2 - 2 * θ) * v ^ 2 := by
      rw [← hpow 2, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h2v (by positivity)
  set T : ℝ := v ^ 6 with hTdef
  have hT1 : 1 ≤ T := one_le_pow₀ hv1
  -- the deterministic inputs
  have hδN : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
    rw [Real.rpow_neg hN0.le]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  have hℓ : opNorm (lam D N A) ≤ 1 / 10 :=
    (opNorm_lam_le D N A).trans (by linarith [hA.trans hδN])
  obtain ⟨hnn, -, hint, hmass, -⟩ := rho_stieltjes (lam D N A) (lam_isHermitian D N A) hℓ
  have h0ℓ : opNorm (0 : Matrix (Idx D N) (Idx D N) ℂ) ≤ 1 / 10 := by
    have : opNorm (0 : Matrix (Idx D N) (Idx D N) ℂ) = 0 := by unfold opNorm; simp
    rw [this]; norm_num
  obtain ⟨hnn0, -, hint0, hmass0, -⟩ :=
    rho_stieltjes (0 : Matrix (Idx D N) (Idx D N) ℂ) isHermitian_zero h0ℓ
  rw [(rho_zero (ι := Idx D N)).2.1] at hnn0 hint0 hmass0
  have hγA : ∀ i j, 1 ≤ i → i ≤ j → j ≤ D * N →
      quant (rho (lam D N A)) (D * N) j ≤ quant (rho (lam D N A)) (D * N) i :=
    fun i j h1 h2 h3 => Ev_quant_anti _ hnn hint hmass (D * N) i j h1 h2 h3
  have hγS : ∀ i j, 1 ≤ i → i ≤ j → j ≤ D * N →
      quant rhoSc (D * N) j ≤ quant rhoSc (D * N) i :=
    fun i j h1 h2 h3 => Ev_quant_anti _ hnn0 hint0 hmass0 (D * N) i j h1 h2 h3
  set s : ℝ := ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * rk D N k ^ (1 / 3 : ℝ) with hsdef
  have hs' : s = ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * (k : ℝ) ^ (1 / 3 : ℝ) := by rw [hsdef, hrk]
  have hs0 : 0 < s := by
    rw [hs']
    exact mul_pos (Real.rpow_pos_of_pos hM0 _) (Real.rpow_pos_of_pos (by linarith) _)
  set e : ℕ → ℝ := fun i =>
    (N : ℝ) ^ (3 * θ) * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N i ^ (-(1 / 3 : ℝ))) with hedef
  set W : Finset (Fin (D * N)) :=
    Finset.univ.filter fun a => |((a : ℕ) + 1 : ℝ) - k| ≤ T with hWdef
  -- the spacing and the gap on the window
  have hsp1 : ∀ i, 1 ≤ i → i ≤ D * N → |(i : ℝ) - k| ≤ T →
      |(i : ℝ) - k| * (cs1 * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k + T) ^ (-(1 / 3 : ℝ)))) ≤
        |quant (rho (lam D N A)) (D * N) i - quant (rho (lam D N A)) (D * N) k| := by
    intro i hi1 hiM hik
    have h := (hNs1 N hNs1' A hA i k hi1 hiM hk1 hkM (by rw [hT]; exact hik)).2
    rw [hrk, hT] at h
    calc |(i : ℝ) - k| * (cs1 * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k + T) ^ (-(1 / 3 : ℝ))))
        = cs1 * |(i : ℝ) - k| * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k + T) ^ (-(1 / 3 : ℝ))) := by ring
      _ ≤ _ := h
  have hsp2 : ∀ i, 1 ≤ i → i ≤ D * N → |(i : ℝ) - k| ≤ T →
      |(i : ℝ) - k| * (cs2 * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k + T) ^ (-(1 / 3 : ℝ)))) ≤
        |quant rhoSc (D * N) i - quant rhoSc (D * N) k| := by
    intro i hi1 hiM hik
    have h := (hNs2 N hNs2' i k hi1 hiM hk1 hkM (by rw [hT]; exact hik)).2
    rw [hrk, hT] at h
    calc |(i : ℝ) - k| * (cs2 * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k + T) ^ (-(1 / 3 : ℝ))))
        = cs2 * |(i : ℝ) - k| * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k + T) ^ (-(1 / 3 : ℝ))) := by ring
      _ ≤ _ := h
  have hRv' : R ≤ v ^ 3 := by rw [← hv3]; exact hRv
  have hcv1 : 8 < cs1 * v := by
    have : 8 / cs1 < v := by
      have : 0 < 8 / cs2 := by positivity
      linarith
    rwa [div_lt_iff₀ hcs1, mul_comm] at this
  have hcv2 : 8 < cs2 * v := by
    have : 8 / cs2 < v := by
      have : 0 < 8 / cs1 := by positivity
      linarith
    rwa [div_lt_iff₀ hcs2, mul_comm] at this
  have hgap : ∀ cs : ℝ, 8 < cs * v → ∀ i, 1 ≤ i → i ≤ D * N → |(i : ℝ) - k| ≤ T →
      R / s + e i < T / 2 * (cs * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * (k + T) ^ (-(1 / 3 : ℝ)))) := by
    intro cs hcv i hi1 hiM hik
    have hlo := (Ev_rk_win D N k i T hT1 hk1 hk hi1 hiM hik).1
    have := Ev_gap N ((D * N : ℕ) : ℝ) k (rk D N i) R v cs hN0 hNM hkr hv1 hR0' hRv' hcv hlo
    change R / s + (N : ℝ) ^ (3 * θ) * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N i ^ (-(1 / 3 : ℝ))) <
      _
    rw [hs', hv3]
    exact this
  -- the events
  have hcH : ∀ i, Continuous fun w => eigK (HLam D N A w) i := fun i =>
    Ev_eigK_cont (HLam D N A) ((Ev_blockH_cont D N).add continuous_const)
      (HLam_isHermitian D N A) i
  have hcB : ∀ i, Continuous fun w => eigK (blockH D N w) i := fun i =>
    Ev_eigK_cont (blockH D N) (Ev_blockH_cont D N) (Ev_blockH_herm D N) i
  set rigS : Set (Fin D → Coords N) := {w | ∀ i, 1 ≤ i → i ≤ D * N →
      |eigK (HLam D N A w) i - quant (rho (lam D N A)) (D * N) i| ≤ e i ∧
        |eigK (blockH D N w) i - quant rhoSc (D * N) i| ≤ e i} with hrigS
  set Bset : Fin (D * N) → Set (Fin D → Coords N) := fun a => {w |
      (N : ℝ) ^ (-(2 / 3 : ℝ) - c') * rk D N ((a : ℕ) + 1) ^ (-(1 / 3 : ℝ)) ≤
        |shiftX D N A ((a : ℕ) + 1) w|} with hBset
  set badS : Set (Fin D → Coords N) := ⋃ a ∈ W, Bset a with hbadS
  have hrigM : MeasurableSet rigS := by
    have : IsClosed rigS := by
      simp only [hrigS, Set.ofPred_forall, Set.ofPred_and]
      refine isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
      exact (isClosed_le ((hcH i).sub continuous_const).abs continuous_const).inter
        (isClosed_le ((hcB i).sub continuous_const).abs continuous_const)
    exact this.measurableSet
  have hbadM : MeasurableSet badS := by
    have : IsClosed badS := by
      refine isClosed_biUnion_finset fun a _ => isClosed_le continuous_const ?_
      unfold shiftX
      exact (((hcH _).sub continuous_const).sub ((hcB _).sub continuous_const)).abs
    exact this.measurableSet
  -- the probabilities
  have hP_rig : blockLaw D N L rigSᶜ ≤ ENNReal.ofReal (2 * (N : ℝ) ^ (-((n : ℝ) + 2))) := by
    have hf : Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) :=
      (Ev_blockH_cont D N).measurable
    have hA0 : opNorm (0 : Matrix (Fin N) (Fin N) ℂ) ≤ (N : ℝ) ^ (-δA) := by
      have : opNorm (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by unfold opNorm; simp
      rw [this]; positivity
    have h1 := hNr N hNr' 1 zero_le_one le_rfl _ (llClass_blockH D N C L) A hA
    have h2 := hNr N hNr' 1 zero_le_one le_rfl _ (llClass_blockH D N C L) 0 hA0
    set S1 : Set (Idx D N → Idx D N → ℂ) := {h | ∃ k : ℕ, 1 ≤ k ∧ k ≤ D * N ∧
        (N : ℝ) ^ (3 * θ) * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) <
          |eigK (Matrix.of h + lam D N A) k - quant (rho (lam D N A)) (D * N) k|} with hS1
    set S2 : Set (Idx D N → Idx D N → ℂ) := {h | ∃ k : ℕ, 1 ≤ k ∧ k ≤ D * N ∧
        (N : ℝ) ^ (3 * θ) * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ))) <
          |eigK (Matrix.of h + lam D N 0) k - quant (rho (lam D N 0)) (D * N) k|} with hS2
    have hsub : rigSᶜ ⊆ (fun w => Matrix.of.symm (blockH D N w)) ⁻¹' S1 ∪
        (fun w => Matrix.of.symm (blockH D N w)) ⁻¹' S2 := by
      intro w hw
      simp only [hrigS, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_and_or,
        not_le] at hw
      obtain ⟨i, hi1, hiM, hw⟩ := hw
      rcases hw with hw | hw
      · left
        simp only [Set.mem_preimage, hS1, Set.mem_ofPred_eq, Equiv.apply_symm_apply]
        exact ⟨i, hi1, hiM, hw⟩
      · right
        simp only [Set.mem_preimage, hS2, Set.mem_ofPred_eq, Equiv.apply_symm_apply]
        refine ⟨i, hi1, hiM, ?_⟩
        rw [Ev_lam_zero, add_zero, (rho_zero (ι := Idx D N)).2.1]
        exact hw
    calc blockLaw D N L rigSᶜ
        ≤ blockLaw D N L ((fun w => Matrix.of.symm (blockH D N w)) ⁻¹' S1 ∪
            (fun w => Matrix.of.symm (blockH D N w)) ⁻¹' S2) := measure_mono hsub
      _ ≤ blockLaw D N L ((fun w => Matrix.of.symm (blockH D N w)) ⁻¹' S1) +
            blockLaw D N L ((fun w => Matrix.of.symm (blockH D N w)) ⁻¹' S2) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-((n : ℝ) + 2))) +
            ENNReal.ofReal ((N : ℝ) ^ (-((n : ℝ) + 2))) :=
          add_le_add ((Measure.le_map_apply hf.aemeasurable _).trans h1)
            ((Measure.le_map_apply hf.aemeasurable _).trans h2)
      _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-((n : ℝ) + 2))) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  have hP_bad : blockLaw D N L badS ≤ ENNReal.ofReal (3 * T * (N : ℝ) ^ (-c')) := by
    refine (measure_biUnion_finset_le W Bset).trans ?_
    calc ∑ a ∈ W, blockLaw D N L (Bset a)
        ≤ ∑ _a ∈ W, ENNReal.ofReal ((N : ℝ) ^ (-c')) := Finset.sum_le_sum fun a ha => ?_
      _ = ENNReal.ofReal (W.card * (N : ℝ) ^ (-c')) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (3 * T * (N : ℝ) ^ (-c')) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Ev_win_card _ k T hT1)
            (by positivity))
    have hi1 : 1 ≤ (a : ℕ) + 1 := by omega
    have hiM : (a : ℕ) + 1 ≤ D * N := a.isLt
    have hik : |(((a : ℕ) + 1 : ℕ) : ℝ) - k| ≤ T := by
      have := (Finset.mem_filter.1 ha).2
      push_cast
      exact this
    obtain ⟨hlo, hhi⟩ := Ev_rk_win D N k ((a : ℕ) + 1) T hT1 hk1 hk hi1 hiM hik
    have hri0 : 0 < rk D N ((a : ℕ) + 1) := lt_of_lt_of_le (by positivity) hlo
    have hhs' := Ev_hs_win N k (rk D N ((a : ℕ) + 1)) v εA (hsNorm A) hN0 (by linarith) hri0
      hv1 hhi hvN (by rw [hrk] at hhs; exact hhs)
    exact hNb N hNb' L A hA ((a : ℕ) + 1) hi1 hiM hhs'
  -- the pointwise comparison
  set δ : ℝ := 2 * D * v ^ 2 * (N : ℝ) ^ (-c') + Cq * (N : ℝ) ^ (τ - εA) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  set K1 : ℝ := ((Finset.univ.filter fun F : Fin n ↪ Fin (D * N) => ∀ j, F j ∈ W).card : ℝ)
    with hK1def
  set K2 : ℝ := (Fintype.card (Fin n ↪ Fin (D * N)) : ℝ) with hK2def
  have hpt : ∀ w, |corrPairing (D * N) n s (quant (rho (lam D N A)) (D * N) k) O
      (eigK (HLam D N A w)) - corrPairing (D * N) n s (quant rhoSc (D * N) k) O
        (eigK (blockH D N w))| ≤
      K1 * LO * δ + (K1 * 2 * MO) * badS.indicator 1 w +
        (K2 * 2 * MO) * rigSᶜ.indicator 1 w := by
    intro w
    have hout : w ∈ rigS → ∀ a : Fin (D * N), a ∉ W →
        R < |s * (eigK (HLam D N A w) ((a : ℕ) + 1) - quant (rho (lam D N A)) (D * N) k)| ∧
          R < |s * (eigK (blockH D N w) ((a : ℕ) + 1) - quant rhoSc (D * N) k)| := by
      intro hrig a ha
      have hr := hrig
      simp only [hrigS, Set.mem_ofPred_eq] at hr
      have hi1 : 1 ≤ (a : ℕ) + 1 := by omega
      have hiM : (a : ℕ) + 1 ≤ D * N := a.isLt
      have hik : T < |(((a : ℕ) + 1 : ℕ) : ℝ) - k| := by
        simp only [hWdef, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at ha
        push_cast
        exact ha
      have hev1 : ∀ i j, 1 ≤ i → i ≤ j → j ≤ D * N →
          eigK (HLam D N A w) j ≤ eigK (HLam D N A w) i := fun i j h1 h2 h3 =>
        Ev_eigK_anti _ (HLam_isHermitian D N A w) i j h1 h2 (by rw [Ev_card]; exact h3)
      have hev2 : ∀ i j, 1 ≤ i → i ≤ j → j ≤ D * N →
          eigK (blockH D N w) j ≤ eigK (blockH D N w) i := fun i j h1 h2 h3 =>
        Ev_eigK_anti _ (Ev_blockH_herm D N w) i j h1 h2 (by rw [Ev_card]; exact h3)
      have w1 := Ev_window (D * N) k hk1 hkM T hT1 (eigK (HLam D N A w))
        (quant (rho (lam D N A)) (D * N)) e hev1 hγA (fun i h1 h2 => (hr i h1 h2).1)
        _ (by positivity) hsp1 (R / s) (hgap cs1 hcv1) ((a : ℕ) + 1) hi1 hiM hik
      have w2 := Ev_window (D * N) k hk1 hkM T hT1 (eigK (blockH D N w))
        (quant rhoSc (D * N)) e hev2 hγS (fun i h1 h2 => (hr i h1 h2).2)
        _ (by positivity) hsp2 (R / s) (hgap cs2 hcv2) ((a : ℕ) + 1) hi1 hiM hik
      rw [div_lt_iff₀ hs0] at w1 w2
      have hsabs : ∀ x : ℝ, |s * x| = s * |x| := fun x => by rw [abs_mul, abs_of_pos hs0]
      rw [hsabs, hsabs]
      constructor <;> linarith
    have hclose : w ∈ rigS → w ∉ badS → ∀ a ∈ W,
        |s * (eigK (HLam D N A w) ((a : ℕ) + 1) - quant (rho (lam D N A)) (D * N) k) -
          s * (eigK (blockH D N w) ((a : ℕ) + 1) - quant rhoSc (D * N) k)| ≤ δ := by
      intro _ hnb a ha
      have hi1 : 1 ≤ (a : ℕ) + 1 := by omega
      have hiM : (a : ℕ) + 1 ≤ D * N := a.isLt
      have hik : |(((a : ℕ) + 1 : ℕ) : ℝ) - k| ≤ T := by
        have := (Finset.mem_filter.1 ha).2
        push_cast
        exact this
      have hX : |shiftX D N A ((a : ℕ) + 1) w| <
          (N : ℝ) ^ (-(2 / 3 : ℝ) - c') * rk D N ((a : ℕ) + 1) ^ (-(1 / 3 : ℝ)) := by
        by_contra hc
        push Not at hc
        exact hnb (Set.mem_biUnion (Finset.mem_coe.2 ha) hc)
      have hQ := hNq N hNq' A hA k hk1 hk hhs ((a : ℕ) + 1) hi1 hiM (by rw [hT]; exact hik)
      rw [hrk] at hQ
      obtain ⟨hlo, -⟩ := Ev_rk_win D N k ((a : ℕ) + 1) T hT1 hk1 hk hi1 hiM hik
      have hri : (k : ℝ) / (4 * v ^ 6) ≤ rk D N ((a : ℕ) + 1) :=
        le_trans (div_le_div_of_nonneg_right (by linarith) (by positivity)) hlo
      have hc := Ev_close D N ((D * N : ℕ) : ℝ) k (rk D N ((a : ℕ) + 1)) v c'
        (shiftX D N A ((a : ℕ) + 1) w) _ (Cq * (N : ℝ) ^ (τ - εA)) hDr hN0 (by push_cast; ring)
        hkr hv1 hri hX hQ (by positivity)
      have e1 : s * (eigK (HLam D N A w) ((a : ℕ) + 1) - quant (rho (lam D N A)) (D * N) k) -
          s * (eigK (blockH D N w) ((a : ℕ) + 1) - quant rhoSc (D * N) k) =
          s * (shiftX D N A ((a : ℕ) + 1) w +
            ((quant (rho (lam D N A)) (D * N) ((a : ℕ) + 1) - quant rhoSc (D * N) ((a : ℕ) + 1)) -
              (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k))) := by
        unfold shiftX
        ring
      rw [e1, hs']
      exact hc
    have hb := Ev_pair_bound (D * N) n s (quant (rho (lam D N A)) (D * N) k)
      (quant rhoSc (D * N) k) O R MO LO δ hR hM hL hLO hδ0 (eigK (HLam D N A w))
      (eigK (blockH D N w)) W (w ∈ badS) (w ∈ rigS) hout hclose
    have hir : (if w ∈ rigS then (0 : ℝ) else 1) = rigSᶜ.indicator 1 w := by
      by_cases h : w ∈ rigS <;> simp [h]
    have hib : (if w ∈ badS then (1 : ℝ) else 0) = badS.indicator 1 w := by
      simp [Set.indicator_apply]
    rw [hir, hib] at hb
    calc _ ≤ _ := hb
      _ = _ := by ring
  -- the integrals
  have hfc : Continuous fun w => corrPairing (D * N) n s (quant (rho (lam D N A)) (D * N) k) O
      (eigK (HLam D N A w)) := by
    unfold corrPairing
    exact continuous_finsetSum _ fun F _ => hOcont.comp (continuous_pi fun j =>
      continuous_const.mul ((hcH _).sub continuous_const))
  have hgc : Continuous fun w => corrPairing (D * N) n s (quant rhoSc (D * N) k) O
      (eigK (blockH D N w)) := by
    unfold corrPairing
    exact continuous_finsetSum _ fun F _ => hOcont.comp (continuous_pi fun j =>
      continuous_const.mul ((hcB _).sub continuous_const))
  have hbd : ∀ (γ : ℝ) (ev : ℕ → ℝ), ‖corrPairing (D * N) n s γ O ev‖ ≤ K2 * MO := by
    intro γ ev
    unfold corrPairing
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ F : Fin n ↪ Fin (D * N), |O fun j => s * (ev ((F j : ℕ) + 1) - γ)|
        ≤ ∑ _F : Fin n ↪ Fin (D * N), MO := Finset.sum_le_sum fun F _ => hM _
      _ = K2 * MO := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfi : Integrable (fun w => corrPairing (D * N) n s (quant (rho (lam D N A)) (D * N) k) O
      (eigK (HLam D N A w))) (blockLaw D N L) :=
    Integrable.of_bound hfc.aestronglyMeasurable (K2 * MO) (ae_of_all _ fun w => hbd _ _)
  have hgi : Integrable (fun w => corrPairing (D * N) n s (quant rhoSc (D * N) k) O
      (eigK (blockH D N w))) (blockLaw D N L) :=
    Integrable.of_bound hgc.aestronglyMeasurable (K2 * MO) (ae_of_all _ fun w => hbd _ _)
  have hK10 : 0 ≤ K1 := Nat.cast_nonneg _
  have hK20 : 0 ≤ K2 := Nat.cast_nonneg _
  refine (Ev_int_bound (blockLaw D N L) _ _ hfi hgi badS rigSᶜ hbadM hrigM.compl (K1 * LO * δ)
    (K1 * 2 * MO) (K2 * 2 * MO) _ _ (by positivity) (by positivity) (by positivity)
    (by positivity) hP_bad hP_rig hpt).trans ?_
  -- the final count
  set P : ℝ := v ^ (6 * (n + 1)) with hPdef
  have hV : (N : ℝ) ^ (24 * ((n : ℝ) + 1) * θ) = P ^ 4 := by
    rw [hPdef, ← pow_mul, show 24 * ((n : ℝ) + 1) = ((6 * (n + 1) * 4 : ℕ) : ℝ) by push_cast; ring,
      hpow]
  have hneg : ∀ a : ℝ, 24 * ((n : ℝ) + 1) * θ ≤ a → (N : ℝ) ^ (-a) ≤ (P ^ 4)⁻¹ := by
    intro a ha
    rw [← hV, ← Real.rpow_neg hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le h1N (by linarith)
  have hK1 : K1 ≤ (3 * v ^ 6) ^ n := by
    have h1 : K1 ≤ (W.card : ℝ) ^ n := by
      rw [hK1def]
      exact_mod_cast Ev_emb_card (D * N) n W
    exact h1.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (Ev_win_card _ k T hT1) n)
  have hδb : δ ≤ (2 * D + Cq) * v ^ 6 * (P ^ 4)⁻¹ := by
    have h1 := hneg c' hθc
    have h2 : (N : ℝ) ^ (τ - εA) ≤ v ^ 6 * (P ^ 4)⁻¹ := by
      rw [sub_eq_add_neg, Real.rpow_add hN0, hT]
      exact mul_le_mul_of_nonneg_left (hneg εA hθe) (by positivity)
    have hv26 : v ^ 2 ≤ v ^ 6 := pow_le_pow_right₀ hv1 (by norm_num)
    have hx0 : 0 ≤ (P ^ 4)⁻¹ := by positivity
    calc δ ≤ 2 * D * v ^ 2 * (P ^ 4)⁻¹ + Cq * (v ^ 6 * (P ^ 4)⁻¹) := by
          rw [hδdef]
          gcongr
      _ ≤ 2 * D * v ^ 6 * (P ^ 4)⁻¹ + Cq * (v ^ 6 * (P ^ 4)⁻¹) := by gcongr
      _ = (2 * D + Cq) * v ^ 6 * (P ^ 4)⁻¹ := by ring
  have hbb : 3 * T * (N : ℝ) ^ (-c') ≤ 3 * v ^ 6 * (P ^ 4)⁻¹ :=
    mul_le_mul_of_nonneg_left (hneg c' hθc) (by positivity)
  have hrb : K2 * (2 * (N : ℝ) ^ (-((n : ℝ) + 2))) ≤ 2 * (D : ℝ) ^ n * (P ^ 4)⁻¹ := by
    have hK2 : K2 ≤ (D : ℝ) ^ n * (N : ℝ) ^ n := by
      rw [hK2def, ← mul_pow]
      exact_mod_cast (Ev_emb_total (D * N) n)
    have hNn : (N : ℝ) ^ n * (N : ℝ) ^ (-((n : ℝ) + 2)) ≤ (P ^ 4)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hN0,
        show (n : ℝ) + -((n : ℝ) + 2) = -2 by ring]
      exact hneg 2 (by linarith)
    calc K2 * (2 * (N : ℝ) ^ (-((n : ℝ) + 2)))
        ≤ (D : ℝ) ^ n * (N : ℝ) ^ n * (2 * (N : ℝ) ^ (-((n : ℝ) + 2))) := by gcongr
      _ = 2 * (D : ℝ) ^ n * ((N : ℝ) ^ n * (N : ℝ) ^ (-((n : ℝ) + 2))) := by ring
      _ ≤ 2 * (D : ℝ) ^ n * (P ^ 4)⁻¹ := by gcongr
  have hKv' : 3 ^ n * (LO * (2 * D + Cq) + 6 * MO) + 4 * MO * (D : ℝ) ^ n ≤ v := hKv
  have hfin := Ev_final n v P (P ^ 4)⁻¹ K1 K2 LO MO δ D Cq (3 * T * (N : ℝ) ^ (-c'))
    (2 * (N : ℝ) ^ (-((n : ℝ) + 2))) hv1 hPdef rfl hK1 hLO hMO (by positivity)
    hδ0 hδb (by positivity) hbb hrb hKv'
  rw [Real.rpow_neg hN0.le θ]
  exact hfin

/-- Theorem 2.5 [theorem_localized_eigenvalue] for `2k ≤ DN + 1`. -/
theorem localized_eval_half : LocalizedEvalHalf := by
  intro D hD δA εA hδA hεA C
  refine ⟨fun ε ε₀ hε hε₀ hεε => Ev_210 D hD δA εA hδA hεA C ε ε₀ hε hε₀ hεε,
    Ev_211 D hD δA εA hδA hεA C, fun n O hO hOc => ?_⟩
  exact Ev_corr D hD δA εA hδA hεA C n O hO.continuous hOc
    (hO.lipschitzWith_of_hasCompactSupport hOc (by simp))

end RBMTransitionEdge

end
