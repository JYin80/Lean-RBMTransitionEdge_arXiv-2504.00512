module

public import RBMTransitionEdge.Edge.FcClose
public import RBMTransitionEdge.Edge.Regular

@[expose] public section

/-!
# Lemma 4.1: the edge eigenvalues of `H_Λ(𝔱)` against a GUE

Under the external input of its proof (the edge universality of Dyson Brownian motion for
`η_*`-regular initial data), the `n` largest eigenvalues of `H_Λ(𝔱)`, `𝔱 = N^{-1/3+𝔠}`, rescaled by
`γ₊ (DN)^{2/3}` at `E⁺`, have the law of the `n` largest eigenvalues of a GUE up to `N^{-c}`
(Lemma 4.1 [CVtG], (4.2) [ls_CVtG]).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The map `h ↦ ‖h - B‖` from arrays to the operator norm is continuous. -/
private lemma CVtG_cont_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) :
    Continuous fun h : ι → ι → ℂ => opNorm (Matrix.of h - B) := by
  have h1 : Continuous fun h : ι → ι → ℂ => (Matrix.of h - B : Matrix ι ι ℂ) := by
    fun_prop
  have h2 : Continuous fun X : Matrix ι ι ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) X :=
    LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).toAlgEquiv.toLinearMap
  exact continuous_norm.comp (h2.comp h1)

/-- The `k`-th largest eigenvalue is a measurable function of the array of entries: it is `0` off
the closed set of Hermitian arrays and `1`-Lipschitz on it (Weyl's inequality). -/
private lemma CVtG_meas_eigK {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    Measurable fun h : ι → ι → ℂ => eigK (Matrix.of h) k := by
  set S : Set (ι → ι → ℂ) := {h | (Matrix.of h).IsHermitian} with hS
  have hSc : IsClosed S := by
    have : S = ⋂ i, ⋂ j, {h : ι → ι → ℂ | star (h j i) = h i j} := by
      ext h
      simp only [hS, Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro hh i j
        exact hh.apply i j
      · intro hh
        exact Matrix.IsHermitian.ext fun i j => hh i j
    rw [this]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    exact isClosed_eq (continuous_star.comp ((continuous_apply i).comp (continuous_apply j)))
      ((continuous_apply j).comp (continuous_apply i))
  have hzero : ∀ h : ι → ι → ℂ, h ∉ S → eigK (Matrix.of h) k = 0 := by
    intro h hh
    have : ¬ (Matrix.of h).IsHermitian := hh
    simp [eigK, eigs, this]
  have hcont : ContinuousOn (fun h : ι → ι → ℂ => eigK (Matrix.of h) k) S := by
    intro h₀ hh₀
    rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    have hg : Filter.Tendsto (fun h : ι → ι → ℂ => opNorm (Matrix.of h - Matrix.of h₀))
        (𝓝[S] h₀) (𝓝 0) := by
      have := ((CVtG_cont_opNorm (Matrix.of h₀)).tendsto h₀).mono_left
        (nhdsWithin_le_nhds (s := S))
      have h0 : opNorm (Matrix.of h₀ - Matrix.of h₀) = 0 := by
        rw [sub_self]; unfold opNorm; rw [map_zero, norm_zero]
      rwa [h0] at this
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hg
    refine eventually_nhdsWithin_of_forall fun h hh => ?_
    rw [Real.dist_eq]
    have := eigK_add_sub_le (Matrix.of h₀) (Matrix.of h - Matrix.of h₀) hh₀
      (Matrix.IsHermitian.sub hh hh₀) k
    rwa [add_sub_cancel] at this
  have hpw : (fun h : ι → ι → ℂ => eigK (Matrix.of h) k) =
      S.piecewise (fun h : ι → ι → ℂ => eigK (Matrix.of h) k) (fun _ => 0) := by
    funext h
    by_cases hh : h ∈ S
    · rw [Set.piecewise_eq_of_mem _ _ _ hh]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hh, hzero h hh]
  rw [hpw]
  exact ContinuousOn.measurable_piecewise hcont continuousOn_const hSc.measurableSet

/-- `eigK (h + B) k` is a measurable function of the array `h`, for a fixed matrix `B`. -/
private lemma CVtG_meas_eigK_add {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (k : ℕ) : Measurable fun h : ι → ι → ℂ => eigK (Matrix.of h + B) k := by
  have h1 : Measurable fun h : ι → ι → ℂ => h + Matrix.of.symm B := by fun_prop
  have h2 := (CVtG_meas_eigK (ι := ι) k).comp h1
  convert h2 using 2 with h
  simp only [Function.comp_apply]
  congr 1

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private lemma CVtG_meas_wig (n : ℕ) (i j : Fin n) :
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

/-- The array `e^{-t/2} H(w) + √(1 - e^{-t}) W(x)` (`t = 𝔱`) of the image law in (4.3)
[eq:eq_in_law_H], as a function of the pair `(w, x)` of block coordinates and GUE coordinates. -/
private def CVtG_psi (D N : ℕ) (ct : ℝ) (p : (Fin D → Coords N) × Coords (D * N)) :
    Idx D N → Idx D N → ℂ :=
  Matrix.of.symm (((Real.exp (-edgeTime N ct / 2) : ℝ) : ℂ) • blockH D N p.1 +
    ((Real.sqrt (1 - Real.exp (-edgeTime N ct)) : ℝ) : ℂ) • gueIdx D N p.2)

/-- `CVtG_psi` is measurable in `(w, x)`. -/
private lemma CVtG_meas_psi (D N : ℕ) (ct : ℝ) : Measurable (CVtG_psi D N ct) := by
  refine measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => ?_
  have h1 : Measurable fun z : (Fin D → Coords N) × Coords (D * N) => blockH D N z.1 p q := by
    unfold blockH
    by_cases h : p.1 = q.1
    · simp only [h, ↓reduceIte]
      exact (CVtG_meas_wig N _ _).comp ((measurable_pi_apply _).comp measurable_fst)
    · simp only [h, ↓reduceIte]
      exact measurable_const
  have h2 : Measurable fun z : (Fin D → Coords N) × Coords (D * N) => gueIdx D N z.2 p q :=
    (CVtG_meas_wig (D * N) _ _).comp measurable_snd
  simp only [CVtG_psi, Matrix.of_symm_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact (measurable_const.mul h1).add (measurable_const.mul h2)

/-- The observable `O` applied to `a (b - λ_i)`, `i = 1, …, n`, for the eigenvalues `λ_i` of the
array `h + Λ`, `Λ = lam D N A` (the integrand of (4.2) [ls_CVtG] with `a = γ₊ (DN)^{2/3}`,
`b = E⁺`). -/
private def CVtG_F {n : ℕ} (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (O : (Fin n → ℝ) → ℝ)
    (a b : ℝ) (h : Idx D N → Idx D N → ℂ) : ℝ :=
  O (fun i => a * (b - eigK (Matrix.of h + lam D N A) ((i : ℕ) + 1)))

/-- `CVtG_F` is a measurable function of the array, for continuous `O`. -/
private lemma CVtG_meas_F {n : ℕ} (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (O : (Fin n → ℝ) → ℝ) (hO : Continuous O) (a b : ℝ) :
    Measurable (CVtG_F D N A O a b) := by
  unfold CVtG_F
  refine hO.measurable.comp (measurable_pi_iff.mpr fun i => ?_)
  exact measurable_const.mul (measurable_const.sub
    (CVtG_meas_eigK_add (lam D N A) ((i : ℕ) + 1)))

/-- The array `ψ(w, x)` plus `Λ` is `V + √t' W` with `V = e^{-𝔱/2} H(w) + Λ`,
`t' = 1 - e^{-𝔱}`, `W = W(x)` (proof of Lemma 4.1 [CVtG]). -/
private lemma CVtG_psi_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (ct : ℝ)
    (w : Fin D → Coords N) (x : Coords (D * N)) :
    Matrix.of (CVtG_psi D N ct (w, x)) + lam D N A =
      edgeV D N A ct w + ((Real.sqrt (1 - Real.exp (-edgeTime N ct)) : ℝ) : ℂ) • gueIdx D N x := by
  unfold CVtG_psi edgeV
  rw [Matrix.of.apply_symm_apply]
  abel

/-- The block matrix `H(w)` is Hermitian. -/
private lemma CVtG_blockH_herm (D N : ℕ) (w : Fin D → Coords N) : (blockH D N w).IsHermitian := by
  have h := (HLam_isHermitian D N 0 w).sub (lam_isHermitian D N 0)
  simpa [HLam] using h

/-- The matrix `V = e^{-𝔱/2} H(w) + Λ` of the proof of Lemma 4.1 [CVtG] is Hermitian. -/
private lemma CVtG_edgeV_herm (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (ct : ℝ)
    (w : Fin D → Coords N) : (edgeV D N A ct w).IsHermitian := by
  unfold edgeV
  exact ((CVtG_blockH_herm D N w).smul (Complex.conj_ofReal _)).add (lam_isHermitian D N A)

/-- Replacement of `(γ₊, E⁺)` by `(γ_fc, E_fc)` inside a smooth compactly supported observable
(proof of Lemma 4.1 [CVtG]): `K` is the product of a Lipschitz constant of `O` and the size of its
support, and it does not depend on the eigenvalues `e i`. For `γ ∈ [1/2, 2]`, `|γ' - γ| ≤ η ≤ 1/4`
and `s |E' - E| ≤ d`, the observable changes by at most `K (η + d)`. -/
private lemma CVtG_repl {n : ℕ} (O : (Fin n → ℝ) → ℝ) (hO : ContDiff ℝ ∞ O)
    (hOc : HasCompactSupport O) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s γ γ' E E' η d : ℝ) (e : Fin n → ℝ), 0 ≤ s → 1 / 2 ≤ γ → γ ≤ 2 →
      0 ≤ η → η ≤ 1 / 4 → |γ' - γ| ≤ η → s * |E' - E| ≤ d →
      |O (fun i => γ * s * (E - e i)) - O (fun i => γ' * s * (E' - e i))| ≤ K * (η + d) := by
  obtain ⟨L, hL⟩ := hO.lipschitzWith_of_hasCompactSupport hOc (by simp)
  obtain ⟨r, hr⟩ := hOc.isCompact.isBounded.subset_closedBall (0 : Fin n → ℝ)
  set R : ℝ := max r 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hsupp : ∀ y : Fin n → ℝ, O y ≠ 0 → ∀ i, |y i| ≤ R := by
    intro y hy i
    have h1 : y ∈ tsupport O := subset_tsupport _ (Function.mem_support.mpr hy)
    have h2 := hr h1
    rw [mem_closedBall_zero_iff] at h2
    have h3 : ‖y i‖ ≤ ‖y‖ := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at h3
    exact h3.trans (h2.trans (le_max_left _ _))
  refine ⟨(L : ℝ) * (4 * R + 3), by positivity, ?_⟩
  intro s γ γ' E E' η d e hs hγ1 hγ2 hη0 hη1 hγγ' hd
  have hd0 : 0 ≤ d := le_trans (by positivity) hd
  have hγ'1 : 1 / 4 ≤ γ' := by
    have := (abs_le.mp hγγ').1
    linarith
  have hγ'2 : γ' ≤ 3 := by
    have := (abs_le.mp hγγ').2
    linarith
  set Y : Fin n → ℝ := fun i => γ * s * (E - e i) with hY
  set Y' : Fin n → ℝ := fun i => γ' * s * (E' - e i) with hY'
  set Dd : ℝ := s * (E' - E) with hDd
  have hDd' : |Dd| ≤ d := by
    rw [hDd, abs_mul, abs_of_nonneg hs]
    exact hd
  have hbd : ∀ i, O Y ≠ 0 ∨ O Y' ≠ 0 → |Y i - Y' i| ≤ (4 * R + 3) * (η + d) := by
    intro i hne
    have hgg : |γ - γ'| ≤ η := by rw [abs_sub_comm]; exact hγγ'
    rcases hne with h | h
    · have hYi : |γ * (s * (E - e i))| ≤ R := by
        have := hsupp Y h i
        rw [hY] at this
        simpa [mul_assoc] using this
      have hu : |s * (E - e i)| ≤ 2 * R := by
        rw [abs_mul, abs_of_pos (by linarith : 0 < γ)] at hYi
        nlinarith [abs_nonneg (s * (E - e i))]
      have heq : Y i - Y' i = (γ - γ') * (s * (E - e i)) - γ' * Dd := by
        simp only [hY, hY', hDd]; ring
      rw [heq]
      calc |(γ - γ') * (s * (E - e i)) - γ' * Dd|
          ≤ |(γ - γ') * (s * (E - e i))| + |γ' * Dd| := abs_sub _ _
        _ = |γ - γ'| * |s * (E - e i)| + |γ'| * |Dd| := by
            rw [abs_mul (γ - γ') (s * (E - e i)), abs_mul γ' Dd]
        _ ≤ η * (2 * R) + 3 * d := by
            rw [abs_of_pos (by linarith : 0 < γ')]
            gcongr
        _ ≤ (4 * R + 3) * (η + d) := by nlinarith [mul_nonneg hR0 hη0, mul_nonneg hR0 hd0]
    · have hYi : |γ' * (s * (E' - e i))| ≤ R := by
        have := hsupp Y' h i
        rw [hY'] at this
        simpa [mul_assoc] using this
      have hu : |s * (E' - e i)| ≤ 4 * R := by
        rw [abs_mul, abs_of_pos (by linarith : 0 < γ')] at hYi
        nlinarith [abs_nonneg (s * (E' - e i))]
      have heq : Y i - Y' i = (γ - γ') * (s * (E' - e i)) - γ * Dd := by
        simp only [hY, hY', hDd]; ring
      rw [heq]
      calc |(γ - γ') * (s * (E' - e i)) - γ * Dd|
          ≤ |(γ - γ') * (s * (E' - e i))| + |γ * Dd| := abs_sub _ _
        _ = |γ - γ'| * |s * (E' - e i)| + |γ| * |Dd| := by
            rw [abs_mul (γ - γ') (s * (E' - e i)), abs_mul γ Dd]
        _ ≤ η * (4 * R) + 2 * d := by
            rw [abs_of_pos (by linarith : 0 < γ)]
            gcongr
        _ ≤ (4 * R + 3) * (η + d) := by nlinarith [mul_nonneg hR0 hη0, mul_nonneg hR0 hd0]
  by_cases hz : O Y ≠ 0 ∨ O Y' ≠ 0
  · have hdist : dist Y Y' ≤ (4 * R + 3) * (η + d) := by
      rw [dist_pi_le_iff (by positivity)]
      intro i
      rw [Real.dist_eq]
      exact hbd i hz
    have := hL.dist_le_mul Y Y'
    rw [Real.dist_eq] at this
    calc |O Y - O Y'| ≤ (L : ℝ) * dist Y Y' := this
      _ ≤ (L : ℝ) * ((4 * R + 3) * (η + d)) := by gcongr
      _ = (L : ℝ) * (4 * R + 3) * (η + d) := by ring
  · simp only [not_or, not_not] at hz
    rw [hz.1, hz.2, sub_self, abs_zero]
    positivity

/-- Averaging a function that is within `b₁` of `e` off a measurable set `T` and within `b₂` of
`e` everywhere: `|∫ a - e| ≤ b₁ + b₂ P(T)` (the split into the good event and its complement in
the proof of Lemma 4.1 [CVtG]). -/
private lemma CVtG_outer {W : Type*} [MeasurableSpace W] (P : Measure W) [IsProbabilityMeasure P]
    (a : W → ℝ) (ha : Integrable a P) (e b₁ b₂ : ℝ) (T : Set W) (hT : MeasurableSet T)
    (h1 : ∀ w, w ∉ T → |a w - e| ≤ b₁) (h2 : ∀ w, |a w - e| ≤ b₂) (hb₁ : 0 ≤ b₁) :
    |(∫ w, a w ∂P) - e| ≤ b₁ + b₂ * P.real T := by
  have hint : (∫ w, a w ∂P) - e = ∫ w, (a w - e) ∂P := by
    rw [integral_sub ha (integrable_const e), integral_const]
    simp
  have hind : Integrable (fun w => b₁ + b₂ * T.indicator (fun _ => (1 : ℝ)) w) P :=
    (integrable_const b₁).add (((integrable_const (1 : ℝ)).indicator hT).const_mul b₂)
  calc |(∫ w, a w ∂P) - e| = ‖∫ w, (a w - e) ∂P‖ := by rw [hint, Real.norm_eq_abs]
    _ ≤ ∫ w, ‖a w - e‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ w, (b₁ + b₂ * T.indicator (fun _ => (1 : ℝ)) w) ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hind
          (Eventually.of_forall fun w => ?_)
        change ‖a w - e‖ ≤ b₁ + b₂ * T.indicator (fun _ => (1 : ℝ)) w
        rw [Real.norm_eq_abs]
        by_cases hw : w ∈ T
        · rw [Set.indicator_of_mem hw]
          linarith [h2 w]
        · rw [Set.indicator_of_notMem hw]
          linarith [h1 w hw]
    _ = b₁ + b₂ * P.real T := by
        rw [integral_add (integrable_const b₁)
            (((integrable_const (1 : ℝ)).indicator hT).const_mul b₂),
          integral_const, integral_const_mul, integral_indicator_const _ hT]
        simp

/-- Fubini for the law `ouMatLaw L 𝔱` of (4.3) [eq:eq_in_law_H]: the expectation of the bounded
observable `CVtG_F` is the average over the block coordinates `w` of its average over the GUE
coordinates `x`; the inner average is integrable in `w`. -/
private lemma CVtG_fubini {n : ℕ} (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C)
    (A : Matrix (Fin N) (Fin N) ℂ) (ct : ℝ) (O : (Fin n → ℝ) → ℝ) (hO : Continuous O) (B : ℝ)
    (hB : ∀ y, |O y| ≤ B) (a b : ℝ) :
    Integrable (fun w => ∫ x, CVtG_F D N A O a b (CVtG_psi D N ct (w, x)) ∂(gueLaw (D * N)))
        (blockLaw D N L) ∧
      ∫ h, CVtG_F D N A O a b h ∂(ouMatLaw D N L (edgeTime N ct)) =
        ∫ w, ∫ x, CVtG_F D N A O a b (CVtG_psi D N ct (w, x)) ∂(gueLaw (D * N))
          ∂(blockLaw D N L) := by
  have hψ := CVtG_meas_psi D N ct
  have hF := CVtG_meas_F D N A O hO a b
  have hFψ : Measurable fun p => CVtG_F D N A O a b (CVtG_psi D N ct p) := hF.comp hψ
  have hint : Integrable (fun p => CVtG_F D N A O a b (CVtG_psi D N ct p))
      ((blockLaw D N L).prod (gueLaw (D * N))) :=
    Integrable.of_bound hFψ.aestronglyMeasurable B (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hB _)
  refine ⟨hint.integral_prod_left, ?_⟩
  have hmap : ouMatLaw D N L (edgeTime N ct) =
      ((blockLaw D N L).prod (gueLaw (D * N))).map (CVtG_psi D N ct) :=
    ouMatLaw_eq_map D N L (edgeTime N ct)
  rw [hmap, integral_map hψ.aemeasurable hF.aestronglyMeasurable]
  exact integral_prod _ hint

/-- The inner bound of the proof of Lemma 4.1 [CVtG] at one configuration `w` of the block part
on the good event: the external input (the law of the `n` largest eigenvalues of `V + √t' W`
rescaled by `γ_fc (DN)^{2/3}` at `E_fc`) and the replacement of `(γ_fc, E_fc)` by `(γ₊, E⁺)`,
which changes the observable by at most `K (N^{-ε} + D^{2/3} N^{-ε})`. -/
private lemma CVtG_inner {n : ℕ} (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (ct ε cE EG : ℝ)
    (O : (Fin n → ℝ) → ℝ) (hO : Continuous O) (B : ℝ) (hB : ∀ y, |O y| ≤ B) (K : ℝ)
    (hK : ∀ (s γ γ' E E' η d : ℝ) (e : Fin n → ℝ), 0 ≤ s → 1 / 2 ≤ γ → γ ≤ 2 →
      0 ≤ η → η ≤ 1 / 4 → |γ' - γ| ≤ η → s * |E' - E| ≤ d →
      |O (fun i => γ * s * (E - e i)) - O (fun i => γ' * s * (E' - e i))| ≤ K * (η + d))
    (hγ1 : 1 / 2 ≤ gammaPlus (lam D N A)) (hγ2 : gammaPlus (lam D N A) ≤ 2)
    (hη : (N : ℝ) ^ (-ε) ≤ 1 / 4) (hN : 1 ≤ N) (w : Fin D → Coords N)
    (hE : |fcEdge (edgeV D N A ct w) (1 - Real.exp (-edgeTime N ct)) - Eplus (lam D N A)| ≤
      (N : ℝ) ^ (-(2 / 3 : ℝ) - ε))
    (hG : |fcGamma (edgeV D N A ct w) (1 - Real.exp (-edgeTime N ct)) - gammaPlus (lam D N A)| ≤
      (N : ℝ) ^ (-ε))
    (hEI : |(∫ x, O (fun i => fcGamma (edgeV D N A ct w) (1 - Real.exp (-edgeTime N ct)) *
            ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
            (fcEdge (edgeV D N A ct w) (1 - Real.exp (-edgeTime N ct)) -
              eigK (edgeV D N A ct w + ((Real.sqrt (1 - Real.exp (-edgeTime N ct)) : ℝ) : ℂ) •
                gueIdx D N x) ((i : ℕ) + 1))) ∂(gueLaw (D * N))) - EG| ≤ (N : ℝ) ^ (-cE)) :
    |(∫ x, CVtG_F D N A O (gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ))
        (Eplus (lam D N A)) (CVtG_psi D N ct (w, x)) ∂(gueLaw (D * N))) - EG| ≤
      (N : ℝ) ^ (-cE) + K * ((N : ℝ) ^ (-ε) + (D : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-ε)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set tp : ℝ := 1 - Real.exp (-edgeTime N ct) with htp
  set Gp : Coords (D * N) → ℝ := fun x => CVtG_F D N A O
    (gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ)) (Eplus (lam D N A))
    (CVtG_psi D N ct (w, x)) with hGp
  set Gc : Coords (D * N) → ℝ := fun x => CVtG_F D N A O
    (fcGamma (edgeV D N A ct w) tp * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ))
    (fcEdge (edgeV D N A ct w) tp) (CVtG_psi D N ct (w, x)) with hGc
  have hGc' : ∀ x, Gc x = O (fun i => fcGamma (edgeV D N A ct w) tp *
      ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
      (fcEdge (edgeV D N A ct w) tp - eigK (edgeV D N A ct w +
        ((Real.sqrt tp : ℝ) : ℂ) • gueIdx D N x) ((i : ℕ) + 1))) := by
    intro x
    simp only [hGc, CVtG_F, CVtG_psi_eq, htp]
  have hmeas : ∀ a b : ℝ, Measurable fun x : Coords (D * N) =>
      CVtG_F D N A O a b (CVtG_psi D N ct (w, x)) := fun a b =>
    (CVtG_meas_F D N A O hO a b).comp
      ((CVtG_meas_psi D N ct).comp measurable_prodMk_left)
  have hbd : ∀ a b : ℝ, ∀ x : Coords (D * N), ‖CVtG_F D N A O a b (CVtG_psi D N ct (w, x))‖ ≤ B :=
    fun a b x => by rw [Real.norm_eq_abs]; exact hB _
  have hip : Integrable Gp (gueLaw (D * N)) :=
    Integrable.of_bound (hmeas _ _).aestronglyMeasurable B (Eventually.of_forall (hbd _ _))
  have hic : Integrable Gc (gueLaw (D * N)) :=
    Integrable.of_bound (hmeas _ _).aestronglyMeasurable B (Eventually.of_forall (hbd _ _))
  have hpt : ∀ x, ‖Gp x - Gc x‖ ≤
      K * ((N : ℝ) ^ (-ε) + (D : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-ε)) := by
    intro x
    rw [Real.norm_eq_abs, hGc' x]
    simp only [hGp, CVtG_F, CVtG_psi_eq, htp]
    refine hK (((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ)) (gammaPlus (lam D N A))
      (fcGamma (edgeV D N A ct w) tp) (Eplus (lam D N A)) (fcEdge (edgeV D N A ct w) tp)
      ((N : ℝ) ^ (-ε)) ((D : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-ε))
      (fun i => eigK (edgeV D N A ct w + ((Real.sqrt tp : ℝ) : ℂ) • gueIdx D N x)
        ((i : ℕ) + 1)) (by positivity) hγ1 hγ2 (by positivity) hη hG ?_
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg D) (Nat.cast_nonneg N)]
    calc (D : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) *
          |fcEdge (edgeV D N A ct w) tp - Eplus (lam D N A)|
        ≤ (D : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ) - ε) := by
          gcongr
      _ = (D : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-ε) := by
          rw [mul_assoc, ← Real.rpow_add hN0]
          ring_nf
  have h1 : |(∫ x, Gp x ∂(gueLaw (D * N))) - ∫ x, Gc x ∂(gueLaw (D * N))| ≤
      K * ((N : ℝ) ^ (-ε) + (D : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-ε)) := by
    rw [← integral_sub hip hic, ← Real.norm_eq_abs]
    have := norm_integral_le_of_norm_le_const (μ := gueLaw (D * N))
      (f := fun x => Gp x - Gc x) (Eventually.of_forall hpt)
    simpa using this
  have h2 : |(∫ x, Gc x ∂(gueLaw (D * N))) - EG| ≤ (N : ℝ) ^ (-cE) := by
    have : (∫ x, Gc x ∂(gueLaw (D * N))) = ∫ x, O (fun i => fcGamma (edgeV D N A ct w) tp *
      ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
      (fcEdge (edgeV D N A ct w) tp - eigK (edgeV D N A ct w +
        ((Real.sqrt tp : ℝ) : ℂ) • gueIdx D N x) ((i : ℕ) + 1))) ∂(gueLaw (D * N)) :=
      integral_congr_ae (Eventually.of_forall hGc')
    rw [this]
    exact hEI
  calc |(∫ x, Gp x ∂(gueLaw (D * N))) - EG|
      ≤ |(∫ x, Gp x ∂(gueLaw (D * N))) - ∫ x, Gc x ∂(gueLaw (D * N))| +
        |(∫ x, Gc x ∂(gueLaw (D * N))) - EG| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- A positive power of `N` exceeds any fixed bound for large `N`. -/
private lemma CVtG_ev_ge {r : ℝ} (hr : 0 < r) (B : ℝ) : ∀ᶠ N : ℕ in atTop, B ≤ (N : ℝ) ^ r :=
  ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B

/-- Lemma 4.1 [CVtG], under the external input of its proof: for `𝔠 ∈ (0, 1/10)` and
`𝔱 = N^{-1/3+𝔠}`, the `n` largest eigenvalues of `H_Λ(𝔱)`, rescaled by `γ₊ (DN)^{2/3}` at `E⁺`,
have the law of the `n` largest eigenvalues of a `DN × DN` GUE up to `N^{-c}`, uniformly in the
entry laws and in `‖A‖ ≤ N^{-δ_A}`. -/
theorem CVtG (hEI : LandonYauEdge) (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ)
    (ct : ℝ) (hct : 0 < ct) (hct' : ct < 1 / 10) (n : ℕ) (O : (Fin n → ℝ) → ℝ)
    (hO : ContDiff ℝ ∞ O) (hOc : HasCompactSupport O) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : EntryLaws C,
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      |(∫ h, O (fun i => gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
            (Eplus (lam D N A) - eigK (Matrix.of h + lam D N A) ((i : ℕ) + 1)))
            ∂(ouMatLaw D N L (edgeTime N ct))) -
        (∫ x, O (fun i => ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
            (2 - eigK (wig (D * N) x) ((i : ℕ) + 1))) ∂(gueLaw (D * N)))| ≤ (N : ℝ) ^ (-c) := by
  obtain ⟨cV, CV, hcV, hCV, hreg⟩ := CVtG_regular D hD δA hδA C ct hct hct'
  obtain ⟨cE, hcE, N₁, hN₁⟩ :=
    hEI D hD ct hct hct' ct hct (by linarith) cV CV hcV hCV n O hO hOc
  obtain ⟨N₂, hN₂⟩ := hreg 1 one_pos
  obtain ⟨N₃, hN₃⟩ :=
    fc_close D hD δA hδA C ct hct hct' (ct / 2) (by linarith) (by linarith) 1 one_pos
  obtain ⟨K, hK0, hK⟩ := CVtG_repl O hO hOc
  obtain ⟨B, hB'⟩ := hO.continuous.bounded_above_of_compact_support hOc
  have hB : ∀ y, |O y| ≤ B := fun y => by simpa using hB' y
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hε0 : 0 < ct / 2 := by linarith
  set ε : ℝ := ct / 2 with hεdef
  set K' : ℝ := K * (1 + (D : ℝ) ^ (2 / 3 : ℝ)) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  set c : ℝ := min cE ε / 2 with hcdef
  have hc0 : 0 < c := by rw [hcdef]; have := lt_min hcE hε0; linarith
  have h2cE : 2 * c ≤ cE := by rw [hcdef]; linarith [min_le_left cE ε]
  have h2cε : 2 * c ≤ ε := by rw [hcdef]; linarith [min_le_right cE ε]
  have hev : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ 20 ≤ (N : ℝ) ^ δA ∧ 4 ≤ (N : ℝ) ^ ε ∧
      1 + K' + 4 * B ≤ (N : ℝ) ^ c :=
    (eventually_ge_atTop 2).and ((CVtG_ev_ge hδA 20).and
      ((CVtG_ev_ge hε0 4).and (CVtG_ev_ge hc0 _)))
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp hev
  refine ⟨c, hc0, max (max N₁ N₂) (max N₃ N₄), ?_⟩
  intro N hN L A hA
  have hN₁N : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂N : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₃N : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN₄N : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hN2, hNδ, hNε, hNc⟩ := hN₄ N hN₄N
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have : Nonempty (Idx D N) := ⟨((⟨0, by omega⟩ : Fin D), (⟨0, by omega⟩ : Fin N))⟩
  -- the size of `Λ` and `γ₊ ∈ [1/2, 2]`
  have hnegδ : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
    rw [Real.rpow_neg hN0.le, ← one_div,
      one_div_le_one_div (Real.rpow_pos_of_pos hN0 _) (by norm_num)]
    linarith
  have hlam : opNorm (lam D N A) ≤ 1 / 10 := by
    have := opNorm_lam_le D N A
    linarith
  obtain ⟨-, -, hγ1, hγ2, -, -⟩ := def_gamma_limits (lam D N A) (lam_isHermitian D N A) hlam
  have hη : (N : ℝ) ^ (-ε) ≤ 1 / 4 := by
    rw [Real.rpow_neg hN0.le, ← one_div,
      one_div_le_one_div (Real.rpow_pos_of_pos hN0 _) (by norm_num)]
    linarith
  -- the exceptional events
  have hS1 := hN₂ N hN₂N L A hA
  have hS2 := hN₃ N hN₃N L A hA
  set S1 := {w : Fin D → Coords N | ¬ etaRegular N ct cV CV (edgeV D N A ct w)
      (Real.exp (-edgeTime N ct / 2) *
        Eplus (lam D N (((Real.exp (edgeTime N ct / 2) : ℝ) : ℂ) • A)))} with hS1def
  set S2 := {w : Fin D → Coords N | (N : ℝ) ^ (-(2 / 3 : ℝ) - ε) <
      |fcEdge (edgeV D N A ct w) (1 - Real.exp (-edgeTime N ct)) - Eplus (lam D N A)| ∨
    (N : ℝ) ^ (-ε) <
      |fcGamma (edgeV D N A ct w) (1 - Real.exp (-edgeTime N ct)) - gammaPlus (lam D N A)|}
    with hS2def
  obtain ⟨T, hsub, hTm, hTeq⟩ := exists_measurable_superset (blockLaw D N L) (S1 ∪ S2)
  have hapos : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 : ℝ)) := by positivity
  have hPT : (blockLaw D N L).real T ≤ 2 * (N : ℝ) ^ (-(1 : ℝ)) := by
    rw [measureReal_def, hTeq]
    have h := (measure_union_le (μ := blockLaw D N L) S1 S2).trans (add_le_add hS1 hS2)
    calc ((blockLaw D N L) (S1 ∪ S2)).toReal
        ≤ (ENNReal.ofReal ((N : ℝ) ^ (-(1 : ℝ))) + ENNReal.ofReal ((N : ℝ) ^ (-(1 : ℝ)))).toReal :=
          ENNReal.toReal_mono (by simp) h
      _ = 2 * (N : ℝ) ^ (-(1 : ℝ)) := by
          rw [← ENNReal.ofReal_add hapos hapos, ENNReal.toReal_ofReal (by positivity)]
          ring
  -- Fubini
  obtain ⟨hint, heq⟩ := CVtG_fubini D N L A ct O hO.continuous B hB
    (gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ)) (Eplus (lam D N A))
  set EG : ℝ := ∫ x, O (fun i => ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
      (2 - eigK (wig (D * N) x) ((i : ℕ) + 1))) ∂(gueLaw (D * N)) with hEG
  have hEGb : |EG| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := gueLaw (D * N))
      (f := fun x => O (fun i => ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
        (2 - eigK (wig (D * N) x) ((i : ℕ) + 1)))) (C := B)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB _)
    rw [hEG]
    simpa using this
  have hab : ∀ w : Fin D → Coords N, |∫ x, CVtG_F D N A O
      (gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ)) (Eplus (lam D N A))
      (CVtG_psi D N ct (w, x)) ∂(gueLaw (D * N))| ≤ B := by
    intro w
    have := norm_integral_le_of_norm_le_const (μ := gueLaw (D * N))
      (f := fun x => CVtG_F D N A O
        (gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ)) (Eplus (lam D N A))
        (CVtG_psi D N ct (w, x))) (C := B)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB _)
    simpa using this
  change |(∫ h, CVtG_F D N A O (gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ))
      (Eplus (lam D N A)) h ∂(ouMatLaw D N L (edgeTime N ct))) - EG| ≤ (N : ℝ) ^ (-c)
  rw [heq]
  have hmain := CVtG_outer (blockLaw D N L) _ hint EG ((N : ℝ) ^ (-cE) + K' * (N : ℝ) ^ (-ε))
    (2 * B) T hTm ?_ ?_ (by positivity)
  · -- the numerics
    have e1 : (N : ℝ) ^ (-cE) ≤ (N : ℝ) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have e2 : (N : ℝ) ^ (-ε) ≤ (N : ℝ) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have e3 : (N : ℝ) ^ (-(1 : ℝ)) ≤ (N : ℝ) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith [show ε < 1 by linarith])
    have hq : (N : ℝ) ^ (-(2 * c)) = (N : ℝ) ^ (-c) * (N : ℝ) ^ (-c) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hu : (1 + K' + 4 * B) * (N : ℝ) ^ (-c) ≤ 1 := by
      rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hN0 c)]
      exact hNc
    have hqpos : 0 ≤ (N : ℝ) ^ (-c) := by positivity
    calc _ ≤ (N : ℝ) ^ (-cE) + K' * (N : ℝ) ^ (-ε) + 2 * B * (2 * (N : ℝ) ^ (-(1 : ℝ))) :=
          hmain.trans (by gcongr)
      _ ≤ (N : ℝ) ^ (-(2 * c)) + K' * (N : ℝ) ^ (-(2 * c)) +
            2 * B * (2 * (N : ℝ) ^ (-(2 * c))) := by gcongr
      _ = (N : ℝ) ^ (-c) * ((1 + K' + 4 * B) * (N : ℝ) ^ (-c)) := by rw [hq]; ring
      _ ≤ (N : ℝ) ^ (-c) * 1 := mul_le_mul_of_nonneg_left hu hqpos
      _ = (N : ℝ) ^ (-c) := mul_one _
  · -- on the good event
    intro w hw
    have hw1 : w ∉ S1 := fun h => hw (hsub (Or.inl h))
    have hw2 : w ∉ S2 := fun h => hw (hsub (Or.inr h))
    have hreg' : etaRegular N ct cV CV (edgeV D N A ct w) (Real.exp (-edgeTime N ct / 2) *
        Eplus (lam D N (((Real.exp (edgeTime N ct / 2) : ℝ) : ℂ) • A))) := by
      by_contra h
      exact hw1 h
    have hw2' : ¬ ((N : ℝ) ^ (-(2 / 3 : ℝ) - ε) <
      |fcEdge (edgeV D N A ct w) (1 - Real.exp (-edgeTime N ct)) - Eplus (lam D N A)| ∨
    (N : ℝ) ^ (-ε) <
      |fcGamma (edgeV D N A ct w) (1 - Real.exp (-edgeTime N ct)) - gammaPlus (lam D N A)|) := hw2
    rw [not_or, not_lt, not_lt] at hw2'
    have hE := hN₁ N hN₁N (edgeV D N A ct w) (CVtG_edgeV_herm D N A ct w) _ hreg'
    have := CVtG_inner D N A ct ε cE EG O hO.continuous B hB K hK hγ1 hγ2 hη hN1 w hw2'.1 hw2'.2 hE
    calc _ ≤ _ := this
      _ = _ := by rw [hK']; ring
  · intro w
    have := hab w
    have := hEGb
    rw [abs_le] at *
    constructor <;> linarith

/-- A smooth compactly supported function on `Fin n → ℝ` with value `1` at the origin. -/
private lemma CVtG_bump (n : ℕ) :
    ∃ O : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ O ∧ HasCompactSupport O ∧ O 0 = 1 := by
  let f : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨f, f.contDiff, f.hasCompactSupport, f.one_of_mem_closedBall (by simp [f])⟩

/-- A coupling for `D = 3`: `A = N^{-1/10} I_N`, with `‖A‖ ≤ N^{-1/100}` by
`admissible_delocalized`. -/
private def CVtG_A (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  ((((N : ℝ) ^ (-(1 / 10 : ℝ)) : ℝ) : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ)

/-- `A = N^{-1/10} I_N` is not zero for `N ≥ 1`. -/
private lemma CVtG_A_ne (N : ℕ) (hN : 1 ≤ N) : CVtG_A N ≠ 0 := by
  intro h
  have h0 := congrFun (congrFun h ⟨0, hN⟩) ⟨0, hN⟩
  simp [CVtG_A] at h0
  omega

/-- `CVtG` at the nondegenerate point `D = 3`, `δ_A = 1/100`, `𝔠 = 1/20`, `n = 1`, `C p = 2`, a
bump `O` with `O 0 = 1`, and `A = N^{-1/10} I_N` (nonzero, with `‖A‖ ≤ N^{-1/100}`), as a function
of the external input `hEI` (which has no instance), for every `N ≥ N₀`: for some entry laws (which
exist since `entryLaws_nonempty`) the two expectations of (4.2) [ls_CVtG] differ by at most
`N^{-c}`. -/
example (hEI : LandonYauEdge) :
    ∃ O : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ O ∧ HasCompactSupport O ∧ O 0 = 1 ∧
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        ∃ L : EntryLaws (fun _ => (2 : ℝ)), CVtG_A N ≠ 0 ∧
          opNorm (CVtG_A N) ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
          |(∫ h, O (fun i => gammaPlus (lam 3 N (CVtG_A N)) * ((3 * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
                (Eplus (lam 3 N (CVtG_A N)) -
                  eigK (Matrix.of h + lam 3 N (CVtG_A N)) ((i : ℕ) + 1)))
                ∂(ouMatLaw 3 N L (edgeTime N (1 / 20)))) -
            (∫ x, O (fun i => ((3 * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
                (2 - eigK (wig (3 * N) x) ((i : ℕ) + 1))) ∂(gueLaw (3 * N)))| ≤
            (N : ℝ) ^ (-c) := by
  obtain ⟨L⟩ := entryLaws_nonempty
  obtain ⟨O, hO, hOc, hO0⟩ := CVtG_bump 1
  obtain ⟨c, hc, N₀, h⟩ := CVtG hEI 3 (by norm_num) (1 / 100) (by norm_num)
    (fun _ => (2 : ℝ)) (1 / 20) (by norm_num) (by norm_num) 1 O hO hOc
  exact ⟨O, hO, hOc, hO0, c, hc, N₀, fun N hN hN1 => ⟨L, CVtG_A_ne N hN1,
    (admissible_delocalized N hN1).1, h N hN L _ (admissible_delocalized N hN1).1⟩⟩

/-- The limit check of `LandonYauEdge` (`V = e^{-𝔱/2} W₀`, `W₀` a GUE independent of `W`):
`e^{-𝔱/2} W₀ + √(1 - e^{-𝔱}) W` is again a GUE, here of size `DN = 6` at `𝔱 = 1/10`. -/
example : ((gueLaw 6).prod (gueLaw 6)).map (fun p => Real.exp (-(1 / 10 : ℝ) / 2) • p.1 +
    Real.sqrt (1 - Real.exp (-(1 / 10 : ℝ))) • p.2) = gueLaw 6 := by
  apply gueLaw_map_add
  have h0 : 0 ≤ 1 - Real.exp (-(1 / 10 : ℝ)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  rw [Real.sq_sqrt h0, sq, ← Real.exp_add]
  ring_nf

end RBMTransitionEdge

end
