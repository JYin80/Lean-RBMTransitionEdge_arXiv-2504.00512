module

public import RBMTransitionEdge.Edge.Smoothing

@[expose] public section

/-!
# The joint sandwich of the edge eigenvalues and Lemma 4.2 from Lemma 4.3

A smooth step `K_k`, the sandwich of `P(λ_k < E_k for all k ≤ n)` between expectations of products
of `K_k` at edge counts (the joint form of (17.6) of [Erds2017ADA, Corollary 17.3]), and the
reduction of Lemma 4.2 [CVtV] to Lemma 4.3 [rescomY] for the `n` largest eigenvalues, uniform in
the scale `γ ∈ [1/2, 2]`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The smooth step `K_k`, equal to `1` on `(-∞, k - 8/9]` and to `0` on `[k - 7/9, ∞)`
(proof of Lemma 4.2 [CVtV], after [Erds2017ADA, Corollary 17.3]). -/
def stepK (k : ℕ) (x : ℝ) : ℝ := cutoffFn (1 + 9 * (x - ((k : ℝ) - 8 / 9)))

/-- `K_k` is smooth, takes values in `[0, 1]`, is `1` on `(-∞, k - 8/9]` and `0` on
`[k - 7/9, ∞)`. -/
theorem stepK_spec (k : ℕ) :
    ContDiff ℝ ∞ (stepK k) ∧ (∀ x, stepK k x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, x ≤ (k : ℝ) - 8 / 9 → stepK k x = 1) ∧
      (∀ x, (k : ℝ) - 7 / 9 ≤ x → stepK k x = 0) := by
  refine ⟨?_, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · unfold stepK cutoffFn
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · unfold stepK cutoffFn
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · unfold stepK cutoffFn
    exact Real.smoothTransition.one_of_one_le (by linarith)
  · unfold stepK cutoffFn
    exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-! ### Helpers: the functions `F`, measurability, the layer-cake bridge -/

/-- A smooth function with values in `[0, 1]`, equal to `1` on `(-∞, a]` and to `0` on `[b, ∞)`,
has bounded iterated derivatives of every order. -/
private lemma Sandwich_step_bdd (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (a b : ℝ)
    (h1 : ∀ y, y ≤ a → g y = 1) (h0 : ∀ y, b ≤ y → g y = 0)
    (hb : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1) (i : ℕ) :
    ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ B := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨1, fun y => ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (hb y).1]
    exact (hb y).2
  have hcont : Continuous fun y => ‖iteratedFDeriv ℝ i g y‖ :=
    (hg.continuous_iteratedFDeriv (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)).norm
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max B 0, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc a b
  · exact le_trans (by simpa using hB y hy) (le_max_left _ _)
  · have hz : iteratedFDeriv ℝ i g y = 0 := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
      have key : ∀ c : ℝ, g =ᶠ[𝓝 y] (fun _ => c) → g y = c → iteratedFDeriv ℝ i g y = 0 := by
        intro c hev hc
        rw [← iteratedFDerivWithin_univ]
        have hev' : g =ᶠ[𝓝[Set.univ] y] (fun _ => c) := by rw [nhdsWithin_univ]; exact hev
        rw [hev'.iteratedFDerivWithin_eq hc i, iteratedFDerivWithin_univ,
          iteratedFDeriv_const_of_ne hi.ne']
        rfl
      rcases hy with hy | hy
      · exact key 1 (by filter_upwards [Iio_mem_nhds hy] with z hz using h1 z hz.le) (h1 y hy.le)
      · exact key 0 (by filter_upwards [Ioi_mem_nhds hy] with z hz using h0 z hz.le) (h0 y hy.le)
    rw [hz, norm_zero]
    exact le_max_right _ _

/-- The function `x ↦ Π_k K_k(x_k/π)` on `ℝ^n` of the proof of Lemma 4.2. -/
private def Sandwich_F (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∏ k : Fin n, stepK ((k : ℕ) + 1) (x k / Real.pi)

/-- The factor `y ↦ K_m(y/π)` is smooth. -/
private lemma Sandwich_g_contDiff (m : ℕ) :
    ContDiff ℝ ∞ (fun y : ℝ => stepK m (y / Real.pi)) :=
  (stepK_spec m).1.comp (contDiff_id.div_const _)

/-- `F` is smooth. -/
private lemma Sandwich_F_contDiff (n : ℕ) : ContDiff ℝ ∞ (Sandwich_F n) := by
  unfold Sandwich_F
  exact contDiff_prod fun k _ =>
    (Sandwich_g_contDiff _).comp (by fun_prop : ContDiff ℝ ∞ fun x : Fin n → ℝ => x k)

/-- Every iterated derivative of `F` is bounded on `ℝ^n`: `F` is a product of smooth functions of
separate coordinates, each with bounded derivatives. -/
private lemma Sandwich_F_deriv_bdd (n j : ℕ) :
    ∃ B : ℝ, ∀ x : Fin n → ℝ, ‖iteratedFDeriv ℝ j (Sandwich_F n) x‖ ≤ B := by
  set f : Fin n → (Fin n → ℝ) → ℝ := fun k x => stepK ((k : ℕ) + 1) (x k / Real.pi) with hf
  have hfd : ∀ k, ContDiff ℝ ∞ (f k) := fun k =>
    (Sandwich_g_contDiff _).comp (by fun_prop : ContDiff ℝ ∞ fun x : Fin n → ℝ => x k)
  have hfb : ∀ (k : Fin n) (i : ℕ), ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ i (f k) x‖ ≤ B := by
    intro k i
    obtain ⟨B, hB⟩ := Sandwich_step_bdd (fun y => stepK ((k : ℕ) + 1) (y / Real.pi))
      (Sandwich_g_contDiff _) (Real.pi * (((k : ℕ) + 1 : ℝ) - 8 / 9))
      (Real.pi * (((k : ℕ) + 1 : ℝ) - 7 / 9))
      (fun y hy => (stepK_spec _).2.2.1 _ (by
        rw [div_le_iff₀ Real.pi_pos]; push_cast; linarith))
      (fun y hy => (stepK_spec _).2.2.2 _ (by
        rw [le_div_iff₀ Real.pi_pos]; push_cast; linarith))
      (fun y => (stepK_spec _).2.1 _) i
    refine ⟨B * ‖(ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)‖ ^ i, fun x => ?_⟩
    have hcomp : f k = (fun y : ℝ => stepK ((k : ℕ) + 1) (y / Real.pi)) ∘
        (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ) := rfl
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ (Sandwich_g_contDiff _) _
      (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (hB _) (by positivity)
  choose Bd hBd using hfb
  refine ⟨∑ p ∈ (Finset.univ : Finset (Fin n)).sym j, ((p : Multiset (Fin n)).countPerms : ℝ) *
    ∏ k, Bd k ((p : Multiset (Fin n)).count k), fun x => ?_⟩
  have := norm_iteratedFDeriv_prod_le (𝕜 := ℝ) (u := Finset.univ) (f := f)
    (fun k _ => hfd k) (x := x) (n := j) (N := ∞) (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)
  refine this.trans (Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => hBd _ _ _) (Nat.cast_nonneg _))

/-- `F` satisfies (4.6) with a constant `CF` depending on `n` only. -/
private lemma Sandwich_F_CF (n : ℕ) : ∃ CF : ℕ → ℝ,
    ∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k (Sandwich_F n) x‖ ≤
      CF l * (1 + ‖x‖) ^ CF l := by
  choose B hB using Sandwich_F_deriv_bdd n
  refine ⟨fun l => 1 + ∑ k ∈ Finset.range (l + 1), |B k|, fun l k _ hkl x => ?_⟩
  set S := ∑ k ∈ Finset.range (l + 1), |B k| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : B k ≤ S := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun k => |B k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hkl)))
  have h2 : (1 : ℝ) ≤ (1 + ‖x‖) ^ (1 + S) :=
    Real.one_le_rpow (by linarith [norm_nonneg x]) (by linarith)
  calc ‖iteratedFDeriv ℝ k (Sandwich_F n) x‖ ≤ B k := hB k x
    _ ≤ (1 + S) * 1 := by linarith
    _ ≤ (1 + S) * (1 + ‖x‖) ^ (1 + S) := mul_le_mul_of_nonneg_left h2 (by linarith)


/-! ### Measurability of the eigenvalues -/

/-- The map `h ↦ ‖h - B‖` from arrays to the operator norm is continuous. -/
private lemma Sandwich_cont_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) :
    Continuous fun h : ι → ι → ℂ => opNorm (Matrix.of h - B) := by
  have h1 : Continuous fun h : ι → ι → ℂ => (Matrix.of h - B : Matrix ι ι ℂ) := by
    fun_prop
  have h2 : Continuous fun X : Matrix ι ι ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) X :=
    LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).toAlgEquiv.toLinearMap
  exact continuous_norm.comp (h2.comp h1)

/-- The `k`-th largest eigenvalue is a measurable function of the array of entries: it is `0` off
the closed set of Hermitian arrays and `1`-Lipschitz on it (Weyl's inequality). -/
private lemma Sandwich_meas_eigK {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
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
      have := ((Sandwich_cont_opNorm (Matrix.of h₀)).tendsto h₀).mono_left
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
private lemma Sandwich_meas_eigK_add {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (k : ℕ) : Measurable fun h : ι → ι → ℂ => eigK (Matrix.of h + B) k := by
  have h1 : Measurable fun h : ι → ι → ℂ => h + Matrix.of.symm B := by fun_prop
  have h2 := (Sandwich_meas_eigK (ι := ι) k).comp h1
  convert h2 using 2 with h
  simp only [Function.comp_apply]
  congr 1


/-! ### The joint sandwich -/

/-- The eigenvalues are antitone in the index on `⟦1, card ι⟧`. -/
private lemma Sandwich_eigK_anti {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ Fintype.card ι) :
    eigK X j ≤ eigK X i := by
  have h1 : j - 1 < Fintype.card ι := by omega
  have h0 : i - 1 < Fintype.card ι := by omega
  simp only [eigK, eigs, hX, h1, h0, dite_true]
  exact hX.eigenvalues₀_antitone (by simp [Fin.le_def]; omega)

/-- `λ_{k+1} < E` iff at most `k` eigenvalues are `≥ E`, for `E > 0`. -/
private lemma Sandwich_event_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (E : ℝ) (hE : 0 < E) (k : ℕ) : eigK X (k + 1) < E ↔ eigCountAbove X E ≤ k := by
  by_cases hX : X.IsHermitian
  · unfold eigCountAbove
    constructor
    · intro h
      have hsub : (Finset.Icc 1 (Fintype.card ι)).filter (fun j => E ≤ eigK X j) ⊆
          Finset.Icc 1 k := by
        intro j hj
        rw [Finset.mem_filter, Finset.mem_Icc] at hj
        rw [Finset.mem_Icc]
        refine ⟨hj.1.1, ?_⟩
        by_contra hjk
        have := Sandwich_eigK_anti hX (i := k + 1) (j := j) (by omega) (by omega) hj.1.2
        linarith [hj.2]
      simpa using Finset.card_le_card hsub
    · intro h
      by_contra hlt
      rw [not_lt] at hlt
      by_cases hk : k + 1 ≤ Fintype.card ι
      · have hsub : Finset.Icc 1 (k + 1) ⊆
            (Finset.Icc 1 (Fintype.card ι)).filter (fun j => E ≤ eigK X j) := by
          intro j hj
          rw [Finset.mem_Icc] at hj
          rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hj.1, by omega⟩,
            hlt.trans (Sandwich_eigK_anti hX hj.1 hj.2 hk)⟩
        have := Finset.card_le_card hsub
        simp at this
        omega
      · have h0 : eigK X (k + 1) = 0 := by
          have : ¬ (k + 1 - 1 < Fintype.card ι) := by omega
          simp only [eigK, this, dite_false]
        linarith
  · have h0 : ∀ j, eigK X j = 0 := fun j => by simp [eigK, eigs, hX]
    simp only [h0, hE, true_iff]
    unfold eigCountAbove
    rw [Finset.card_eq_zero.mpr]
    · exact Nat.zero_le _
    · rw [Finset.filter_eq_empty_iff]
      intro j _
      simp [h0, hE]


/-- `N^{-a} ≤ c` for large `N`. -/
private lemma Sandwich_ev_small (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) ^ (-a) ≤ c := by
  have h := (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.mp (h.eventually (ge_mem_nhds hc))

/-- `c ≤ N^a` for large `N`. -/
private lemma Sandwich_ev_large (a c : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c ≤ (N : ℝ) ^ a := by
  have h := (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.mp (h.eventually_ge_atTop c)

/-- The smoothed edge count `A(E₁, E₊)/π`, `η = N^{-2/3-9ε'}`, `E₊ = E⁺ + N^{-2/3+ε'}`. -/
private def Sandwich_cnt (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (ε' E₁ : ℝ)
    (h : Idx D N → Idx D N → ℂ) : ℝ :=
  edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε')) E₁
    (Eplus (lam D N A) + (N : ℝ) ^ (-(2 / 3 : ℝ) + ε')) h / Real.pi

/-- `Π_k K_k(A(E₁(k), E₊)/π)`. -/
private def Sandwich_PF (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (ε' : ℝ) (n : ℕ)
    (E₁ : Fin n → ℝ) (h : Idx D N → Idx D N → ℂ) : ℝ :=
  ∏ k : Fin n, stepK ((k : ℕ) + 1) (Sandwich_cnt D N A ε' (E₁ k) h)

/-- The event `{λ_k < E_k for all k}`. -/
private def Sandwich_ev (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (n : ℕ) (E : Fin n → ℝ) :
    Set (Idx D N → Idx D N → ℂ) :=
  {h | ∀ k : Fin n, eigK (Matrix.of h + lam D N A) ((k : ℕ) + 1) < E k}

/-- The event `{λ_k < E_k for all k}` is measurable. -/
private lemma Sandwich_ev_meas (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (n : ℕ)
    (E : Fin n → ℝ) : MeasurableSet (Sandwich_ev D N A n E) := by
  have : Sandwich_ev D N A n E = ⋂ k : Fin n,
      {h | eigK (Matrix.of h + lam D N A) ((k : ℕ) + 1) < E k} := by
    ext h
    simp [Sandwich_ev]
  rw [this]
  exact MeasurableSet.iInter fun k =>
    measurableSet_lt (Sandwich_meas_eigK_add _ _) measurable_const

/-- The smoothed edge count is almost surely measurable, for a law carried by Hermitian arrays
(it is then a sum of arctangents of eigenvalues). -/
private lemma Sandwich_cnt_aemeas (D N : ℕ) (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ)
    (ε' E₁ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) :
    AEMeasurable (Sandwich_cnt D N A ε' E₁) μ := by
  have hη : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε') := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have hm : Measurable fun h : Idx D N → Idx D N → ℂ =>
      (∑ k ∈ Finset.Icc 1 (D * N),
        (Real.arctan ((Eplus (lam D N A) + (N : ℝ) ^ (-(2 / 3 : ℝ) + ε') -
            eigK (Matrix.of h + lam D N A) k) / (N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε')) -
          Real.arctan ((E₁ - eigK (Matrix.of h + lam D N A) k) /
            (N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε')))) / Real.pi := by
    refine Measurable.div_const (Finset.measurable_sum _ fun k _ => ?_) _
    exact (Real.continuous_arctan.measurable.comp
      ((measurable_const.sub (Sandwich_meas_eigK_add _ k)).div_const _)).sub
      (Real.continuous_arctan.measurable.comp
      ((measurable_const.sub (Sandwich_meas_eigK_add _ k)).div_const _))
  refine hm.aemeasurable.congr (hμ.mono fun h hh => ?_)
  simp only [Sandwich_cnt, edgeCount_eq_arctan D N A _ _ _ hη h hh]

/-- `Π_k K_k(A(E₁(k), E₊)/π)` is almost surely measurable. -/
private lemma Sandwich_PF_aesm (D N : ℕ) (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ)
    (ε' : ℝ) (n : ℕ) (E₁ : Fin n → ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) :
    AEStronglyMeasurable (Sandwich_PF D N A ε' n E₁) μ := by
  unfold Sandwich_PF
  refine AEMeasurable.aestronglyMeasurable ?_
  refine Finset.aemeasurable_fun_prod _ fun k _ => ?_
  exact (stepK_spec _).1.continuous.measurable.comp_aemeasurable
    (Sandwich_cnt_aemeas D N hN A ε' _ μ hμ)

/-- `Π_k K_k(A(E₁(k), E₊)/π)` takes values in `[0, 1]`. -/
private lemma Sandwich_PF_mem (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (ε' : ℝ) (n : ℕ) (E₁ : Fin n → ℝ) (h : Idx D N → Idx D N → ℂ) :
    Sandwich_PF D N A ε' n E₁ h ∈ Set.Icc (0 : ℝ) 1 := by
  unfold Sandwich_PF
  exact ⟨Finset.prod_nonneg fun k _ => ((stepK_spec _).2.1 _).1,
    Finset.prod_le_one₀ (fun k _ => ((stepK_spec _).2.1 _).1) fun k _ => ((stepK_spec _).2.1 _).2⟩


/-- If `N_k ≤ k` and `b_k - u ≤ N_k` for all `k`, with `u ≤ 1/9`, every factor `K_{k+1}(b_k)`
is `1`. -/
private lemma Sandwich_prod_one (n : ℕ) (b : Fin n → ℝ) (Nk : Fin n → ℕ) (u : ℝ)
    (hu : u ≤ 1 / 9) (hN : ∀ k : Fin n, Nk k ≤ (k : ℕ)) (hb : ∀ k, b k - u ≤ Nk k) :
    ∏ k : Fin n, stepK ((k : ℕ) + 1) (b k) = 1 := by
  refine Finset.prod_eq_one fun k _ => (stepK_spec _).2.2.1 _ ?_
  have h2 : (Nk k : ℝ) ≤ k := by exact_mod_cast hN k
  push_cast
  linarith [hb k]

/-- If `k₀ + 1 ≤ N_{k₀}` and `N_k ≤ a_k + u` for all `k`, with `u ≤ 1/9`, the factor
`K_{k₀+1}(a_{k₀})` vanishes, so the product is `0`. -/
private lemma Sandwich_prod_zero (n : ℕ) (a : Fin n → ℝ) (Nk : Fin n → ℕ) (u : ℝ)
    (hu : u ≤ 1 / 9) (k₀ : Fin n) (hN : (k₀ : ℕ) + 1 ≤ Nk k₀)
    (ha : ∀ k, (Nk k : ℝ) ≤ a k + u) :
    ∏ k : Fin n, stepK ((k : ℕ) + 1) (a k) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ k₀) ((stepK_spec _).2.2.2 _ ?_)
  have h2 : ((k₀ : ℕ) : ℝ) + 1 ≤ Nk k₀ := by exact_mod_cast hN
  push_cast
  linarith [ha k₀]

/-- `P(Ev) ≤ E f + P(B)` when `f ∈ [0, 1]` equals `1` on `Ev` off `B`. -/
private lemma Sandwich_upper_aux {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Ev B : Set Ω) (hEv : MeasurableSet Ev) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (h01 : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ z, z ∉ B → z ∈ Ev → f z = 1) :
    (μ Ev).toReal ≤ (∫ z, f z ∂μ) + (μ B).toReal := by
  have hint : Integrable f μ := Integrable.of_bound hf 1 (ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h01 z).1]; exact (h01 z).2)
  set B' := toMeasurable μ B with hB'def
  have hB' : MeasurableSet B' := measurableSet_toMeasurable μ B
  have hμB' : μ B' = μ B := measure_toMeasurable B
  have hsub : B ⊆ B' := subset_toMeasurable μ B
  have key : ∀ z, Ev.indicator (fun _ => (1 : ℝ)) z ≤ f z + B'.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    have h0 := (h01 z).1
    by_cases hzB : z ∈ B'
    · by_cases hzE : z ∈ Ev <;> simp [Set.indicator, hzB, hzE] <;> linarith
    · by_cases hzE : z ∈ Ev
      · have := hB z (fun h => hzB (hsub h)) hzE
        simp [Set.indicator, hzB, hzE, this]
      · simp [Set.indicator, hzB, hzE, h0]
  have hI1 : ∫ z, Ev.indicator (fun _ => (1 : ℝ)) z ∂μ = (μ Ev).toReal := by
    rw [integral_indicator_const _ hEv]; simp [Measure.real]
  have hI2 : ∫ z, B'.indicator (fun _ => (1 : ℝ)) z ∂μ = (μ B).toReal := by
    rw [integral_indicator_const _ hB']; simp [Measure.real, hμB']
  have hi1 : Integrable (Ev.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hEv
  have hi2 : Integrable (B'.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hB'
  calc (μ Ev).toReal = ∫ z, Ev.indicator (fun _ => (1 : ℝ)) z ∂μ := hI1.symm
    _ ≤ ∫ z, (f z + B'.indicator (fun _ => (1 : ℝ)) z) ∂μ := integral_mono hi1 (hint.add hi2) key
    _ = _ := by rw [integral_add hint hi2, hI2]

/-- `E f ≤ P(Ev) + P(B)` when `f ∈ [0, 1]` vanishes off `Ev` off `B`. -/
private lemma Sandwich_lower_aux {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Ev B : Set Ω) (hEv : MeasurableSet Ev) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (h01 : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ z, z ∉ B → z ∉ Ev → f z = 0) :
    (∫ z, f z ∂μ) ≤ (μ Ev).toReal + (μ B).toReal := by
  have hint : Integrable f μ := Integrable.of_bound hf 1 (ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h01 z).1]; exact (h01 z).2)
  set B' := toMeasurable μ B with hB'def
  have hB' : MeasurableSet B' := measurableSet_toMeasurable μ B
  have hμB' : μ B' = μ B := measure_toMeasurable B
  have hsub : B ⊆ B' := subset_toMeasurable μ B
  have key : ∀ z, f z ≤ Ev.indicator (fun _ => (1 : ℝ)) z + B'.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    have h1 := (h01 z).2
    by_cases hzB : z ∈ B'
    · by_cases hzE : z ∈ Ev <;> simp [Set.indicator, hzB, hzE] <;> linarith
    · by_cases hzE : z ∈ Ev
      · simp [Set.indicator, hzB, hzE, h1]
      · have := hB z (fun h => hzB (hsub h)) hzE
        simp [Set.indicator, hzB, hzE, this]
  have hI1 : ∫ z, Ev.indicator (fun _ => (1 : ℝ)) z ∂μ = (μ Ev).toReal := by
    rw [integral_indicator_const _ hEv]; simp [Measure.real]
  have hI2 : ∫ z, B'.indicator (fun _ => (1 : ℝ)) z ∂μ = (μ B).toReal := by
    rw [integral_indicator_const _ hB']; simp [Measure.real, hμB']
  have hi1 : Integrable (Ev.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hEv
  have hi2 : Integrable (B'.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hB'
  calc ∫ z, f z ∂μ ≤ ∫ z, (Ev.indicator (fun _ => (1 : ℝ)) z +
        B'.indicator (fun _ => (1 : ℝ)) z) ∂μ := integral_mono hint (hi1.add hi2) key
    _ = _ := by rw [integral_add hi1 hi2, hI1, hI2]

/-- Union bound for `n` bad events. -/
private lemma Sandwich_union_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ)
    (Bk : Fin n → Set Ω) (x : ℝ) (hx : 0 ≤ x) (h : ∀ k, μ (Bk k) ≤ ENNReal.ofReal x) :
    (μ (⋃ k, Bk k)).toReal ≤ n * x := by
  have h1 : μ (⋃ k, Bk k) ≤ ENNReal.ofReal (n * x) := by
    calc μ (⋃ k, Bk k) ≤ ∑ k, μ (Bk k) := measure_iUnion_fintype_le μ Bk
      _ ≤ ∑ _k : Fin n, ENNReal.ofReal x := Finset.sum_le_sum fun k _ => h k
      _ = ENNReal.ofReal (n * x) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h1


/-! ### The pointwise comparison of survival functions -/

/-- The four-term estimate behind the pointwise comparison: for the smooth counts of the two laws,
`|S₁ E - S₀ E| ≤ (S₀ (E + 2ℓ) - S₀ (E - 2ℓ)) + (r + 2e)`. -/
private lemma Sandwich_abstract {n : ℕ} (a0 a1 S0 S1 : (Fin n → ℝ) → ℝ)
    (win win' : (Fin n → ℝ) → Prop) (ℓ e r : ℝ)
    (H0 : ∀ E, win E → a0 (fun k => E k - ℓ) - e ≤ S0 E ∧ S0 E ≤ a0 (fun k => E k + ℓ) + e)
    (H1 : ∀ E, win E → a1 (fun k => E k - ℓ) - e ≤ S1 E ∧ S1 E ≤ a1 (fun k => E k + ℓ) + e)
    (HR : ∀ E₁, win' E₁ → |a0 E₁ - a1 E₁| ≤ r)
    (E : Fin n → ℝ) (h1 : win E) (h2 : win (fun k => E k + 2 * ℓ))
    (h3 : win (fun k => E k - 2 * ℓ)) (h4 : win' (fun k => E k + ℓ))
    (h5 : win' (fun k => E k - ℓ))
    (m1 : S0 E ≤ S0 (fun k => E k + 2 * ℓ)) (m2 : S0 (fun k => E k - 2 * ℓ) ≤ S0 E) :
    |S1 E - S0 E| ≤ (S0 (fun k => E k + 2 * ℓ) - S0 (fun k => E k - 2 * ℓ)) + (r + 2 * e) := by
  have e1 : (fun k => (E k + 2 * ℓ) - ℓ) = fun k => E k + ℓ := by funext k; ring
  have e2 : (fun k => (E k - 2 * ℓ) + ℓ) = fun k => E k - ℓ := by funext k; ring
  have u1 := (H1 E h1).2
  have u2 := (abs_le.mp (HR _ h4)).1
  have u3 := (H0 _ h2).1
  rw [e1] at u3
  have l1 := (H1 E h1).1
  have l2 := (abs_le.mp (HR _ h5)).2
  have l3 := (H0 _ h3).2
  rw [e2] at l3
  rw [abs_le]
  constructor <;> linarith

/-- The vector of rescaled gaps `x_i = γ (DN)^{2/3} (E⁺ - λ_{i+1})` of Lemma 4.2 [CVtV]. -/
private def Sandwich_x (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (n : ℕ) (γ : ℝ)
    (h : Idx D N → Idx D N → ℂ) : Fin n → ℝ := fun i =>
  γ * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
    (Eplus (lam D N A) - eigK (Matrix.of h + lam D N A) ((i : ℕ) + 1))

/-- The vector of rescaled gaps is measurable in the array. -/
private lemma Sandwich_x_meas (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (n : ℕ) (γ : ℝ) :
    Measurable (Sandwich_x D N A n γ) := by
  refine measurable_pi_iff.mpr fun i => ?_
  exact measurable_const.mul (measurable_const.sub (Sandwich_meas_eigK_add _ _))

/-- `{x > s}` is the event `{λ_{k+1} < E⁺ - s_k / (γ (DN)^{2/3})}`. -/
private lemma Sandwich_survSet (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (n : ℕ) (c γ : ℝ)
    (hc : c = γ * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ)) (hc0 : 0 < c) (s : Fin n → ℝ) :
    {h : Idx D N → Idx D N → ℂ | ∀ k, s k < Sandwich_x D N A n γ h k} =
      Sandwich_ev D N A n (fun k => Eplus (lam D N A) - s k / c) := by
  ext h
  simp only [Set.mem_ofPred_eq, Sandwich_ev, Sandwich_x, ← hc]
  refine forall_congr' fun k => ?_
  rw [← sub_pos, ← sub_pos (a := Eplus (lam D N A) - s k / c)]
  have : c * (Eplus (lam D N A) - eigK (Matrix.of h + lam D N A) ((k : ℕ) + 1)) - s k =
      c * ((Eplus (lam D N A) - s k / c) - eigK (Matrix.of h + lam D N A) ((k : ℕ) + 1)) := by
    field_simp
    ring
  rw [this]
  exact mul_pos_iff_of_pos_left hc0


/-- `a^n - b^n ≤ n a^n (a - b)` for `1 ≤ a`, `0 ≤ b ≤ a`. -/
private lemma Sandwich_pow_sub_pow (a b : ℝ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a) :
    ∀ n : ℕ, a ^ n - b ^ n ≤ n * a ^ n * (a - b)
  | 0 => by simp
  | n + 1 => by
    have ih := Sandwich_pow_sub_pow a b ha hb hab n
    have ha0 : 0 ≤ a := by linarith
    have h1 : b ^ n ≤ a ^ n := pow_le_pow_left₀ hb hab n
    have h2 : a ^ n ≤ a ^ (n + 1) := pow_le_pow_right₀ ha (Nat.le_succ n)
    have h3 : 0 ≤ a - b := by linarith
    have h4 : a * (a ^ n - b ^ n) ≤ a * (n * a ^ n * (a - b)) :=
      mul_le_mul_of_nonneg_left ih ha0
    have h5 : b ^ n * (a - b) ≤ a ^ n * (a - b) := mul_le_mul_of_nonneg_right h1 h3
    have h6 : a ^ n * (a - b) ≤ a ^ (n + 1) * (a - b) := mul_le_mul_of_nonneg_right h2 h3
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
    have e2 : a * (n * a ^ n * (a - b)) = n * a ^ (n + 1) * (a - b) := by ring
    push_cast
    nlinarith

/-- The shift error: for a measurable `P` with values in `[0, 1]` and `0 ≤ c ≤ R`,
`∫_{[-R, R]^n} (P(s - c) - P(s + c)) ds ≤ (2R)^n - (2R - 2c)^n`. -/
private lemma Sandwich_shift (n : ℕ) (P : (Fin n → ℝ) → ℝ) (hP : Measurable P)
    (hP01 : ∀ s, 0 ≤ P s ∧ P s ≤ 1) (R c : ℝ) (hc0 : 0 ≤ c) (hcR : c ≤ R) :
    ∫ s in Set.Icc (fun _ : Fin n => -R) (fun _ => R),
        (P (s - fun _ => c) - P (s + fun _ => c)) ≤ (2 * R) ^ n - (2 * R - 2 * c) ^ n := by
  set cv : Fin n → ℝ := fun _ => c with hcv
  set Bx : Set (Fin n → ℝ) := Set.Icc (fun _ => -R) (fun _ => R) with hBx
  have hBxm : MeasurableSet Bx := measurableSet_Icc
  set S₁ : Set (Fin n → ℝ) := (fun u => u + cv) ⁻¹' Bx with hS₁
  set S₂ : Set (Fin n → ℝ) := (fun u => u - cv) ⁻¹' Bx with hS₂
  have hS₁m : MeasurableSet S₁ := hBxm.preimage (measurable_id.add_const _)
  have hS₂m : MeasurableSet S₂ := hBxm.preimage (measurable_id.sub_const _)
  have hPb : ∀ x, ‖P x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hP01 x).1]; exact (hP01 x).2
  have hPint : ∀ S : Set (Fin n → ℝ), volume S ≠ ⊤ → IntegrableOn P S := fun S hS =>
    Measure.integrableOn_of_bounded (M := 1) hS hP.aestronglyMeasurable
      (ae_of_all _ fun x => hPb x)
  have hvolBx : volume Bx ≠ ⊤ := isCompact_Icc.measure_lt_top.ne
  have hS₁fin : volume S₁ ≠ ⊤ := by rw [hS₁, measure_preimage_add_right]; exact hvolBx
  have hS₂fin : volume S₂ ≠ ⊤ := by
    rw [hS₂, (measurePreserving_sub_right (volume : Measure (Fin n → ℝ)) cv).measure_preimage
      hBxm.nullMeasurableSet]
    exact hvolBx
  have hI1 : ∫ s in Bx, P (s - cv) = ∫ u in S₁, P u := by
    have := (measurePreserving_sub_right (volume : Measure (Fin n → ℝ)) cv).setIntegral_preimage_emb
      (by exact (MeasurableEquiv.subRight cv).measurableEmbedding) P S₁
    rw [← this]
    congr 2
    ext s
    simp [hS₁]
  have hI2 : ∫ s in Bx, P (s + cv) = ∫ u in S₂, P u := by
    have := (measurePreserving_add_right (volume : Measure (Fin n → ℝ)) cv).setIntegral_preimage_emb
      (by exact (MeasurableEquiv.addRight cv).measurableEmbedding) P S₂
    rw [← this]
    congr 2
    ext s
    simp [hS₂]
  have hint1 : IntegrableOn (fun s => P (s - cv)) Bx :=
    Measure.integrableOn_of_bounded (M := 1) hvolBx
      (hP.comp (measurable_id.sub_const _)).aestronglyMeasurable (ae_of_all _ fun x => hPb _)
  have hint2 : IntegrableOn (fun s => P (s + cv)) Bx :=
    Measure.integrableOn_of_bounded (M := 1) hvolBx
      (hP.comp (measurable_id.add_const _)).aestronglyMeasurable (ae_of_all _ fun x => hPb _)
  have hS₁S₂ : S₁ ∩ S₂ = Set.Icc (fun _ : Fin n => -R + c) (fun _ => R - c) := by
    ext u
    simp only [hS₁, hS₂, hBx, hcv, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, Pi.le_def,
      Pi.add_apply, Pi.sub_apply]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨fun k => by linarith [h3 k], fun k => by linarith [h2 k]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fun k => by linarith [h1 k], fun k => by linarith [h2 k]⟩,
        fun k => by linarith [h1 k], fun k => by linarith [h2 k]⟩
  have hvol1 : (volume S₁).toReal = (2 * R) ^ n := by
    rw [hS₁, measure_preimage_add_right, hBx,
      Real.volume_Icc_pi_toReal (fun k => by simp; linarith)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hvol12 : (volume (S₁ ∩ S₂)).toReal = (2 * R - 2 * c) ^ n := by
    rw [hS₁S₂, Real.volume_Icc_pi_toReal (fun k => by simp; linarith)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring_nf
  have hsplit := integral_inter_add_sdiff (f := P) hS₂m (hPint S₁ hS₁fin)
  have hmono : ∫ u in S₁ ∩ S₂, P u ≤ ∫ u in S₂, P u :=
    setIntegral_mono_set (hPint S₂ hS₂fin) (Filter.Eventually.of_forall fun x => (hP01 x).1)
      (ae_of_all _ fun x hx => hx.2)
  have hdiff : ∫ u in S₁ \ S₂, P u ≤ (volume (S₁ \ S₂)).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := P) (s := S₁ \ S₂) (C := 1)
      (lt_of_le_of_lt (measure_mono Set.sdiff_subset) (lt_top_iff_ne_top.mpr hS₁fin))
      (fun x _ => hPb x)
    rw [one_mul] at this
    exact (le_abs_self _).trans (by simpa [Measure.real] using this)
  have hvolsd := measureReal_inter_add_sdiff (μ := volume) (s := S₁) hS₂m hS₁fin
  simp only [Measure.real] at hvolsd
  calc ∫ s in Bx, (P (s - cv) - P (s + cv)) =
        (∫ s in Bx, P (s - cv)) - ∫ s in Bx, P (s + cv) := integral_sub hint1 hint2
    _ = (∫ u in S₁, P u) - ∫ u in S₂, P u := by rw [hI1, hI2]
    _ ≤ (volume (S₁ \ S₂)).toReal := by linarith
    _ = (2 * R) ^ n - (2 * R - 2 * c) ^ n := by rw [← hvol1, ← hvol12]; linarith


/-- The survival function `s ↦ P(x_k > s_k for all k)` is measurable. -/
private lemma Sandwich_surv_meas {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Ω → (Fin n → ℝ))
    (hx : Measurable x) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Measurable fun s : Fin n → ℝ => (μ {h | ∀ k, s k < x h k}).toReal := by
  set S : Set ((Fin n → ℝ) × Ω) := {p | ∀ k, p.1 k < x p.2 k} with hS
  have hSm : MeasurableSet S := by
    simp only [hS, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_lt
      ((measurable_pi_apply k).comp measurable_fst)
      ((measurable_pi_apply k).comp (hx.comp measurable_snd))
  exact (measurable_measure_prodMk_left (ν := μ) hSm).ennreal_toReal

/-- A probability of an event, as a real number, lies in `[0, 1]`. -/
private lemma Sandwich_surv01 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Set Ω) : 0 ≤ (μ S).toReal ∧ (μ S).toReal ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one⟩

/-- Layer-cake formula for `O(x)` under `μ` (`integral_eq_survival` for the law of `x`). -/
private lemma Sandwich_layer {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Ω → (Fin n → ℝ))
    (hx : Measurable x) (μ : Measure Ω) [IsProbabilityMeasure μ] (O : (Fin n → ℝ) → ℝ)
    (hO : ContDiff ℝ ∞ O) (hOc : HasCompactSupport O) :
    ∫ h, O (x h) ∂μ = ∫ s, iteratedFDeriv ℝ n O s (fun k => Pi.single k 1) *
      (μ {h | ∀ k, s k < x h k}).toReal := by
  have : IsProbabilityMeasure (μ.map x) :=
    (Measure.isProbabilityMeasure_map_iff hx.aemeasurable).mpr inferInstance
  have h1 := integral_eq_survival n O hO hOc (μ.map x)
  rw [integral_map hx.aemeasurable hO.continuous.aestronglyMeasurable] at h1
  rw [h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have hmeas : MeasurableSet {y : Fin n → ℝ | ∀ k, s k < y k} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_lt measurable_const (measurable_pi_apply k)
  simp only
  rw [Measure.map_apply hx hmeas]
  rfl


/-- The comparison of the two expectations of `O(x)` from the pointwise comparison of the survival
functions (the Fubini step of the proof of Lemma 4.2 [CVtV]). -/
private lemma Sandwich_core {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Ω → (Fin n → ℝ))
    (hx : Measurable x) (μ₀ μ₁ : Measure Ω) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (O : (Fin n → ℝ) → ℝ) (hO : ContDiff ℝ ∞ O) (hOc : HasCompactSupport O)
    (R M δ' ε : ℝ) (hM : ∀ s, |iteratedFDeriv ℝ n O s (fun k => Pi.single k 1)| ≤ M)
    (hsupp : ∀ s, s ∉ Set.Icc (fun _ : Fin n => -R) (fun _ => R) →
      iteratedFDeriv ℝ n O s (fun k => Pi.single k 1) = 0)
    (hδ0 : 0 ≤ δ') (hδR : δ' ≤ R)
    (hpt : ∀ s ∈ Set.Icc (fun _ : Fin n => -R) (fun _ => R),
      |(μ₁ {h | ∀ k, s k < x h k}).toReal - (μ₀ {h | ∀ k, s k < x h k}).toReal| ≤
        ((μ₀ {h | ∀ k, s k - δ' < x h k}).toReal -
          (μ₀ {h | ∀ k, s k + δ' < x h k}).toReal) + ε) :
    |(∫ h, O (x h) ∂μ₁) - ∫ h, O (x h) ∂μ₀| ≤
      M * (((2 * R) ^ n - (2 * R - 2 * δ') ^ n) + ε * (2 * R) ^ n) := by
  set DOf : (Fin n → ℝ) → ℝ := fun s => iteratedFDeriv ℝ n O s (fun k => Pi.single k 1) with hDOf
  have hD : Continuous DOf := by
    have h1 : Continuous (iteratedFDeriv ℝ n O) := hO.continuous_iteratedFDeriv
      (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Fin n → ℝ) ℝ
      (fun k : Fin n => Pi.single k 1)).continuous.comp h1
  have hDc : HasCompactSupport DOf :=
    (hOc.iteratedFDeriv n).comp_left (g := fun T : ContinuousMultilinearMap ℝ
      (fun _ : Fin n => Fin n → ℝ) ℝ => T (fun k : Fin n => Pi.single k 1)) (by simp)
  have hDint : Integrable DOf volume := hD.integrable_of_hasCompactSupport hDc
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hR0 : 0 ≤ R := hδ0.trans hδR
  set Bx : Set (Fin n → ℝ) := Set.Icc (fun _ => -R) (fun _ => R) with hBx
  have hBxm : MeasurableSet Bx := measurableSet_Icc
  have hvolBx : volume Bx ≠ ⊤ := isCompact_Icc.measure_lt_top.ne
  set P₀ : (Fin n → ℝ) → ℝ := fun s => (μ₀ {h | ∀ k, s k < x h k}).toReal with hP₀
  set P₁ : (Fin n → ℝ) → ℝ := fun s => (μ₁ {h | ∀ k, s k < x h k}).toReal with hP₁
  have hP₀m : Measurable P₀ := Sandwich_surv_meas x hx μ₀
  have hP₁m : Measurable P₁ := Sandwich_surv_meas x hx μ₁
  have hP₀b : ∀ s, ‖P₀ s‖ ≤ 1 := fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Sandwich_surv01 μ₀ _).1]; exact (Sandwich_surv01 μ₀ _).2
  have hP₁b : ∀ s, ‖P₁ s‖ ≤ 1 := fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Sandwich_surv01 μ₁ _).1]; exact (Sandwich_surv01 μ₁ _).2
  have hi₀ : Integrable (fun s => DOf s * P₀ s) volume :=
    hDint.mul_bdd hP₀m.aestronglyMeasurable (ae_of_all _ hP₀b)
  have hi₁ : Integrable (fun s => DOf s * P₁ s) volume :=
    hDint.mul_bdd hP₁m.aestronglyMeasurable (ae_of_all _ hP₁b)
  set Q : (Fin n → ℝ) → ℝ := fun s => P₀ (s - fun _ => δ') - P₀ (s + fun _ => δ') with hQ
  have hQm : Measurable Q :=
    (hP₀m.comp (measurable_id.sub_const _)).sub (hP₀m.comp (measurable_id.add_const _))
  have hQb : ∀ s, ‖Q s‖ ≤ 1 := fun s => by
    have h1 := Sandwich_surv01 μ₀ {h | ∀ k, s k - δ' < x h k}
    have h2 := Sandwich_surv01 μ₀ {h | ∀ k, s k + δ' < x h k}
    have hQs : Q s = (μ₀ {h | ∀ k, s k - δ' < x h k}).toReal -
        (μ₀ {h | ∀ k, s k + δ' < x h k}).toReal := rfl
    rw [Real.norm_eq_abs, abs_le, hQs]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hQint : IntegrableOn Q Bx :=
    Measure.integrableOn_of_bounded (M := 1) hvolBx hQm.aestronglyMeasurable
      (ae_of_all _ fun s => hQb s)
  have hg : IntegrableOn (fun s => M * (Q s + ε)) Bx :=
    (hQint.add (integrableOn_const hvolBx)).const_mul M
  have hpt' : ∀ s, ‖DOf s * P₁ s - DOf s * P₀ s‖ ≤
      Bx.indicator (fun s => M * (Q s + ε)) s := by
    intro s
    by_cases hs : s ∈ Bx
    · rw [Set.indicator_of_mem hs, ← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hM s) (hpt s hs) (abs_nonneg _) hM0
    · rw [Set.indicator_of_notMem hs]
      have : DOf s = 0 := hsupp s hs
      simp [this]
  have hshift := Sandwich_shift n P₀ hP₀m (fun s => Sandwich_surv01 μ₀ _) R δ' hδ0 hδR
  have hvol : (volume Bx).toReal = (2 * R) ^ n := by
    rw [hBx, Real.volume_Icc_pi_toReal (fun k => by simp; linarith)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [Sandwich_layer x hx μ₁ O hO hOc, Sandwich_layer x hx μ₀ O hO hOc, ← integral_sub hi₁ hi₀]
  calc |∫ s, (DOf s * P₁ s - DOf s * P₀ s)| = ‖∫ s, (DOf s * P₁ s - DOf s * P₀ s)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ s, Bx.indicator (fun s => M * (Q s + ε)) s :=
        norm_integral_le_of_norm_le ((integrable_indicator_iff hBxm).mpr hg) (ae_of_all _ hpt')
    _ = ∫ s in Bx, M * (Q s + ε) := integral_indicator hBxm
    _ = M * ((∫ s in Bx, Q s) + ε * (2 * R) ^ n) := by
        rw [integral_const_mul, integral_add hQint (integrableOn_const hvolBx), setIntegral_const]
        simp only [Measure.real, hvol, smul_eq_mul]
        ring
    _ ≤ M * (((2 * R) ^ n - (2 * R - 2 * δ') ^ n) + ε * (2 * R) ^ n) := by
        refine mul_le_mul_of_nonneg_left ?_ hM0
        linarith [hshift]


/-- The event `{λ_k < E_k}` grows with `E`. -/
private lemma Sandwich_ev_mono (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (n : ℕ)
    (E E' : Fin n → ℝ) (h : ∀ k, E k ≤ E' k) :
    Sandwich_ev D N A n E ⊆ Sandwich_ev D N A n E' := fun _ hh k => (hh k).trans_le (h k)

/-- The pointwise comparison of the survival functions of the two laws: for `|s_k| ≤ R`,
`|P_1(s) - P_0(s)| ≤ P_0(s - δ') - P_0(s + δ') + r + 2e`, from the joint sandwich for both laws
(error `e`) and the comparison bound of Lemma 4.3 [rescomY] (error `r`) on the window functions. -/
private lemma Sandwich_pointwise (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (n : ℕ)
    (γ c ℓ δ' e r w₁ w₂ R ε' : ℝ)
    (hc : c = γ * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ)) (hc0 : 0 < c) (hℓ0 : 0 ≤ ℓ)
    (hδ' : δ' = 2 * ℓ * c)
    (μ₀ μ₁ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (H0 : ∀ E : Fin n → ℝ, (∀ k, |E k - Eplus (lam D N A)| ≤ w₁) →
      (∫ h, Sandwich_PF D N A ε' n (fun k => E k - ℓ) h ∂μ₀) - e ≤
          (μ₀ (Sandwich_ev D N A n E)).toReal ∧
        (μ₀ (Sandwich_ev D N A n E)).toReal ≤
          (∫ h, Sandwich_PF D N A ε' n (fun k => E k + ℓ) h ∂μ₀) + e)
    (H1 : ∀ E : Fin n → ℝ, (∀ k, |E k - Eplus (lam D N A)| ≤ w₁) →
      (∫ h, Sandwich_PF D N A ε' n (fun k => E k - ℓ) h ∂μ₁) - e ≤
          (μ₁ (Sandwich_ev D N A n E)).toReal ∧
        (μ₁ (Sandwich_ev D N A n E)).toReal ≤
          (∫ h, Sandwich_PF D N A ε' n (fun k => E k + ℓ) h ∂μ₁) + e)
    (HR : ∀ E₁ : Fin n → ℝ, (∀ k, |E₁ k - Eplus (lam D N A)| ≤ w₂) →
      |(∫ h, Sandwich_PF D N A ε' n E₁ h ∂μ₀) - ∫ h, Sandwich_PF D N A ε' n E₁ h ∂μ₁| ≤ r)
    (hρ1 : R / c + 2 * ℓ ≤ w₁) (hρ2 : R / c + ℓ ≤ w₂)
    (s : Fin n → ℝ) (hs : ∀ k, |s k| ≤ R) :
    |(μ₁ {h | ∀ k, s k < Sandwich_x D N A n γ h k}).toReal -
        (μ₀ {h | ∀ k, s k < Sandwich_x D N A n γ h k}).toReal| ≤
      ((μ₀ {h | ∀ k, s k - δ' < Sandwich_x D N A n γ h k}).toReal -
        (μ₀ {h | ∀ k, s k + δ' < Sandwich_x D N A n γ h k}).toReal) + (r + 2 * e) := by
  set Ep := Eplus (lam D N A) with hEp
  set E : Fin n → ℝ := fun k => Ep - s k / c with hE
  have hsc : ∀ k, |s k / c| ≤ R / c := fun k => by
    rw [abs_div, abs_of_pos hc0]
    exact div_le_div_of_nonneg_right (hs k) hc0.le
  have hEw : ∀ k, |E k - Ep| ≤ R / c := fun k => by
    have : E k - Ep = -(s k / c) := by simp [hE]
    rw [this, abs_neg]; exact hsc k
  have hδc : δ' / c = 2 * ℓ := by rw [hδ']; field_simp
  have e1 : {h : Idx D N → Idx D N → ℂ | ∀ k, s k < Sandwich_x D N A n γ h k} =
      Sandwich_ev D N A n E := Sandwich_survSet D N A n c γ hc hc0 s
  have e2 : {h : Idx D N → Idx D N → ℂ | ∀ k, s k - δ' < Sandwich_x D N A n γ h k} =
      Sandwich_ev D N A n (fun k => E k + 2 * ℓ) := by
    have := Sandwich_survSet D N A n c γ hc hc0 (fun k => s k - δ')
    refine this.trans ?_
    congr 1
    funext k
    simp only [hE]
    rw [sub_div, hδc]
    ring
  have e3 : {h : Idx D N → Idx D N → ℂ | ∀ k, s k + δ' < Sandwich_x D N A n γ h k} =
      Sandwich_ev D N A n (fun k => E k - 2 * ℓ) := by
    have := Sandwich_survSet D N A n c γ hc hc0 (fun k => s k + δ')
    refine this.trans ?_
    congr 1
    funext k
    simp only [hE]
    rw [add_div, hδc]
    ring
  rw [e1, e2, e3]
  refine Sandwich_abstract (fun E₁ => ∫ h, Sandwich_PF D N A ε' n E₁ h ∂μ₀)
    (fun E₁ => ∫ h, Sandwich_PF D N A ε' n E₁ h ∂μ₁)
    (fun E' => (μ₀ (Sandwich_ev D N A n E')).toReal)
    (fun E' => (μ₁ (Sandwich_ev D N A n E')).toReal)
    (fun E' => ∀ k, |E' k - Ep| ≤ w₁) (fun E' => ∀ k, |E' k - Ep| ≤ w₂) ℓ e r H0 H1 HR E
    (fun k => (hEw k).trans (by linarith))
    (fun k => by
      have : |E k + 2 * ℓ - Ep| ≤ |E k - Ep| + 2 * ℓ := by
        calc |E k + 2 * ℓ - Ep| = |(E k - Ep) + 2 * ℓ| := by ring_nf
          _ ≤ |E k - Ep| + |2 * ℓ| := abs_add_le _ _
          _ = |E k - Ep| + 2 * ℓ := by rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 * ℓ by linarith)]
      linarith [hEw k])
    (fun k => by
      have : |E k - 2 * ℓ - Ep| ≤ |E k - Ep| + 2 * ℓ := by
        calc |E k - 2 * ℓ - Ep| = |(E k - Ep) - 2 * ℓ| := by ring_nf
          _ ≤ |E k - Ep| + |2 * ℓ| := abs_sub _ _
          _ = |E k - Ep| + 2 * ℓ := by rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 * ℓ by linarith)]
      linarith [hEw k])
    (fun k => by
      have : |E k + ℓ - Ep| ≤ |E k - Ep| + ℓ := by
        calc |E k + ℓ - Ep| = |(E k - Ep) + ℓ| := by ring_nf
          _ ≤ |E k - Ep| + |ℓ| := abs_add_le _ _
          _ = |E k - Ep| + ℓ := by rw [abs_of_nonneg hℓ0]
      linarith [hEw k])
    (fun k => by
      have : |E k - ℓ - Ep| ≤ |E k - Ep| + ℓ := by
        calc |E k - ℓ - Ep| = |(E k - Ep) - ℓ| := by ring_nf
          _ ≤ |E k - Ep| + |ℓ| := abs_sub _ _
          _ = |E k - Ep| + ℓ := by rw [abs_of_nonneg hℓ0]
      linarith [hEw k])
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono
      (Sandwich_ev_mono D N A n _ _ fun k => by linarith)))
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono
      (Sandwich_ev_mono D N A n _ _ fun k => by linarith)))


/-- The joint form of (17.6) of [Erds2017ADA, Corollary 17.3] for the `n` largest eigenvalues:
for `ε' ∈ (0, 1/100]`, `η = N^{-2/3-9ε'}`, `ℓ = N^{-2/3-ε'}/2`, `E₊ = E⁺ + N^{-2/3+ε'}` and
`|E_k - E⁺| ≤ N^{-2/3+ε'}`, uniformly in `t ≥ 0`,
`E Π_k K_k(A(E_k - ℓ, E₊)/π) - n N^{-D'} ≤ P(λ_k < E_k for all k)` and
`P(λ_k < E_k for all k) ≤ E Π_k K_k(A(E_k + ℓ, E₊)/π) + n N^{-D'}`. -/
theorem edge_joint_sandwich (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) :
    ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 / 100 → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t → ∀ A : Matrix (Fin N) (Fin N) ℂ,
      opNorm A ≤ (N : ℝ) ^ (-δA) → ∀ (n : ℕ) (E : Fin n → ℝ),
      (∀ k, |E k - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + ε')) →
        (∫ h, ∏ k : Fin n, stepK ((k : ℕ) + 1)
            (edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε'))
              (E k - (N : ℝ) ^ (-(2 / 3 : ℝ) - ε') / 2)
              (Eplus (lam D N A) + (N : ℝ) ^ (-(2 / 3 : ℝ) + ε')) h / Real.pi)
            ∂(ouMatLaw D N L t)) - (n : ℝ) * (N : ℝ) ^ (-D') ≤
          (ouMatLaw D N L t {h | ∀ k : Fin n,
            eigK (Matrix.of h + lam D N A) ((k : ℕ) + 1) < E k}).toReal ∧
        (ouMatLaw D N L t {h | ∀ k : Fin n,
            eigK (Matrix.of h + lam D N A) ((k : ℕ) + 1) < E k}).toReal ≤
          (∫ h, ∏ k : Fin n, stepK ((k : ℕ) + 1)
            (edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - 9 * ε'))
              (E k + (N : ℝ) ^ (-(2 / 3 : ℝ) - ε') / 2)
              (Eplus (lam D N A) + (N : ℝ) ^ (-(2 / 3 : ℝ) + ε')) h / Real.pi)
            ∂(ouMatLaw D N L t)) + (n : ℝ) * (N : ℝ) ^ (-D') := by
  intro ε' hε' hε'1 D' hD'
  obtain ⟨N₁, h₁⟩ := edge_smoothing D hD δA hδA C ε' hε' hε'1 D' hD'
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  obtain ⟨Ce, hCe, hedge⟩ := edge_close_to_edge_sc
  obtain ⟨N₂, h₂⟩ := Sandwich_ev_small ε' (1 / 9) hε' (by norm_num)
  obtain ⟨N₃, h₃⟩ := Sandwich_ev_small δA (min (1 / 20) (1 / (4 * Ce))) hδA (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ 1), ?_⟩
  intro N hN L t ht A hA n E hE
  simp only [max_le_iff] at hN
  obtain ⟨⟨hN₁, hN₂⟩, hN₃, hN1⟩ := hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hΛh : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hδ := h₃ N hN₃
  have hδ1 : (N : ℝ) ^ (-δA) ≤ 1 / 20 := hδ.trans (min_le_left _ _)
  have hδ2 : (N : ℝ) ^ (-δA) ≤ 1 / (4 * Ce) := hδ.trans (min_le_right _ _)
  have hopΛ : opNorm (lam D N A) ≤ 2 * (N : ℝ) ^ (-δA) := (opNorm_lam_le D N A).trans (by linarith)
  have hEplus : 3 / 2 ≤ Eplus (lam D N A) := by
    have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    have h1 := hedge (Idx D N) (lam D N A) hΛh (by linarith)
    have h2 : Ce * opNorm (lam D N A) ≤ 1 / 2 := by
      calc Ce * opNorm (lam D N A) ≤ Ce * (2 * (N : ℝ) ^ (-δA)) :=
            mul_le_mul_of_nonneg_left hopΛ hCe.le
        _ ≤ Ce * (2 * (1 / (4 * Ce))) := by gcongr
        _ = 1 / 2 := by field_simp; ring
    have h3 : |2 - Eplus (lam D N A)| ≤ 1 / 2 := by
      linarith [abs_nonneg (2 + Eminus (lam D N A))]
    linarith [(abs_le.mp h3).2]
  have hw : (N : ℝ) ^ (-(2 / 3 : ℝ) + ε') ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  have hEpos : ∀ k, 0 < E k := fun k => by
    have := (abs_le.mp (hE k)).1
    linarith
  have hprob : IsProbabilityMeasure (ouMatLaw D N L t) := (hC' N L t ht).prob
  have hherm : ∀ᵐ h ∂(ouMatLaw D N L t), (Matrix.of h).IsHermitian := (hC' N L t ht).herm
  have hu : (N : ℝ) ^ (-ε') ≤ 1 / 9 := h₂ N hN₂
  change (∫ h, Sandwich_PF D N A ε' n (fun k => E k - (N : ℝ) ^ (-(2 / 3 : ℝ) - ε') / 2) h
      ∂(ouMatLaw D N L t)) - (n : ℝ) * (N : ℝ) ^ (-D') ≤
      (ouMatLaw D N L t (Sandwich_ev D N A n E)).toReal ∧
    (ouMatLaw D N L t (Sandwich_ev D N A n E)).toReal ≤
      (∫ h, Sandwich_PF D N A ε' n (fun k => E k + (N : ℝ) ^ (-(2 / 3 : ℝ) - ε') / 2) h
      ∂(ouMatLaw D N L t)) + (n : ℝ) * (N : ℝ) ^ (-D')
  set μ := ouMatLaw D N L t with hμ
  set u : ℝ := (N : ℝ) ^ (-ε') with hu_def
  set ℓ : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) - ε') / 2 with hℓ
  set Bk : Fin n → Set (Idx D N → Idx D N → ℂ) := fun k => {h |
    ((eigCountAbove (Matrix.of h + lam D N A) (E k) : ℕ) : ℝ) <
        Sandwich_cnt D N A ε' (E k + ℓ) h - u ∨
      Sandwich_cnt D N A ε' (E k - ℓ) h + u <
        ((eigCountAbove (Matrix.of h + lam D N A) (E k) : ℕ) : ℝ)} with hBk
  have hBkm : ∀ k, μ (Bk k) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) :=
    fun k => h₁ N hN₁ L t ht A hA (E k) (hE k)
  set B := ⋃ k, Bk k with hB
  have hμB : (μ B).toReal ≤ n * (N : ℝ) ^ (-D') :=
    Sandwich_union_bound μ n Bk _ (Real.rpow_nonneg hN0.le _) hBkm
  have hgood : ∀ h, h ∉ B → ∀ k,
      Sandwich_cnt D N A ε' (E k + ℓ) h - u ≤
        ((eigCountAbove (Matrix.of h + lam D N A) (E k) : ℕ) : ℝ) ∧
      ((eigCountAbove (Matrix.of h + lam D N A) (E k) : ℕ) : ℝ) ≤
        Sandwich_cnt D N A ε' (E k - ℓ) h + u := by
    intro h hh k
    have : h ∉ Bk k := fun hk => hh (Set.mem_iUnion.mpr ⟨k, hk⟩)
    simp only [hBk, Set.mem_ofPred_eq, not_or, not_lt] at this
    exact this
  have hev := Sandwich_ev_meas D N A n E
  refine ⟨?_, ?_⟩
  · have := Sandwich_lower_aux μ (Sandwich_ev D N A n E) B hev
      (Sandwich_PF D N A ε' n (fun k => E k - ℓ)) (Sandwich_PF_aesm D N hN1 A ε' n _ μ hherm)
      (Sandwich_PF_mem D N A ε' n _) ?_
    · linarith
    · intro h hh hnev
      simp only [Sandwich_ev, Set.mem_ofPred_eq, not_forall, not_lt] at hnev
      obtain ⟨k₀, hk₀⟩ := hnev
      have hk1 : (k₀ : ℕ) + 1 ≤ eigCountAbove (Matrix.of h + lam D N A) (E k₀) := by
        by_contra hlt
        have := (Sandwich_event_iff (Matrix.of h + lam D N A) (E k₀) (hEpos k₀) k₀).mpr (by omega)
        linarith
      exact Sandwich_prod_zero n (fun k => Sandwich_cnt D N A ε' (E k - ℓ) h)
        (fun k => eigCountAbove (Matrix.of h + lam D N A) (E k)) u hu k₀ hk1
        (fun k => (hgood h hh k).2)
  · have := Sandwich_upper_aux μ (Sandwich_ev D N A n E) B hev
      (Sandwich_PF D N A ε' n (fun k => E k + ℓ)) (Sandwich_PF_aesm D N hN1 A ε' n _ μ hherm)
      (Sandwich_PF_mem D N A ε' n _) ?_
    · linarith
    · intro h hh hev'
      exact Sandwich_prod_one n (fun k => Sandwich_cnt D N A ε' (E k + ℓ) h)
        (fun k => eigCountAbove (Matrix.of h + lam D N A) (E k)) u hu
        (fun k => (Sandwich_event_iff _ _ (hEpos k) k).mp (hev' k))
        (fun k => (hgood h hh k).1)

/-- The conclusion of Lemma 4.3 [rescomY], as a proposition. -/
def RescomYStatement (D : ℕ) (δA εA : ℝ) (C : ℕ → ℝ) : Prop :=
    ∃ ct₀ : ℝ, 0 < ct₀ ∧ ∀ ct : ℝ, 0 < ct → ct ≤ ct₀ →
    ∀ (n : ℕ) (F : (Fin n → ℝ) → ℝ) (CF : ℕ → ℝ), ContDiff ℝ ∞ F →
      (∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l) →
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 0 < σ → σ < σ₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : EntryLaws C,
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      (N : ℝ) ^ ((1 / 3 : ℝ) + εA) ≤ hsNorm A →
      ∀ E₁ E₂ : Fin n → ℝ,
      (∀ i, |E₁ i - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
      (∀ i, |E₂ i - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
      |(∫ h, F (fun i => edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) (E₁ i) (E₂ i) h)
            ∂(ouMatLaw D N L 0)) -
        (∫ h, F (fun i => edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) (E₁ i) (E₂ i) h)
            ∂(ouMatLaw D N L (edgeTime N ct)))| ≤ (N : ℝ) ^ (-δ)

/-- The conclusion of Lemma 4.2 [CVtV], as a proposition. -/
def CVtVStatement (D : ℕ) (δA εA : ℝ) (C : ℕ → ℝ) : Prop :=
    ∃ ct₀ : ℝ, 0 < ct₀ ∧ ∀ ct : ℝ, 0 < ct → ct ≤ ct₀ →
    ∀ n : ℕ, ∀ O : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ O → HasCompactSupport O →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : EntryLaws C,
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      (N : ℝ) ^ ((1 / 3 : ℝ) + εA) ≤ hsNorm A → ∀ γ : ℝ, 1 / 2 ≤ γ → γ ≤ 2 →
      |(∫ h, O (fun i => γ * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
            (Eplus (lam D N A) - eigK (Matrix.of h + lam D N A) ((i : ℕ) + 1)))
            ∂(ouMatLaw D N L (edgeTime N ct))) -
        (∫ h, O (fun i => γ * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
            (Eplus (lam D N A) - eigK (Matrix.of h + lam D N A) ((i : ℕ) + 1)))
            ∂(ouMatLaw D N L 0))| ≤ (N : ℝ) ^ (-c)

set_option maxHeartbeats 1000000 in
/-- Lemma 4.2 [CVtV] from Lemma 4.3 [rescomY] ([Erds2017ADA, Section 17], extended to `n`
eigenvalues by `edge_joint_sandwich` and `integral_eq_survival`): the conclusion of Lemma 4.3
implies that of Lemma 4.2, with the same `𝔠₀`. -/
theorem cvtv_of_rescomY (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (C : ℕ → ℝ) (hR : RescomYStatement D δA εA C) : CVtVStatement D δA εA C := by
  obtain ⟨ct₀, hct₀, hR'⟩ := hR
  refine ⟨ct₀, hct₀, fun ct hct hctle n O hO hOc => ?_⟩
  obtain ⟨CF, hCF⟩ := Sandwich_F_CF n
  obtain ⟨σ₀, hσ₀, δ, hδ, hσ⟩ := hR' ct hct hctle n (Sandwich_F n) CF (Sandwich_F_contDiff n) hCF
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  -- the parameters
  set ε' : ℝ := min (σ₀ / 18) (1 / 100) with hε'
  have hε'0 : 0 < ε' := lt_min (by positivity) (by norm_num)
  have hε'1 : ε' ≤ 1 / 100 := min_le_right _ _
  have hε'2 : 9 * ε' < σ₀ := by
    have := min_le_left (σ₀ / 18) (1 / 100)
    linarith
  obtain ⟨Nσ, hNσ⟩ := hσ (9 * ε') (by positivity) hε'2
  obtain ⟨Ns, hNs⟩ := edge_joint_sandwich D hD δA hδA C ε' hε'0 hε'1 1 one_pos
  -- the data of `O`
  set DOf : (Fin n → ℝ) → ℝ := fun s => iteratedFDeriv ℝ n O s (fun k => Pi.single k 1) with hDOf
  have hDcont : Continuous DOf := by
    have h1 : Continuous (iteratedFDeriv ℝ n O) := hO.continuous_iteratedFDeriv
      (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Fin n → ℝ) ℝ
      (fun k : Fin n => Pi.single k 1)).continuous.comp h1
  have hDc : HasCompactSupport DOf :=
    (hOc.iteratedFDeriv n).comp_left (g := fun T : ContinuousMultilinearMap ℝ
      (fun _ : Fin n => Fin n → ℝ) ℝ => T (fun k : Fin n => Pi.single k 1)) (by simp)
  obtain ⟨M, hM⟩ := hDcont.bounded_above_of_compact_support hDc
  obtain ⟨R₀, hR₀⟩ := hDc.isCompact.isBounded.exists_norm_le
  set R : ℝ := max R₀ 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hsupp : ∀ s, s ∉ Set.Icc (fun _ : Fin n => -R) (fun _ => R) →
      iteratedFDeriv ℝ n O s (fun k => Pi.single k 1) = 0 := by
    intro s hs
    have hnot : s ∉ tsupport DOf := by
      intro hmem
      apply hs
      have h1 := (hR₀ s hmem).trans (le_max_left R₀ 1)
      rw [Set.mem_Icc]
      refine ⟨fun k => ?_, fun k => ?_⟩
      · have := (norm_le_pi_norm s k).trans h1
        rw [Real.norm_eq_abs, abs_le] at this
        linarith [this.1]
      · have := (norm_le_pi_norm s k).trans h1
        rw [Real.norm_eq_abs, abs_le] at this
        linarith [this.2]
    exact image_eq_zero_of_notMem_tsupport (f := DOf) hnot
  have hMabs : ∀ s, |iteratedFDeriv ℝ n O s (fun k => Pi.single k 1)| ≤ M := fun s => by
    have := hM s
    rwa [Real.norm_eq_abs] at this
  -- the exponent and the threshold
  set c₀ : ℝ := min ε' (min δ 1) / 2 with hc₀
  have hc₀0 : 0 < c₀ := by
    have : 0 < min ε' (min δ 1) := lt_min hε'0 (lt_min hδ one_pos)
    positivity
  have hc₀ε : 2 * c₀ ≤ ε' := by have := min_le_left ε' (min δ 1); rw [hc₀]; linarith
  have hc₀δ : 2 * c₀ ≤ δ := by
    have := (min_le_right ε' (min δ 1)).trans (min_le_left δ 1)
    rw [hc₀]; linarith
  have hc₀1 : 2 * c₀ ≤ 1 := by
    have := (min_le_right ε' (min δ 1)).trans (min_le_right δ 1)
    rw [hc₀]; linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMabs 0)
  set K₀ : ℝ := M * (2 * R) ^ n * (4 * n * (D : ℝ) ^ (2 / 3 : ℝ) + 1 + 2 * n) with hK₀
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hK₀0 : 0 ≤ K₀ := by positivity
  obtain ⟨N₁, hN₁⟩ := Sandwich_ev_large ε' (2 * R + 1) hε'0
  obtain ⟨N₂, hN₂⟩ := Sandwich_ev_large ε' (2 * (D : ℝ) ^ (2 / 3 : ℝ)) hε'0
  obtain ⟨N₃, hN₃⟩ := Sandwich_ev_large c₀ K₀ hc₀0
  refine ⟨c₀, hc₀0, max (max (max Nσ Ns) (max N₁ N₂)) (max N₃ 1), ?_⟩
  intro N hN L A hA hHS γ hγ1 hγ2
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hNσ', hNs'⟩, hN₁', hN₂'⟩, hN₃', hN1⟩ := hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  -- the scales `(DN)^{2/3}`, `c = γ (DN)^{2/3}`, `ℓ`, `δ'`
  set cN : ℝ := ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) with hcN
  set Dp : ℝ := (D : ℝ) ^ (2 / 3 : ℝ) with hDp
  have hDp1 : 1 ≤ Dp := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ D)) (by norm_num)
  set Np : ℝ := (N : ℝ) ^ (2 / 3 : ℝ) with hNp
  have hNp0 : 0 < Np := Real.rpow_pos_of_pos hN0 _
  have hcN_eq : cN = Dp * Np := by
    rw [hcN, hDp, hNp]
    push_cast
    exact Real.mul_rpow hD0.le hN0.le
  have hcN_ge : Np ≤ cN := by rw [hcN_eq]; nlinarith
  set r : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hN0 _
  have hrNp : r * Np = 1 := by rw [hr, hNp, ← Real.rpow_add hN0]; simp
  set u : ℝ := (N : ℝ) ^ (-ε') with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hN0 _
  have hu1 : u ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  have huNe : u * (N : ℝ) ^ ε' = 1 := by rw [hu, ← Real.rpow_add hN0]; simp
  set c : ℝ := γ * cN with hcdef
  have hc0 : 0 < c := mul_pos (by linarith) (lt_of_lt_of_le hNp0 hcN_ge)
  have hc_ge : Np / 2 ≤ c := by rw [hcdef]; nlinarith
  set ℓ : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) - ε') / 2 with hℓ
  have hℓ_eq : 2 * ℓ = r * u := by
    rw [hℓ, hr, hu, ← Real.rpow_add hN0, sub_eq_add_neg]; ring
  have hℓ0 : 0 ≤ ℓ := by have : 0 < r * u := mul_pos hr0 hu0; linarith
  set δ' : ℝ := 2 * ℓ * c with hδ'
  have hδ'_eq : δ' = γ * Dp * u := by
    rw [hδ', hℓ_eq, hcdef, hcN_eq]
    have : r * u * (γ * (Dp * Np)) = γ * Dp * u * (r * Np) := by ring
    rw [this, hrNp, mul_one]
  have hDu0 : 0 ≤ Dp * u := mul_nonneg (by linarith) hu0.le
  have hδ'0 : 0 ≤ δ' := by
    rw [hδ'_eq]
    calc (0 : ℝ) ≤ γ * (Dp * u) := mul_nonneg (by linarith) hDu0
      _ = γ * Dp * u := by ring
  have hδ'_le : δ' ≤ 2 * Dp * u := by
    rw [hδ'_eq]
    calc γ * Dp * u = γ * (Dp * u) := by ring
      _ ≤ 2 * (Dp * u) := mul_le_mul_of_nonneg_right hγ2 hDu0
      _ = 2 * Dp * u := by ring
  have h2Dpu : 2 * Dp * u ≤ 1 := by
    calc 2 * Dp * u ≤ (N : ℝ) ^ ε' * u := mul_le_mul_of_nonneg_right (hN₂ N hN₂') hu0.le
      _ = 1 := by rw [mul_comm]; exact huNe
  have hδ'R : δ' ≤ R := by linarith
  -- the windows
  set w₁ : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) + ε') with hw₁
  set w₂ : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) + 9 * ε') with hw₂
  have hw₁r : w₁ = r * (N : ℝ) ^ ε' := by rw [hw₁, hr, Real.rpow_add hN0]
  have hw₁₂ : w₁ ≤ w₂ := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hRc : R / c ≤ 2 * R * r := by
    rw [div_le_iff₀ hc0]
    have h1 : 1 / 2 ≤ r * c := by
      calc (1 : ℝ) / 2 = r * (Np / 2) := by linarith [hrNp]
        _ ≤ r * c := mul_le_mul_of_nonneg_left hc_ge hr0.le
    calc R = 2 * R * (1 / 2) := by ring
      _ ≤ 2 * R * (r * c) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 2 * R * r * c := by ring
  have hρ1 : R / c + 2 * ℓ ≤ w₁ := by
    have h1 : 2 * ℓ ≤ r := by
      rw [hℓ_eq]
      calc r * u ≤ r * 1 := mul_le_mul_of_nonneg_left hu1 hr0.le
        _ = r := mul_one r
    have h2 : (2 * R + 1) * r ≤ (N : ℝ) ^ ε' * r :=
      mul_le_mul_of_nonneg_right (hN₁ N hN₁') hr0.le
    rw [hw₁r]
    calc R / c + 2 * ℓ ≤ 2 * R * r + r := add_le_add hRc h1
      _ = (2 * R + 1) * r := by ring
      _ ≤ (N : ℝ) ^ ε' * r := h2
      _ = r * (N : ℝ) ^ ε' := mul_comm _ _
  have hρ2 : R / c + ℓ ≤ w₂ := by linarith
  -- the two laws
  have hP0 : IsProbabilityMeasure (ouMatLaw D N L 0) := (hC' N L 0 le_rfl).prob
  have hτ : 0 ≤ edgeTime N ct := Real.rpow_nonneg hN0.le _
  have hP1 : IsProbabilityMeasure (ouMatLaw D N L (edgeTime N ct)) := (hC' N L _ hτ).prob
  have hw₁0 : 0 < w₁ := Real.rpow_pos_of_pos hN0 _
  have hE₂ : ∀ i : Fin n, |(fun _ : Fin n => Eplus (lam D N A) + w₁) i - Eplus (lam D N A)| ≤ w₂ :=
    fun i => by
      change |Eplus (lam D N A) + w₁ - Eplus (lam D N A)| ≤ w₂
      rw [add_sub_cancel_left, abs_of_pos hw₁0]
      exact hw₁₂
  have hbound := Sandwich_core (Sandwich_x D N A n γ) (Sandwich_x_meas D N A n γ)
    (ouMatLaw D N L 0) (ouMatLaw D N L (edgeTime N ct)) O hO hOc R M δ'
    ((N : ℝ) ^ (-δ) + 2 * ((n : ℝ) * (N : ℝ) ^ (-(1 : ℝ)))) hMabs hsupp hδ'0 hδ'R
    (fun s hs => Sandwich_pointwise D N A n γ c ℓ δ' ((n : ℝ) * (N : ℝ) ^ (-(1 : ℝ)))
        ((N : ℝ) ^ (-δ)) w₁ w₂ R ε' rfl hc0 hℓ0 hδ' (ouMatLaw D N L 0)
        (ouMatLaw D N L (edgeTime N ct))
        (fun E hE => hNs N hNs' L 0 le_rfl A hA n E hE)
        (fun E hE => hNs N hNs' L _ hτ A hA n E hE)
        (fun E₁ hE₁ => hNσ N hNσ' L A hA hHS E₁
          (fun _ => Eplus (lam D N A) + w₁) hE₁ hE₂)
        hρ1 hρ2 s (fun k => abs_le.mpr ⟨hs.1 k, hs.2 k⟩))
  refine hbound.trans ?_
  set Z : ℝ := (N : ℝ) ^ (-(2 * c₀)) with hZ
  have hZ0 : 0 ≤ Z := Real.rpow_nonneg hN0.le _
  have hZe : Z = (N : ℝ) ^ (-c₀) * (N : ℝ) ^ (-c₀) := by
    rw [hZ, ← Real.rpow_add hN0]; congr 1; ring
  have hu_Z : u ≤ Z := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hv_Z : (N : ℝ) ^ (-δ) ≤ Z := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hw_Z : (N : ℝ) ^ (-(1 : ℝ)) ≤ Z := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hapow : 0 ≤ (2 * R) ^ n := by positivity
  have hshift := Sandwich_pow_sub_pow (2 * R) (2 * R - 2 * δ') (by linarith) (by linarith)
    (by linarith) n
  have h2δ : 2 * δ' ≤ 4 * Dp * Z := by
    have : 2 * Dp * u ≤ 2 * Dp * Z := mul_le_mul_of_nonneg_left hu_Z (by linarith)
    linarith
  have hεZ : (N : ℝ) ^ (-δ) + 2 * ((n : ℝ) * (N : ℝ) ^ (-(1 : ℝ))) ≤ Z + 2 * ((n : ℝ) * Z) := by
    have : (n : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) ≤ (n : ℝ) * Z := mul_le_mul_of_nonneg_left hw_Z hn0
    linarith
  have hK : K₀ * (N : ℝ) ^ (-c₀) ≤ 1 := by
    calc K₀ * (N : ℝ) ^ (-c₀) ≤ (N : ℝ) ^ c₀ * (N : ℝ) ^ (-c₀) :=
          mul_le_mul_of_nonneg_right (hN₃ N hN₃') (Real.rpow_nonneg hN0.le _)
      _ = 1 := by rw [← Real.rpow_add hN0]; simp
  have hNc0 : 0 ≤ (N : ℝ) ^ (-c₀) := Real.rpow_nonneg hN0.le _
  calc M * (((2 * R) ^ n - (2 * R - 2 * δ') ^ n) +
        ((N : ℝ) ^ (-δ) + 2 * ((n : ℝ) * (N : ℝ) ^ (-(1 : ℝ)))) * (2 * R) ^ n)
      ≤ M * ((n * (2 * R) ^ n * (4 * Dp * Z)) + (Z + 2 * ((n : ℝ) * Z)) * (2 * R) ^ n) := by
        refine mul_le_mul_of_nonneg_left ?_ hM0
        have h1 : (n : ℝ) * (2 * R) ^ n * (2 * δ') ≤ n * (2 * R) ^ n * (4 * Dp * Z) :=
          mul_le_mul_of_nonneg_left h2δ (mul_nonneg hn0 hapow)
        have h2 : ((N : ℝ) ^ (-δ) + 2 * ((n : ℝ) * (N : ℝ) ^ (-(1 : ℝ)))) * (2 * R) ^ n ≤
            (Z + 2 * ((n : ℝ) * Z)) * (2 * R) ^ n := mul_le_mul_of_nonneg_right hεZ hapow
        linarith
    _ = K₀ * Z := by rw [hK₀]; ring
    _ = K₀ * (N : ℝ) ^ (-c₀) * (N : ℝ) ^ (-c₀) := by rw [hZe]; ring
    _ ≤ 1 * (N : ℝ) ^ (-c₀) := mul_le_mul_of_nonneg_right hK hNc0
    _ = (N : ℝ) ^ (-c₀) := one_mul _

end RBMTransitionEdge

end
