module

public import RBMTransitionEdge.Edge.CVtG
public import RBMTransitionEdge.Edge.Comparison

@[expose] public section

/-!
# Theorem 2.2

Theorem 2.2 [MixEV] at the right edge from Lemma 4.1 [CVtG] and Lemma 4.2 [CVtV] at `γ = γ₊`,
under the external input of Lemma 4.1, and at the left edge by the reflection `h ↦ -h`,
`A ↦ -A`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The map `h ↦ ‖h - B‖` from arrays to the operator norm is continuous. -/
private lemma MixEV_cont_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) :
    Continuous fun h : ι → ι → ℂ => opNorm (Matrix.of h - B) := by
  have h1 : Continuous fun h : ι → ι → ℂ => (Matrix.of h - B : Matrix ι ι ℂ) := by
    fun_prop
  have h2 : Continuous fun X : Matrix ι ι ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) X :=
    LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).toAlgEquiv.toLinearMap
  exact continuous_norm.comp (h2.comp h1)

/-- The `k`-th largest eigenvalue is a measurable function of the array of entries: it is `0` off
the closed set of Hermitian arrays and `1`-Lipschitz on it (Weyl's inequality). -/
private lemma MixEV_meas_eigK {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
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
      have := ((MixEV_cont_opNorm (Matrix.of h₀)).tendsto h₀).mono_left
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
private lemma MixEV_meas_eigK_add {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (k : ℕ) : Measurable fun h : ι → ι → ℂ => eigK (Matrix.of h + B) k := by
  have h1 : Measurable fun h : ι → ι → ℂ => h + Matrix.of.symm B := by fun_prop
  have h2 := (MixEV_meas_eigK (ι := ι) k).comp h1
  convert h2 using 2 with h
  simp only [Function.comp_apply]
  congr 1

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private lemma MixEV_meas_wig (n : ℕ) (i j : Fin n) :
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

/-- The array of `blockH D N w` is a measurable function of the block coordinates `w`. -/
private lemma MixEV_meas_blockH (D N : ℕ) :
    Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) := by
  refine measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => ?_
  change Measurable fun w : Fin D → Coords N => blockH D N w p q
  unfold blockH
  by_cases h : p.1 = q.1
  · simp only [h, ↓reduceIte]
    exact (MixEV_meas_wig N _ _).comp (measurable_pi_apply _)
  · simp only [h, ↓reduceIte]
    exact measurable_const

/-- The observable `O` applied to `a (b - λ_i(h + Λ))`, `i = 1, …, n`, `Λ = lam D N A`, is a
measurable function of the array `h`, for continuous `O` (the integrand of (4.2) [ls_CVtG]). -/
private lemma MixEV_meas_obs {n : ℕ} (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (O : (Fin n → ℝ) → ℝ) (hO : Continuous O) (a b : ℝ) :
    Measurable fun h : Idx D N → Idx D N → ℂ =>
      O (fun i => a * (b - eigK (Matrix.of h + lam D N A) ((i : ℕ) + 1))) :=
  hO.measurable.comp (measurable_pi_iff.mpr fun i => measurable_const.mul
    (measurable_const.sub (MixEV_meas_eigK_add (lam D N A) ((i : ℕ) + 1))))

/-- The Wigner matrix `wig n x` is Hermitian. -/
private lemma MixEV_wig_herm (n : ℕ) (x : Coords n) : (wig n x).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    simp [wig]
  · by_cases h' : i < j
    · have h'' : ¬ j < i := not_lt.mpr h'.le
      simp [wig, h, h', h'', Ne.symm h]
    · have h'' : j < i := lt_of_le_of_ne (not_lt.mp h') (Ne.symm h)
      simp [wig, h, h', h'', Ne.symm h]

/-- `wig n (-x) = -wig n x`. -/
private lemma MixEV_wig_neg (n : ℕ) (x : Coords n) : wig n (-x) = -wig n x := by
  ext i j
  simp only [wig, Matrix.neg_apply]
  by_cases h : i = j
  · simp [h]
  · by_cases h' : i < j <;> simp [h, h']

/-- `lam D N (-A) = -lam D N A`. -/
private lemma MixEV_lam_neg (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N (-A) = -lam D N A := by
  ext p q
  simp only [lam, Matrix.neg_apply, star_neg]
  split_ifs <;> simp [add_comm]

/-- `‖-A‖ = ‖A‖`. -/
private lemma MixEV_opNorm_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    opNorm (-A) = opNorm A := by
  unfold opNorm
  rw [map_neg, norm_neg]

/-- `‖-A‖_HS = ‖A‖_HS`. -/
private lemma MixEV_hsNorm_neg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    hsNorm (-A) = hsNorm A := by
  unfold hsNorm
  simp

/-- The block law of the entry laws of `-h` integrates `f` as `blockLaw` integrates `f (-·)`. -/
private lemma MixEV_integral_blockLaw_neg (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C)
    (f : (Fin D → Coords N) → ℝ) :
    ∫ w, f w ∂(blockLaw D N (Reflect_negLaws L)) = ∫ w, f (-w) ∂(blockLaw D N L) := by
  rw [← Reflect_blockLaw_neg]
  exact (MeasurableEquiv.neg (Fin D → Coords N)).measurableEmbedding.integral_map f

/-- The GUE law is invariant under `x ↦ -x`, so it integrates `f` as it integrates `f (-·)`. -/
private lemma MixEV_integral_gue_neg (m : ℕ) (f : Coords m → ℝ) :
    ∫ x, f x ∂(gueLaw m) = ∫ x, f (-x) ∂(gueLaw m) := by
  conv_lhs => rw [← gueLaw_map_neg m]
  exact (MeasurableEquiv.neg (Coords m)).measurableEmbedding.integral_map f

/-- Theorem 2.2 [MixEV] at the left edge from the right edge, applied to the entry laws of `-h`
and to `-A`: the right-edge half implies `MixEVStatement`. -/
theorem mixEV_reflect (h : MixEVRightStatement) : MixEVStatement := by
  intro D hD δA εA hδA hεA C n O hO hOc
  obtain ⟨c, hc, N₀, hN₀⟩ := h D hD δA εA hδA hεA C n O hO hOc
  refine ⟨c, hc, max N₀ n, fun N hN L A hA hHS =>
    ⟨hN₀ N (le_trans (le_max_left _ _) hN) L A hA hHS, ?_⟩⟩
  have hnN : n ≤ N := le_trans (le_max_right _ _) hN
  have hND : N ≤ D * N := by nlinarith
  have key := hN₀ N (le_trans (le_max_left _ _) hN) (Reflect_negLaws L) (-A)
    (by rwa [MixEV_opNorm_neg]) (by rwa [MixEV_hsNorm_neg])
  rw [MixEV_integral_blockLaw_neg, MixEV_integral_gue_neg] at key
  have hΛ : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hX : ∀ w, (HLam D N A w).IsHermitian := fun w => HLam_isHermitian D N A w
  have hcard : Fintype.card (Idx D N) = D * N := by simp
  have eL : ∀ w : Fin D → Coords N, ∀ i : Fin n,
      gammaPlus (lam D N (-A)) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
        (Eplus (lam D N (-A)) - eigK (HLam D N (-A) (-w)) ((i : ℕ) + 1)) =
      gammaMinus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
        (eigK (HLam D N A w) (D * N - (i : ℕ)) - Eminus (lam D N A)) := by
    intro w i
    have hi : (i : ℕ) < n := i.isLt
    have h1 : Eplus (-lam D N A) = -Eminus (lam D N A) := by
      rw [(edge_neg (lam D N A) hΛ).1, neg_neg]
    have h2 : gammaPlus (-lam D N A) = gammaMinus (lam D N A) :=
      (edge_neg (lam D N A) hΛ).2.symm
    have h3 : eigK (-HLam D N A w) ((i : ℕ) + 1) = -eigK (HLam D N A w) (D * N - (i : ℕ)) := by
      rw [eigK_neg _ (hX w) _ (by omega) (by rw [hcard]; omega), hcard]
      congr 2
      omega
    rw [MixEV_lam_neg, HLam_neg, h1, h2, h3]
    ring
  have eR : ∀ x : Coords (D * N), ∀ i : Fin n,
      ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * (2 - eigK (wig (D * N) (-x)) ((i : ℕ) + 1)) =
      ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * (eigK (wig (D * N) x) (D * N - (i : ℕ)) + 2) := by
    intro x i
    have hi : (i : ℕ) < n := i.isLt
    have h3 : eigK (-wig (D * N) x) ((i : ℕ) + 1) = -eigK (wig (D * N) x) (D * N - (i : ℕ)) := by
      rw [eigK_neg _ (MixEV_wig_herm _ x) _ (by omega) (by simp; omega)]
      simp only [Fintype.card_fin]
      congr 2
      omega
    rw [MixEV_wig_neg, h3]
    ring
  simp only [eL, eR] at key
  exact key

/-- Theorem 2.2 [MixEV] at the right edge from Lemma 4.1 [CVtG] and Lemma 4.2 [CVtV] at
`γ = γ₊`, under the external input of Lemma 4.1. -/
theorem mixEV_right (hEI : LandonYauEdge) : MixEVRightStatement := by
  intro D hD δA εA hδA hεA C n O hO hOc
  obtain ⟨ct₀, hct₀, hV⟩ := CVtV D hD δA εA hδA hεA C
  set ct : ℝ := min ct₀ (1 / 20) with hct
  have hct0 : 0 < ct := lt_min hct₀ (by norm_num)
  have hct1 : ct < 1 / 10 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨c₁, hc₁, N₁, h₁⟩ := CVtG hEI D hD δA hδA C ct hct0 hct1 n O hO hOc
  obtain ⟨c₂, hc₂, N₂, h₂⟩ := hV ct hct0 (min_le_left _ _) n O hO hOc
  set c : ℝ := min c₁ c₂ / 2 with hcdef
  have hc : 0 < c := by
    have := lt_min hc₁ hc₂
    positivity
  refine ⟨c, hc, max (max N₁ N₂) (max (max 2 ⌈(2 : ℝ) ^ (1 / c)⌉₊) ⌈(20 : ℝ) ^ (1 / δA)⌉₊),
    ?_⟩
  intro N hN L A hA hHS
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_right _ _))) hN
  have hNa : (2 : ℝ) ^ (1 / c) ≤ N :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_max_right _ _))) hN))
  have hNb : (20 : ℝ) ^ (1 / δA) ≤ N :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_trans (le_trans (le_max_right _ _)
      (le_max_right _ _)) hN))
  have hNr : (1 : ℝ) ≤ N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hNc : (2 : ℝ) ≤ (N : ℝ) ^ c := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ (N : ℝ) ^ c := Real.rpow_le_rpow (by positivity) hNa hc.le
  have hNd : (20 : ℝ) ≤ (N : ℝ) ^ δA := by
    calc (20 : ℝ) = ((20 : ℝ) ^ (1 / δA)) ^ δA := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hδA.ne', Real.rpow_one]
      _ ≤ (N : ℝ) ^ δA := Real.rpow_le_rpow (by positivity) hNb hδA.le
  have hnc : (N : ℝ) ^ (-c) ≤ 1 / 2 := by
    rw [Real.rpow_neg hNpos.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hNc
  have hnd : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
    rw [Real.rpow_neg hNpos.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hNd
  have hnc0 : 0 ≤ (N : ℝ) ^ (-c) := Real.rpow_nonneg hNpos.le _
  have e2c : (N : ℝ) ^ (-(c + c)) = (N : ℝ) ^ (-c) * (N : ℝ) ^ (-c) := by
    rw [show -(c + c) = -c + -c by ring, Real.rpow_add hNpos]
  have hcc : c + c ≤ c₁ ∧ c + c ≤ c₂ := by
    rw [hcdef]
    exact ⟨by linarith [min_le_left c₁ c₂], by linarith [min_le_right c₁ c₂]⟩
  have hb1 : (N : ℝ) ^ (-c₁) ≤ (N : ℝ) ^ (-c) * (N : ℝ) ^ (-c) := by
    rw [← e2c]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith [hcc.1])
  have hb2 : (N : ℝ) ^ (-c₂) ≤ (N : ℝ) ^ (-c) * (N : ℝ) ^ (-c) := by
    rw [← e2c]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith [hcc.2])
  have hℓ : opNorm (lam D N A) ≤ 1 / 10 := by
    have := opNorm_lam_le D N A
    linarith
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  obtain ⟨-, -, hg1, hg2, -, -⟩ := def_gamma_limits (lam D N A) (lam_isHermitian D N A) hℓ
  have hI := h₁ N hN1 L A hA
  have hII := h₂ N hN2 L A hA hHS (gammaPlus (lam D N A)) hg1 hg2
  have hmap : ∫ h, O (fun i => gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
        (Eplus (lam D N A) - eigK (Matrix.of h + lam D N A) ((i : ℕ) + 1)))
        ∂(ouMatLaw D N L 0) =
      ∫ w, O (fun i => gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
        (Eplus (lam D N A) - eigK (HLam D N A w) ((i : ℕ) + 1))) ∂(blockLaw D N L) := by
    rw [ouMatLaw_zero, integral_map (MixEV_meas_blockH D N).aemeasurable
      (MixEV_meas_obs D N A O hO.continuous _ _).aestronglyMeasurable]
    rfl
  rw [hmap] at hII
  have h3 := abs_sub_le
    (∫ w, O (fun i => gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
        (Eplus (lam D N A) - eigK (HLam D N A w) ((i : ℕ) + 1))) ∂(blockLaw D N L))
    (∫ h, O (fun i => gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
        (Eplus (lam D N A) - eigK (Matrix.of h + lam D N A) ((i : ℕ) + 1)))
        ∂(ouMatLaw D N L (edgeTime N ct)))
    (∫ x, O (fun i => ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
        (2 - eigK (wig (D * N) x) ((i : ℕ) + 1))) ∂(gueLaw (D * N)))
  rw [abs_sub_comm] at hII
  have hsq : (N : ℝ) ^ (-c) * (N : ℝ) ^ (-c) * 2 ≤ (N : ℝ) ^ (-c) := by nlinarith
  linarith

/-- Theorem 2.2 [MixEV], under the external input of Lemma 4.1 [CVtG]. -/
theorem mixEV (hEI : LandonYauEdge) : MixEVStatement :=
  mixEV_reflect (mixEV_right hEI)

end RBMTransitionEdge

end
