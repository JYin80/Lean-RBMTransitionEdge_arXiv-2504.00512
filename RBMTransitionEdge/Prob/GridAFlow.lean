module

public import RBMTransitionEdge.Prob.GridAMart

@[expose] public section

/-!
# Martingale tools for the flow on the grid with a full initial array

Adaptedness on the grid of `GridΩA`, the single-step expansion of the flow
(3.12) [eq:Ht] for time-dependent functions (the discrete (3.47) [Ito]), the maximal stopped
Azuma bound used in place of the Burkholder–Davis–Gundy step before (3.59) [CIest], Doob's `L²`
maximal inequality, and one step of the flow in law.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Arrays of block coordinates and the generating map of the filtration -/

/-- The array `Matrix.of.symm (blockH D N w)` of a block-GUE coordinate vector `w`. -/
private abbrev GAF_arr (D N : ℕ) (w : Fin D → Coords N) : Idx D N → Idx D N → ℂ :=
  Matrix.of.symm (blockH D N w)

/-- `GAF_arr` is additive (`wig_add` entrywise). -/
private theorem GAF_arr_add (D N : ℕ) (v w : Fin D → Coords N) :
    GAF_arr D N (v + w) = GAF_arr D N v + GAF_arr D N w := by
  ext p q
  simp only [GAF_arr, blockH, Pi.add_apply, wig_add, Matrix.add_apply, Matrix.of_symm_apply]
  split_ifs <;> simp

/-- `GAF_arr` is real-homogeneous (`wig_smul` entrywise). -/
private theorem GAF_arr_smul (D N : ℕ) (c : ℝ) (w : Fin D → Coords N) :
    GAF_arr D N (c • w) = c • GAF_arr D N w := by
  ext p q
  simp only [GAF_arr, blockH, Pi.smul_apply, wig_smul, Matrix.smul_apply, Matrix.of_symm_apply]
  split_ifs <;> simp [Complex.real_smul]

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private theorem GAF_measurable_wig (n : ℕ) (i j : Fin n) :
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

/-- `GAF_arr` is measurable. -/
private theorem GAF_arr_measurable (D N : ℕ) : Measurable (GAF_arr D N) := by
  refine measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => ?_
  by_cases h : p.1 = q.1
  · simp only [GAF_arr, blockH, h, ↓reduceIte, Matrix.of_symm_apply]
    exact (GAF_measurable_wig N p.2 q.2).comp (measurable_pi_apply q.1)
  · simp only [GAF_arr, blockH, h, ↓reduceIte, Matrix.of_symm_apply]
    exact measurable_const

/-- Scalar multiples of a measurable array-valued map are measurable. -/
private theorem GAF_meas_smul {α : Type*} [MeasurableSpace α] {D N : ℕ} (c : ℝ)
    {f : α → Idx D N → Idx D N → ℂ} (hf : Measurable f) : Measurable fun x => c • f x :=
  measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b =>
    (((measurable_pi_apply b).comp (measurable_pi_apply a)).comp hf).const_smul c

/-- The generating map of `gridFiltrA D N K k`: the initial array and the increments `X_{j+1}`,
`j < k`, with the others set to `0`. -/
private def GAF_mask (D N K k : ℕ) (ω : GridΩA D N K) : GridΩA D N K :=
  (ω.1, fun j : Fin K => if (j : ℕ) < k then ω.2 j else 0)

private theorem GAF_mask_measurable (D N K k : ℕ) : Measurable (GAF_mask D N K k) := by
  unfold GAF_mask
  refine measurable_fst.prodMk (measurable_pi_iff.mpr fun j => ?_)
  by_cases hj : (j : ℕ) < k
  · simp only [hj, ↓reduceIte]
    fun_prop
  · simp [hj]

private theorem GAF_mask_mask {D N K k k' : ℕ} (hkk' : k ≤ k') (ω : GridΩA D N K) :
    GAF_mask D N K k (GAF_mask D N K k' ω) = GAF_mask D N K k ω := by
  refine Prod.ext rfl (funext fun j => ?_)
  by_cases hj : (j : ℕ) < k
  · simp [GAF_mask, hj, lt_of_lt_of_le hj hkk']
  · simp [GAF_mask, hj]

/-- `H_k` is a measurable function of the generating map of `𝓕_k`. -/
private theorem GAF_state_factor (D N K : ℕ) (h : ℝ) (k : ℕ) :
    ∃ g : GridΩA D N K → Idx D N → Idx D N → ℂ, Measurable g ∧
      ∀ ω, gridStateA D N K h ω k = g (GAF_mask D N K k ω) := by
  induction k with
  | zero => exact ⟨Prod.fst, measurable_fst, fun ω => rfl⟩
  | succ k ih =>
    obtain ⟨g, hg, hgk⟩ := ih
    by_cases hk : k < K
    · refine ⟨fun p => Real.exp (-h / 2) • g (GAF_mask D N K k p) +
        Real.sqrt (1 - Real.exp (-h)) • GAF_arr D N (p.2 ⟨k, hk⟩), ?_, fun ω => ?_⟩
      · exact (GAF_meas_smul _ (hg.comp (GAF_mask_measurable D N K k))).add
          (GAF_meas_smul _ ((GAF_arr_measurable D N).comp
            ((measurable_pi_apply (⟨k, hk⟩ : Fin K)).comp measurable_snd)))
      · beta_reduce
        rw [GAF_mask_mask (Nat.le_succ k)]
        simp [gridStateA, hk, hgk, GAF_mask, GAF_arr]
    · refine ⟨fun p => Real.exp (-h / 2) • g (GAF_mask D N K k p), ?_, fun ω => ?_⟩
      · exact GAF_meas_smul _ (hg.comp (GAF_mask_measurable D N K k))
      · beta_reduce
        rw [GAF_mask_mask (Nat.le_succ k)]
        simp [gridStateA, hk, hgk]

/-- The grid process with a full initial array is adapted to its filtration. -/
theorem gridStateA_adapted (D N K : ℕ) (h : ℝ) :
    Adapted (gridFiltrationA D N K) fun k ω => gridStateA D N K h ω k := by
  intro k
  obtain ⟨g, hg, hgk⟩ := GAF_state_factor D N K h k
  have : (fun ω => gridStateA D N K h ω k) = g ∘ GAF_mask D N K k := funext hgk
  change Measurable[gridFiltrA D N K k] (fun ω => gridStateA D N K h ω k)
  rw [this]
  exact hg.comp (comap_measurable (GAF_mask D N K k))

/-! ### Tools for the time-dependent expansion -/

/-- An entry of `wig n c` is bounded by the sup norm of the coordinates `c`. -/
private theorem GAF_wig_norm_le (n : ℕ) (c : Coords n) (i j : Fin n) : ‖wig n c i j‖ ≤ ‖c‖ := by
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
private theorem GAF_arr_norm_le (D N : ℕ) (w : Fin D → Coords N) : ‖GAF_arr D N w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun p =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun q => ?_
  simp only [GAF_arr, blockH, Matrix.of_symm_apply]
  split_ifs
  · exact (GAF_wig_norm_le N (w p.1) p.2 q.2).trans (norm_le_pi_norm w p.1)
  · simp

/-- `GAF_arr` as a real-linear map. -/
private def GAF_arrL (D N : ℕ) : (Fin D → Coords N) →ₗ[ℝ] (Idx D N → Idx D N → ℂ) where
  toFun := GAF_arr D N
  map_add' := GAF_arr_add D N
  map_smul' c w := by simpa using GAF_arr_smul D N c w

/-- `GAF_arr` is continuous (a linear map of finite-dimensional spaces). -/
private theorem GAF_arr_continuous (D N : ℕ) : Continuous (GAF_arr D N) :=
  (GAF_arrL D N).continuous_of_finiteDimensional

/-- `‖x‖^p` is integrable under the GUE blocks. -/
private theorem GAF_Int_pow (D N p : ℕ) :
    Integrable (fun x : Fin D → Coords N => ‖x‖ ^ p) (gueBlocks D N) :=
  (IsGaussian.memLp_id (gueBlocks D N) p (by simp)).integrable_norm_pow'

/-- `‖x‖⁴ ≤ Σ_i ‖x_i‖⁴` for the sup norm of a finite product. -/
private theorem GAF_Pi_pow2 {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (x : ι → E) :
    ‖x‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim x 0]
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖)
      Finset.univ_nonempty
    have h : ‖x‖ ≤ ‖x i₀‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hi₀ i (Finset.mem_univ _)
    calc ‖x‖ ^ 2 ≤ ‖x i₀‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ ≤ ∑ i, ‖x i‖ ^ 2 := Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2)
          (fun i _ => by positivity) (Finset.mem_univ i₀)

/-- `‖(u, v)‖⁴ ≤ ‖u‖⁴ + ‖v‖⁴` for the sup norm of a product. -/
private theorem GAF_Prod_pow2 {E G : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup G]
    (p : E × G) : ‖p‖ ^ 2 ≤ ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  rw [Prod.norm_def]
  rcases le_total ‖p.1‖ ‖p.2‖ with h | h
  · rw [max_eq_right h]; have := pow_nonneg (norm_nonneg p.1) 2; linarith
  · rw [max_eq_left h]; have := pow_nonneg (norm_nonneg p.2) 2; linarith

/-- The second moment of the GUE blocks: `E‖X‖² ≤ (DN + DN²)(m₂ + m₂')`, with `m₂` and `m₂'` the
second absolute moments of `N(0, 1)` and of the standard complex Gaussian. -/
private theorem GAF_Moment2 (D N : ℕ) :
    ∫ x, ‖x‖ ^ 2 ∂(gueBlocks D N) ≤ ((D : ℝ) * N + D * N * N) *
      ((∫ y, ‖y‖ ^ 2 ∂(gaussianReal 0 1)) + ∫ z, ‖z‖ ^ 2 ∂(cGauss : Measure ℂ)) := by
  set γ := gueBlocks D N with hγ
  set mR := ∫ y, ‖y‖ ^ 2 ∂(gaussianReal 0 1) with hmR
  set mC := ∫ z, ‖z‖ ^ 2 ∂(cGauss : Measure ℂ) with hmC
  have hmR0 : 0 ≤ mR := integral_nonneg fun y => by positivity
  have hmC0 : 0 ≤ mC := integral_nonneg fun z => by positivity
  have iR : Integrable (fun y : ℝ => ‖y‖ ^ 2) (gaussianReal 0 1) :=
    (IsGaussian.memLp_id (gaussianReal 0 1) 2 (by simp)).integrable_norm_pow'
  have iC : Integrable (fun z : ℂ => ‖z‖ ^ 2) (cGauss : Measure ℂ) :=
    (IsGaussian.memLp_id (cGauss : Measure ℂ) 2 (by simp)).integrable_norm_pow'
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
      Integrable (fun x : Fin D → Coords N => ‖(x a).1 i‖ ^ 2) γ :=
    fun a i => by
      have := (mpD a i).integrable_comp_of_integrable (g := fun y : ℝ => ‖y‖ ^ 2) iR
      exact this
  have iAc : ∀ (a : Fin D) (i j : Fin N),
      Integrable (fun x : Fin D → Coords N => ‖(x a).2 i j‖ ^ 2) γ :=
    fun a i j => by
      have := (mpA a i j).integrable_comp_of_integrable (g := fun z : ℂ => ‖z‖ ^ 2) iC
      exact this
  have eD : ∀ (a : Fin D) (i : Fin N), ∫ x, ‖(x a).1 i‖ ^ 2 ∂γ = mR := by
    intro a i
    have := integral_map (μ := γ) (mpD a i).measurable.aemeasurable
      (continuous_norm.pow 2).aestronglyMeasurable (f := fun y : ℝ => ‖y‖ ^ 2)
    rw [(mpD a i).map_eq] at this
    exact this.symm
  have eA : ∀ (a : Fin D) (i j : Fin N), ∫ x, ‖(x a).2 i j‖ ^ 2 ∂γ = mC := by
    intro a i j
    have := integral_map (μ := γ) (mpA a i j).measurable.aemeasurable
      (continuous_norm.pow 2).aestronglyMeasurable (f := fun z : ℂ => ‖z‖ ^ 2)
    rw [(mpA a i j).map_eq] at this
    exact this.symm
  have hpt : ∀ x : Fin D → Coords N, ‖x‖ ^ 2 ≤
      ∑ a, ((∑ i, ‖(x a).1 i‖ ^ 2) + ∑ i, ∑ j, ‖(x a).2 i j‖ ^ 2) := by
    intro x
    refine (GAF_Pi_pow2 x).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (GAF_Prod_pow2 (x a)).trans (add_le_add (GAF_Pi_pow2 _) ?_)
    exact (GAF_Pi_pow2 _).trans (Finset.sum_le_sum fun i _ => GAF_Pi_pow2 _)
  have iS : ∀ a : Fin D, Integrable (fun x : Fin D → Coords N =>
      (∑ i, ‖(x a).1 i‖ ^ 2) + ∑ i, ∑ j, ‖(x a).2 i j‖ ^ 2) γ := fun a =>
    (integrable_finsetSum _ fun i _ => iDc a i).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iAc a i j)
  calc ∫ x, ‖x‖ ^ 2 ∂γ ≤ ∫ x, ∑ a, ((∑ i, ‖(x a).1 i‖ ^ 2) + ∑ i, ∑ j, ‖(x a).2 i j‖ ^ 2) ∂γ :=
        integral_mono (GAF_Int_pow D N 2) (integrable_finsetSum _ fun a _ => iS a) hpt
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

/-- The generator of the flow (3.12) [eq:Ht] is bounded by the derivatives of orders `1` and `2`:
`‖𝓛G(H)‖ ≤ (B ‖H‖ + B E‖X‖²)/2`. -/
private theorem GAF_genA_bound (D N : ℕ) (G : (Idx D N → Idx D N → ℂ) → ℂ) (B : ℝ)
    (h1 : ∀ v, ‖iteratedFDeriv ℝ 1 G v‖ ≤ B) (h2 : ∀ v, ‖iteratedFDeriv ℝ 2 G v‖ ≤ B)
    (H : Idx D N → Idx D N → ℂ) :
    ‖genA G H‖ ≤ (B * ‖H‖ + B * ∫ x, ‖x‖ ^ 2 ∂(gueBlocks D N)) / 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (h1 H)
  have hfd : ‖fderiv ℝ G H H‖ ≤ B * ‖H‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have := h1 H
    rw [norm_iteratedFDeriv_one] at this
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hq : ∀ x : Fin D → Coords N,
      ‖iteratedFDeriv ℝ 2 G H ![GAF_arr D N x, GAF_arr D N x]‖ ≤ B * ‖x‖ ^ 2 := by
    intro x
    have e : (![GAF_arr D N x, GAF_arr D N x] : Fin 2 → Idx D N → Idx D N → ℂ) =
        fun _ => GAF_arr D N x := by
      funext i
      fin_cases i <;> rfl
    rw [e]
    refine ((iteratedFDeriv ℝ 2 G H).le_opNorm _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul (h2 H) (pow_le_pow_left₀ (norm_nonneg _) (GAF_arr_norm_le D N x) 2)
      (by positivity) hB0
  have hint : ‖∫ x, iteratedFDeriv ℝ 2 G H ![GAF_arr D N x, GAF_arr D N x] ∂(gueBlocks D N)‖ ≤
      B * ∫ x, ‖x‖ ^ 2 ∂(gueBlocks D N) := by
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le ((GAF_Int_pow D N 2).const_mul B) (ae_of_all _ hq)
  unfold genA
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have e1 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have e2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [e1, e2]
  linarith

/-- A `C¹` function of the array with derivative bounded by `B`, composed with
`x ↦ c + σ A(x)`, is integrable under the GUE blocks. -/
private theorem GAF_int_comp (D N : ℕ) (G : (Idx D N → Idx D N → ℂ) → ℂ) (hG : ContDiff ℝ 1 G)
    (B : ℝ) (hB : ∀ v, ‖iteratedFDeriv ℝ 1 G v‖ ≤ B) (c : Idx D N → Idx D N → ℂ) (σ : ℝ) :
    Integrable (fun x : Fin D → Coords N => G (c + σ • GAF_arr D N x)) (gueBlocks D N) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB c)
  have hlip : ∀ u v, ‖G u - G v‖ ≤ B * ‖u - v‖ := fun u v =>
    Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := G) (C := B) (s := Set.univ)
      (fun x _ => hG.differentiable (by norm_num) x)
      (fun x _ => by have := hB x; rwa [norm_iteratedFDeriv_one] at this)
      convex_univ (Set.mem_univ v) (Set.mem_univ u)
  have hcont : Continuous fun x : Fin D → Coords N => G (c + σ • GAF_arr D N x) :=
    hG.continuous.comp (continuous_const.add ((GAF_arr_continuous D N).const_smul σ))
  have hg : Integrable (fun x : Fin D → Coords N => ‖G c‖ + B * |σ| * ‖x‖ ^ 1)
      (gueBlocks D N) := (integrable_const _).add ((GAF_Int_pow D N 1).const_mul _)
  refine Integrable.mono' hg hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have h1 := hlip (c + σ • GAF_arr D N x) c
  have h2 : ‖σ • GAF_arr D N x‖ ≤ |σ| * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (GAF_arr_norm_le D N x) (abs_nonneg _)
  rw [add_sub_cancel_left] at h1
  calc ‖G (c + σ • GAF_arr D N x)‖ = ‖(G (c + σ • GAF_arr D N x) - G c) + G c‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖G (c + σ • GAF_arr D N x) - G c‖ + ‖G c‖ := norm_add_le _ _
    _ ≤ B * (|σ| * ‖x‖) + ‖G c‖ := by
        have := mul_le_mul_of_nonneg_left h2 hB0
        linarith
    _ = ‖G c‖ + B * |σ| * ‖x‖ ^ 1 := by ring

/-- The mean-value estimate behind the first remainder: `F(s + h, v) - F(s, v) - h ∂_s F(s, v)` is
at most `B h²` when `∂_s F` is `B`-Lipschitz in time on `[s, s + h]`. -/
private theorem GAF_time_remainder {V : Type*} (F Ft : ℝ → V → ℂ) (B h s : ℝ) (hh : 0 < h)
    (hB0 : 0 ≤ B)
    (hder : ∀ r ∈ Set.Icc s (s + h), ∀ v,
      HasDerivWithinAt (fun r' => F r' v) (Ft r v) (Set.Icc s (s + h)) r)
    (hlip : ∀ r ∈ Set.Icc s (s + h), ∀ r' ∈ Set.Icc s (s + h), ∀ v,
      ‖Ft r v - Ft r' v‖ ≤ B * |r - r'|) (v : V) :
    ‖F (s + h) v - F s v - (h : ℂ) * Ft s v‖ ≤ B * h ^ 2 := by
  have hs : s ∈ Set.Icc s (s + h) := ⟨le_rfl, by linarith⟩
  have hsh : s + h ∈ Set.Icc s (s + h) := ⟨by linarith, le_rfl⟩
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun r => F r v - (r - s) • Ft s v) (f' := fun r => Ft r v - Ft s v) (C := B * h)
    (s := Set.Icc s (s + h)) (x := s) (y := s + h)
    (fun r hr => ((hder r hr v).sub
      ((((hasDerivAt_id r).sub_const s).smul_const (Ft s v)).hasDerivWithinAt)).congr_deriv
        (by rw [one_smul]))
    (fun r hr => by
      refine (hlip r hr s hs v).trans ?_
      have : |r - s| ≤ h := by
        rw [abs_of_nonneg (by linarith [hr.1])]
        linarith [hr.2]
      exact mul_le_mul_of_nonneg_left this hB0)
    (convex_Icc _ _) hs hsh
  have e : (F (s + h) v - (s + h - s) • Ft s v) - (F s v - (s - s) • Ft s v) =
      F (s + h) v - F s v - (h : ℂ) * Ft s v := by
    simp [Complex.real_smul]
    ring
  rw [e] at key
  calc ‖F (s + h) v - F s v - (h : ℂ) * Ft s v‖ ≤ B * h * ‖s + h - s‖ := key
    _ = B * h ^ 2 := by
        rw [add_sub_cancel_left, Real.norm_eq_abs, abs_of_pos hh]
        ring

/-- The state after one step of the flow (3.12) [eq:Ht] from the array `H` with the block-GUE
increment `X`: `e^{-h/2} H + √(1 - e^{-h}) X`. -/
private abbrev GAF_Hp (D N : ℕ) (h : ℝ) (H : Idx D N → Idx D N → ℂ) (x : Fin D → Coords N) :
    Idx D N → Idx D N → ℂ :=
  Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) • Matrix.of.symm (blockH D N x)

/-- The single-step expansion of the flow (3.12) [eq:Ht] for a time-dependent function, the
discrete form of (3.47) [Ito]: `E F(s + h, e^{-h/2} H + √(1-e^{-h}) X) = F(s, H) +
h (∂_s F + 𝓛F)(s, H) + O(h²)` with the remainder `K B h² (1 + ‖H‖)⁴ (DN + 1)⁴`, `K` absolute,
when on `[s, s + h]` the functions `F(r, ·)` and `∂_s F(r, ·)` are `C⁴` with derivatives of
orders `1, …, 4` at most `B` and `∂_s F` is `B`-Lipschitz in `r`. -/
theorem gaussStepA_expansion_t : ∃ K : ℝ, ∀ (D N : ℕ)
    (F Ft : ℝ → (Idx D N → Idx D N → ℂ) → ℂ) (B h s : ℝ), 0 < h → h ≤ 1 →
    (∀ r ∈ Set.Icc s (s + h), ContDiff ℝ 4 (F r) ∧ ContDiff ℝ 4 (Ft r)) →
    (∀ r ∈ Set.Icc s (s + h), ∀ v,
      HasDerivWithinAt (fun r' => F r' v) (Ft r v) (Set.Icc s (s + h)) r) →
    (∀ r ∈ Set.Icc s (s + h), ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ v,
      ‖iteratedFDeriv ℝ j (F r) v‖ ≤ B ∧ ‖iteratedFDeriv ℝ j (Ft r) v‖ ≤ B) →
    (∀ r ∈ Set.Icc s (s + h), ∀ r' ∈ Set.Icc s (s + h), ∀ v,
      ‖Ft r v - Ft r' v‖ ≤ B * |r - r'|) →
    ∀ H : Idx D N → Idx D N → ℂ,
      ‖(∫ x, F (s + h) (Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) •
            Matrix.of.symm (blockH D N x)) ∂(gueBlocks D N)) - F s H -
          h * (Ft s H + genA (F s) H)‖ ≤
        K * B * h ^ 2 * (1 + ‖H‖) ^ 4 * ((D : ℝ) * N + 1) ^ 4 := by
  obtain ⟨K₀, hK₀⟩ := gaussStepA_expansion
  set Mo : ℝ := (∫ y, ‖y‖ ^ 2 ∂(gaussianReal 0 1)) + ∫ z, ‖z‖ ^ 2 ∂(cGauss : Measure ℂ) with hMo
  have hMo0 : 0 ≤ Mo := add_nonneg (integral_nonneg fun y => by positivity)
    (integral_nonneg fun z => by positivity)
  refine ⟨2 * max K₀ 0 + 2 + Mo, fun D N F Ft B h s hh0 hh1 hCd hder hbd hlip H => ?_⟩
  have hsI : s ∈ Set.Icc s (s + h) := ⟨le_rfl, by linarith⟩
  have hshI : s + h ∈ Set.Icc s (s + h) := ⟨by linarith, le_rfl⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans ((hbd s hsI 1 le_rfl (by norm_num) H).1)
  -- the expansion at the time `s`, for `F s` and for `∂_s F (s)`
  have e2 := hK₀ D N (F s) B h (hCd s hsI).1 (fun j h1 h2 v => (hbd s hsI j h1 h2 v).1) hh0 hh1 H
  have e3 := hK₀ D N (Ft s) B h (hCd s hsI).2 (fun j h1 h2 v => (hbd s hsI j h1 h2 v).2) hh0 hh1 H
  have hgen := GAF_genA_bound D N (Ft s) B (fun v => (hbd s hsI 1 le_rfl (by norm_num) v).2)
    (fun v => (hbd s hsI 2 (by norm_num) (by norm_num) v).2) H
  -- integrability of the three integrands
  have iF1 : Integrable (fun x : Fin D → Coords N => F (s + h) (GAF_Hp D N h H x))
      (gueBlocks D N) :=
    GAF_int_comp D N (F (s + h)) ((hCd _ hshI).1.of_le (by norm_num)) B
      (fun v => (hbd _ hshI 1 le_rfl (by norm_num) v).1) _ _
  have iF2 : Integrable (fun x : Fin D → Coords N => F s (GAF_Hp D N h H x)) (gueBlocks D N) :=
    GAF_int_comp D N (F s) ((hCd _ hsI).1.of_le (by norm_num)) B
      (fun v => (hbd _ hsI 1 le_rfl (by norm_num) v).1) _ _
  have iF3 : Integrable (fun x : Fin D → Coords N => Ft s (GAF_Hp D N h H x)) (gueBlocks D N) :=
    GAF_int_comp D N (Ft s) ((hCd _ hsI).2.of_le (by norm_num)) B
      (fun v => (hbd _ hsI 1 le_rfl (by norm_num) v).2) _ _
  -- the first piece: the time increment
  have hT1 : ‖∫ x, (F (s + h) (GAF_Hp D N h H x) - F s (GAF_Hp D N h H x) -
      (h : ℂ) * Ft s (GAF_Hp D N h H x)) ∂(gueBlocks D N)‖ ≤ B * h ^ 2 := by
    refine (norm_integral_le_of_norm_le_const (ae_of_all _ fun x =>
      GAF_time_remainder F Ft B h s hh0 hB0 hder hlip (GAF_Hp D N h H x))).trans ?_
    simp
  have iF12 : Integrable (fun x : Fin D → Coords N =>
      F (s + h) (GAF_Hp D N h H x) - F s (GAF_Hp D N h H x)) (gueBlocks D N) := iF1.sub iF2
  have iF3' : Integrable (fun x : Fin D → Coords N =>
      (h : ℂ) * Ft s (GAF_Hp D N h H x)) (gueBlocks D N) := iF3.const_mul _
  rw [integral_sub iF12 iF3', integral_sub iF1 iF2, integral_const_mul] at hT1
  -- second moment
  have hm2 : ∫ x, ‖x‖ ^ 2 ∂(gueBlocks D N) ≤ Mo * ((D : ℝ) * N + 1) ^ 4 := by
    refine (GAF_Moment2 D N).trans ?_
    have hQ : (D : ℝ) * N + D * N * N ≤ ((D : ℝ) * N + 1) ^ 4 := by
      have hD : (D : ℝ) * N * N ≤ ((D : ℝ) * N) ^ 2 := by
        rcases Nat.eq_zero_or_pos D with hD0 | hD0
        · simp [hD0]
        · have h1 : (1 : ℝ) ≤ D := by exact_mod_cast hD0
          have h2 : (N : ℝ) ≤ D * N := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) D) (Nat.cast_nonneg (α := ℝ) N)]
      have h0 : (0 : ℝ) ≤ D * N := by positivity
      nlinarith [pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4]
    calc ((D : ℝ) * N + D * N * N) * Mo ≤ ((D : ℝ) * N + 1) ^ 4 * Mo :=
          mul_le_mul_of_nonneg_right hQ hMo0
      _ = Mo * ((D : ℝ) * N + 1) ^ 4 := mul_comm _ _
  -- bookkeeping with `X = B h² W P`
  have hW1 : 1 ≤ (1 + ‖H‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg H])
  have hP1 : 1 ≤ ((D : ℝ) * N + 1) ^ 4 :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ D * N := by positivity
                    linarith)
  have hHW : ‖H‖ ≤ (1 + ‖H‖) ^ 4 := by
    have h1 : 1 + ‖H‖ ≤ (1 + ‖H‖) ^ 4 :=
      le_self_pow₀ (by linarith [norm_nonneg H]) (by norm_num)
    linarith
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (1 + ‖H‖) ^ 4 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ((D : ℝ) * N + 1) ^ 4 := ⟨_, rfl⟩
  rw [← hW] at hW1 hHW e2 e3 ⊢
  rw [← hP] at hP1 hm2 e2 e3 ⊢
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = B * h ^ 2 * W * P := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hWP : 1 ≤ W * P := one_le_mul_of_one_le_of_one_le hW1 hP1
  have hh2 : 0 ≤ h ^ 2 := by positivity
  have hBh : 0 ≤ B * h ^ 2 := by positivity
  obtain ⟨K₀', hK₀'def⟩ : ∃ K₀' : ℝ, K₀' = max K₀ 0 := ⟨_, rfl⟩
  have hK₀' : K₀ ≤ K₀' := hK₀'def ▸ le_max_left _ _
  have hK₀'0 : 0 ≤ K₀' := hK₀'def ▸ le_max_right _ _
  rw [← hK₀'def]
  have b1 : B * h ^ 2 ≤ X := by
    calc B * h ^ 2 = B * h ^ 2 * 1 := (mul_one _).symm
      _ ≤ B * h ^ 2 * (W * P) := mul_le_mul_of_nonneg_left hWP hBh
      _ = X := by rw [hX]; ring
  have hKX : K₀ * B * h ^ 2 * W * P = K₀ * X := by rw [hX]; ring
  have b2 : ‖(∫ x, F s (GAF_Hp D N h H x) ∂(gueBlocks D N)) - F s H -
      (h : ℂ) * genA (F s) H‖ ≤ K₀' * X := by
    refine e2.trans ?_
    rw [hKX]
    exact mul_le_mul_of_nonneg_right hK₀' hX0
  have b3 : ‖(∫ x, Ft s (GAF_Hp D N h H x) ∂(gueBlocks D N)) - Ft s H -
      (h : ℂ) * genA (Ft s) H‖ ≤ K₀' * X := by
    refine e3.trans ?_
    rw [hKX]
    exact mul_le_mul_of_nonneg_right hK₀' hX0
  have b4 : h ^ 2 * ‖genA (Ft s) H‖ ≤ (X + Mo * X) / 2 := by
    have h1 : h ^ 2 * (B * ‖H‖) ≤ X := by
      calc h ^ 2 * (B * ‖H‖) ≤ h ^ 2 * (B * W) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHW hB0) hh2
        _ = B * h ^ 2 * W * 1 := by ring
        _ ≤ B * h ^ 2 * W * P := mul_le_mul_of_nonneg_left hP1 (by positivity)
        _ = X := hX.symm
    have h2 : h ^ 2 * (B * ∫ x, ‖x‖ ^ 2 ∂(gueBlocks D N)) ≤ Mo * X := by
      have hW0 : 0 ≤ P := by linarith
      calc h ^ 2 * (B * ∫ x, ‖x‖ ^ 2 ∂(gueBlocks D N)) ≤ h ^ 2 * (B * (Mo * P)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm2 hB0) hh2
        _ = Mo * (B * h ^ 2 * 1 * P) := by ring
        _ ≤ Mo * (B * h ^ 2 * W * P) := by
            refine mul_le_mul_of_nonneg_left ?_ hMo0
            refine mul_le_mul_of_nonneg_right ?_ hW0
            exact mul_le_mul_of_nonneg_left hW1 hBh
        _ = Mo * X := by rw [hX]
    calc h ^ 2 * ‖genA (Ft s) H‖ ≤
          h ^ 2 * ((B * ‖H‖ + B * ∫ x, ‖x‖ ^ 2 ∂(gueBlocks D N)) / 2) :=
          mul_le_mul_of_nonneg_left hgen hh2
      _ = (h ^ 2 * (B * ‖H‖) + h ^ 2 * (B * ∫ x, ‖x‖ ^ 2 ∂(gueBlocks D N))) / 2 := by ring
      _ ≤ (X + Mo * X) / 2 := by linarith
  -- the decomposition into the three pieces
  have hdec : (∫ x, F (s + h) (GAF_Hp D N h H x) ∂(gueBlocks D N)) - F s H -
      (h : ℂ) * (Ft s H + genA (F s) H) =
      ((∫ x, F (s + h) (GAF_Hp D N h H x) ∂(gueBlocks D N)) -
        (∫ x, F s (GAF_Hp D N h H x) ∂(gueBlocks D N)) -
        (h : ℂ) * ∫ x, Ft s (GAF_Hp D N h H x) ∂(gueBlocks D N)) +
      ((∫ x, F s (GAF_Hp D N h H x) ∂(gueBlocks D N)) - F s H - (h : ℂ) * genA (F s) H) +
      (h : ℂ) * ((∫ x, Ft s (GAF_Hp D N h H x) ∂(gueBlocks D N)) - Ft s H -
        (h : ℂ) * genA (Ft s) H) + ((h : ℂ) ^ 2) * genA (Ft s) H := by ring
  have hnh : ‖(h : ℂ)‖ = h := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0]
  have hnh2 : ‖(h : ℂ) ^ 2‖ = h ^ 2 := by rw [norm_pow, hnh]
  have hfin : ‖(∫ x, F (s + h) (GAF_Hp D N h H x) ∂(gueBlocks D N)) - F s H -
      (h : ℂ) * (Ft s H + genA (F s) H)‖ ≤ X + K₀' * X + h * (K₀' * X) +
        h ^ 2 * ‖genA (Ft s) H‖ := by
    rw [hdec]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add (hT1.trans b1) b2)) ?_)) ?_)
    · rw [norm_mul, hnh]
      exact mul_le_mul_of_nonneg_left b3 hh0.le
    · rw [norm_mul, hnh2]
  have hhK : h * (K₀' * X) ≤ K₀' * X := by
    have := mul_le_mul_of_nonneg_right hh1 (mul_nonneg hK₀'0 hX0)
    linarith
  calc _ ≤ X + K₀' * X + h * (K₀' * X) + h ^ 2 * ‖genA (Ft s) H‖ := hfin
    _ ≤ (2 * K₀' + 2 + Mo) * X := by nlinarith [mul_nonneg hMo0 hX0]
    _ = _ := by rw [hX]; ring

/-- The maximal stopped Azuma–Hoeffding bound on the grid with initial law `μ₀`, in place of the
Burkholder–Davis–Gundy step before (3.59) [CIest]: with `σ` a grid stopping time, `0 < c_k` and
`E_X (a_k X)² ≤ c_k` on `{k < σ}`, the probability that
`|Σ_{k<n} 1_{k<σ} a_k(X_{k+1})| > ℓ (Σ_{k<n} c_k)^{1/2}` for some `n ≤ K` is at most
`2 K e^{-ℓ²/2}`. -/
theorem gridMartA_max (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] (a : ℕ → GridΩA D N K → (Fin D → Coords N) →L[ℝ] ℝ)
    (ha : ∀ k, StronglyMeasurable[gridFiltrA D N K k] (a k)) (σ : GridΩA D N K → WithTop ℕ)
    (hσ : IsStoppingTime (gridFiltrationA D N K) σ) (c : ℕ → ℝ≥0) (hc₀ : ∀ k, 0 < c k)
    (hc : ∀ (k : ℕ) ω, (k : WithTop ℕ) < σ ω → ∫ x, (a k ω x) ^ 2 ∂(gueBlocks D N) ≤ c k)
    (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (gridLawA D N K μ₀).real {ω | ∃ n ≤ K,
        ℓ * Real.sqrt (∑ k ∈ Finset.range n, (c k : ℝ)) < |∑ k ∈ Finset.range n,
          if hk : k < K then (if (k : WithTop ℕ) < σ ω then a k ω (ω.2 ⟨k, hk⟩) else 0)
            else 0|} ≤
      2 * K * Real.exp (-ℓ ^ 2 / 2) := by
  set μ := gridLawA D N K μ₀ with hμ
  set S : ℕ → GridΩA D N K → ℝ := fun n ω => ∑ k ∈ Finset.range n,
    if hk : k < K then (if (k : WithTop ℕ) < σ ω then a k ω (ω.2 ⟨k, hk⟩) else 0) else 0
    with hS
  -- the partial sums of the variance bounds are positive for `n ≥ 1`
  have hCpos : ∀ n, 1 ≤ n → 0 < ∑ k ∈ Finset.range n, (c k : ℝ) := fun n hn =>
    Finset.sum_pos (fun k _ => NNReal.coe_pos.2 (hc₀ k)) (Finset.nonempty_range_iff.2 (by omega))
  -- Azuma for `a` and for `-a`
  have key : ∀ n, 1 ≤ n → n ≤ K →
      μ.real {ω | ℓ * Real.sqrt (∑ k ∈ Finset.range n, (c k : ℝ)) ≤ S n ω} ≤
          Real.exp (-ℓ ^ 2 / 2) ∧
        μ.real {ω | ℓ * Real.sqrt (∑ k ∈ Finset.range n, (c k : ℝ)) ≤ -S n ω} ≤
          Real.exp (-ℓ ^ 2 / 2) := by
    intro n hn1 hnK
    set C := ∑ k ∈ Finset.range n, (c k : ℝ) with hC
    have hC0 : 0 < C := hCpos n hn1
    have hε : 0 ≤ ℓ * Real.sqrt C := by positivity
    have hexp : Real.exp (-(ℓ * Real.sqrt C) ^ 2 / (2 * C)) = Real.exp (-ℓ ^ 2 / 2) := by
      congr 1
      rw [mul_pow, Real.sq_sqrt hC0.le]
      field_simp
    constructor
    · have := gridAzumaA_stopped D N K μ₀ a ha σ hσ c hc n hnK (ℓ * Real.sqrt C) hε
      rw [hexp] at this
      exact this
    · have ha' : ∀ k, StronglyMeasurable[gridFiltrA D N K k] (fun ω => -(a k ω)) :=
        fun k => (ha k).neg
      have := gridAzumaA_stopped D N K μ₀ (fun k ω => -(a k ω)) ha' σ hσ c
        (fun k ω hω => by simpa using hc k ω hω) n hnK (ℓ * Real.sqrt C) hε
      rw [hexp] at this
      refine le_trans (le_of_eq ?_) this
      congr 1
      ext ω
      simp only [hS, Set.mem_ofPred_eq, ContinuousLinearMap.neg_apply]
      have : (∑ k ∈ Finset.range n, if hk : k < K then
          (if (k : WithTop ℕ) < σ ω then -a k ω (ω.2 ⟨k, hk⟩) else 0) else 0) =
          -∑ k ∈ Finset.range n, if hk : k < K then
            (if (k : WithTop ℕ) < σ ω then a k ω (ω.2 ⟨k, hk⟩) else 0) else 0 := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k < K <;> by_cases hkσ : (k : WithTop ℕ) < σ ω <;> simp [hk, hkσ]
      rw [this]
  -- the bad event is contained in a union over `n = 1, …, K`
  have hsub : {ω | ∃ n ≤ K, ℓ * Real.sqrt (∑ k ∈ Finset.range n, (c k : ℝ)) < |S n ω|} ⊆
      ⋃ n ∈ Finset.Icc 1 K,
        ({ω | ℓ * Real.sqrt (∑ k ∈ Finset.range n, (c k : ℝ)) ≤ S n ω} ∪
          {ω | ℓ * Real.sqrt (∑ k ∈ Finset.range n, (c k : ℝ)) ≤ -S n ω}) := by
    intro ω ⟨n, hnK, hω⟩
    have hn1 : 1 ≤ n := by
      by_contra h0
      have : n = 0 := by omega
      subst this
      simp [hS] at hω
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_Icc]
    refine ⟨n, ⟨hn1, hnK⟩, ?_⟩
    rcases le_or_gt 0 (S n ω) with h0 | h0
    · left
      rw [abs_of_nonneg h0] at hω
      exact hω.le
    · right
      rw [abs_of_neg h0] at hω
      exact hω.le
  calc μ.real {ω | ∃ n ≤ K, ℓ * Real.sqrt (∑ k ∈ Finset.range n, (c k : ℝ)) < |S n ω|}
      ≤ μ.real (⋃ n ∈ Finset.Icc 1 K,
        ({ω | ℓ * Real.sqrt (∑ k ∈ Finset.range n, (c k : ℝ)) ≤ S n ω} ∪
          {ω | ℓ * Real.sqrt (∑ k ∈ Finset.range n, (c k : ℝ)) ≤ -S n ω})) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ n ∈ Finset.Icc 1 K, μ.real
        ({ω | ℓ * Real.sqrt (∑ k ∈ Finset.range n, (c k : ℝ)) ≤ S n ω} ∪
          {ω | ℓ * Real.sqrt (∑ k ∈ Finset.range n, (c k : ℝ)) ≤ -S n ω}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 K, 2 * Real.exp (-ℓ ^ 2 / 2) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        obtain ⟨h1, h2⟩ := key n hn.1 hn.2
        refine (measureReal_union_le _ _).trans ?_
        linarith
    _ = 2 * K * Real.exp (-ℓ ^ 2 / 2) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

/-- Doob's `L²` maximal inequality for the second-order part on the grid with initial law `μ₀`:
for increments `Y_k` that are `𝓕_{k+1}`-measurable and square integrable, with
`E[Y_k | 𝓕_k] = 0` and `E Y_k² ≤ v_k`, `P(max_{n ≤ K} |Σ_{k<n} Y_k| ≥ ε) ≤ Σ_{k<K} v_k / ε²`. -/
theorem gridDoobA_max (D N K : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ))
    [IsProbabilityMeasure μ₀] (Y : ℕ → GridΩA D N K → ℝ)
    (hY : ∀ k, StronglyMeasurable[gridFiltrA D N K (k + 1)] (Y k))
    (hY₂ : ∀ k, MemLp (Y k) 2 (gridLawA D N K μ₀))
    (hY₀ : ∀ k, (gridLawA D N K μ₀)[Y k | gridFiltrA D N K k] =ᵐ[gridLawA D N K μ₀] 0)
    (v : ℕ → ℝ) (hv : ∀ k, ∫ ω, Y k ω ^ 2 ∂(gridLawA D N K μ₀) ≤ v k) (ε : ℝ) (hε : 0 < ε) :
    (gridLawA D N K μ₀).real {ω | ∃ n ≤ K, ε ≤ |∑ k ∈ Finset.range n, Y k ω|} ≤
      (∑ k ∈ Finset.range K, v k) / ε ^ 2 := by
  set μ := gridLawA D N K μ₀ with hμ
  set ℱ := gridFiltrationA D N K with hℱ
  set M : ℕ → GridΩA D N K → ℝ := fun n ω => ∑ k ∈ Finset.range n, Y k ω with hM
  have hmono := (gridFiltrA_mono D N K).1
  have hle := (gridFiltrA_mono D N K).2
  have hYint : ∀ k, Integrable (Y k) μ := fun k => (hY₂ k).integrable one_le_two
  have hM0 : M 0 = fun _ => 0 := funext fun ω => by simp [hM]
  have hMsucc : ∀ n, M (n + 1) = fun ω => M n ω + Y n ω := fun n =>
    funext fun ω => by simp [hM, Finset.sum_range_succ]
  -- the partial sums are adapted, square integrable, and a martingale
  have hMadp : StronglyAdapted ℱ M := by
    intro n
    change StronglyMeasurable[gridFiltrA D N K n] (M n)
    exact Finset.stronglyMeasurable_fun_sum _ fun k hk =>
      (hY k).mono (hmono (Finset.mem_range.1 hk))
  have hM2 : ∀ n, MemLp (M n) 2 μ := by
    intro n
    induction n with
    | zero => rw [hM0]; exact memLp_const 0
    | succ n ih => rw [hMsucc n]; exact ih.add (hY₂ n)
  have hmart : Martingale M ℱ μ := by
    refine martingale_nat hMadp (fun n => (hM2 n).integrable one_le_two) (fun n => ?_)
    have h1 : μ[M (n + 1) | gridFiltrA D N K n] =ᵐ[μ]
        fun ω => M n ω + μ[Y n | gridFiltrA D N K n] ω := by
      rw [hMsucc n]
      refine (condExp_add ((hM2 n).integrable one_le_two) (hYint n) _).trans ?_
      rw [condExp_of_stronglyMeasurable (hle n) (hMadp n) ((hM2 n).integrable one_le_two)]
      exact Filter.EventuallyEq.rfl
    filter_upwards [h1, hY₀ n] with ω a b
    rw [show μ[M (n + 1) | ℱ n] ω = μ[M (n + 1) | gridFiltrA D N K n] ω from rfl, a, b]
    simp
  -- orthogonality of the increments
  have horth : ∀ n, ∫ ω, M n ω * Y n ω ∂μ = 0 := by
    intro n
    have hint : Integrable (M n * Y n) μ := (hM2 n).integrable_mul (hY₂ n)
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := gridFiltrA D N K n)
      (hMadp n) hint (hYint n)
    have h2 : μ[M n * Y n | gridFiltrA D N K n] =ᵐ[μ] 0 := by
      filter_upwards [h1, hY₀ n] with ω a b
      rw [a]
      simp [b]
    calc ∫ ω, M n ω * Y n ω ∂μ = ∫ ω, (μ[M n * Y n | gridFiltrA D N K n]) ω ∂μ :=
          (integral_condExp (hle n)).symm
      _ = 0 := by rw [integral_congr_ae h2]; simp
  have hsq : ∀ n, ∫ ω, M n ω ^ 2 ∂μ = ∑ k ∈ Finset.range n, ∫ ω, Y k ω ^ 2 ∂μ := by
    intro n
    induction n with
    | zero => simp [hM0]
    | succ n ih =>
      have e : (fun ω => M (n + 1) ω ^ 2) =
          fun ω => (M n ω ^ 2 + 2 * (M n ω * Y n ω)) + Y n ω ^ 2 := by
        funext ω
        rw [hMsucc n]
        ring
      have hi1 := (hM2 n).integrable_sq
      have hi2 : Integrable (fun ω => M n ω * Y n ω) μ := (hM2 n).integrable_mul (hY₂ n)
      have hi3 : Integrable (fun ω => M n ω ^ 2 + 2 * (M n ω * Y n ω)) μ :=
        hi1.add (hi2.const_mul 2)
      rw [e, integral_add hi3 (hY₂ n).integrable_sq,
        integral_add hi1 (hi2.const_mul 2), integral_const_mul, horth n, ih,
        Finset.sum_range_succ]
      ring
  have hdoob := doob_sq_maximal μ ℱ M hmart hM2 K ε hε
  have hset : {ω | ∃ n ≤ K, ε ≤ |∑ k ∈ Finset.range n, Y k ω|} =
      {ω | ε ≤ (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun k => |M k ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff, hM]
  rw [hset]
  refine hdoob.trans ?_
  rw [hsq K]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun k _ => hv k) (by positivity)

/-! ### One step of the flow in law -/

/-- Measurability of `(a, w) ↦ c a + s A(w)` into the array. -/
private theorem GAF_meas_comb {D N : ℕ} (c s : ℝ) :
    Measurable fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
      c • p.1 + s • GAF_arr D N p.2 :=
  (GAF_meas_smul c measurable_fst).add
    (GAF_meas_smul s ((GAF_arr_measurable D N).comp measurable_snd))

/-- Scalar multiples of a measurable block-valued map are measurable. -/
private theorem GAF_meas_smulB {α : Type*} [MeasurableSpace α] {D N : ℕ} (c : ℝ)
    {f : α → Fin D → Coords N} (hf : Measurable f) : Measurable fun x => c • f x :=
  measurable_pi_iff.2 fun a => ((measurable_pi_apply a).comp hf).const_smul c

/-- Measurability of a linear combination of two block-valued maps. -/
private theorem GAF_measB_comb {D N : ℕ} (a b : ℝ) :
    Measurable fun p : (Fin D → Coords N) × (Fin D → Coords N) => a • p.1 + b • p.2 :=
  (GAF_meas_smulB a measurable_fst).add (GAF_meas_smulB b measurable_snd)

/-- If `g` maps `μ ⊗ μ` to `μ`, then the coordinatewise `g` maps `(⊗ᵢ μ) ⊗ (⊗ᵢ μ)` to `⊗ᵢ μ`. -/
private theorem GAF_pi_pair_map {ι E : Type*} [Fintype ι] [MeasurableSpace E]
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

/-- Invariance of the `D` GUE blocks: `a X + b Y` is distributed as `gueBlocks D N` for independent
`X`, `Y` of that law and `a² + b² = 1`. -/
private theorem GAF_blocks_map_add (D N : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((gueBlocks D N).prod (gueBlocks D N)).map (fun p => a • p.1 + b • p.2) = gueBlocks D N := by
  unfold gueBlocks
  exact GAF_pi_pair_map (ι := Fin D) (gueLaw N) (fun q : Coords N × Coords N => a • q.1 + b • q.2)
    ((measurable_fst.const_smul a).add (measurable_snd.const_smul b)) (gueLaw_map_add N a b hab)

/-- For `c² + d² = s²` with `s ≥ 0`, `c X + d Y` has the law of `s X` for independent GUE blocks. -/
private theorem GAF_blocks_map_comb (D N : ℕ) (c d s : ℝ) (hs : 0 ≤ s)
    (h : c ^ 2 + d ^ 2 = s ^ 2) :
    ((gueBlocks D N).prod (gueBlocks D N)).map (fun p => c • p.1 + d • p.2) =
      (gueBlocks D N).map (fun w => s • w) := by
  rcases hs.eq_or_lt with hs0 | hspos
  · subst hs0
    have hc : c = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    have hd : d = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    subst hc hd
    simp [Measure.map_const]
  · have hab : (c / s) ^ 2 + (d / s) ^ 2 = 1 := by
      field_simp
      linarith
    have key := GAF_blocks_map_add D N (c / s) (d / s) hab
    have e : (fun p : (Fin D → Coords N) × (Fin D → Coords N) => c • p.1 + d • p.2) =
        (fun w : Fin D → Coords N => s • w) ∘
          (fun p : (Fin D → Coords N) × (Fin D → Coords N) => (c / s) • p.1 + (d / s) • p.2) := by
      funext p
      simp only [Function.comp, smul_add, smul_smul]
      rw [mul_div_cancel₀ _ hspos.ne', mul_div_cancel₀ _ hspos.ne']
    have hsm : Measurable fun w : Fin D → Coords N => s • w := GAF_meas_smulB s measurable_id
    rw [e, ← Measure.map_map hsm (GAF_measB_comb (c / s) (d / s)), key]

/-- The convolution step: for independent block-GUE `X`, `Y` and `a² + b² = σ²`, `σ ≥ 0`,
`E F(c + A(a X + b Y)) = E F(c + σ A(X))` for bounded measurable `F`. -/
private theorem GAF_conv (D N : ℕ) (F : (Idx D N → Idx D N → ℂ) → ℂ) (hF : Measurable F) (B : ℝ)
    (hB : ∀ w, ‖F w‖ ≤ B) (c₀ : Idx D N → Idx D N → ℂ) (a b σ : ℝ) (hσ : 0 ≤ σ)
    (hab : a ^ 2 + b ^ 2 = σ ^ 2) :
    ∫ x, ∫ y, F (c₀ + GAF_arr D N (a • x + b • y)) ∂(gueBlocks D N) ∂(gueBlocks D N) =
      ∫ z, F (c₀ + σ • GAF_arr D N z) ∂(gueBlocks D N) := by
  have hFm : Measurable fun w : Fin D → Coords N => F (c₀ + GAF_arr D N w) :=
    hF.comp (measurable_const.add (GAF_arr_measurable D N))
  have hfint : Integrable (fun p : (Fin D → Coords N) × (Fin D → Coords N) =>
      F (c₀ + GAF_arr D N (a • p.1 + b • p.2))) ((gueBlocks D N).prod (gueBlocks D N)) :=
    Integrable.of_bound (hFm.comp (GAF_measB_comb a b)).aestronglyMeasurable B
      (ae_of_all _ fun p => hB _)
  calc ∫ x, ∫ y, F (c₀ + GAF_arr D N (a • x + b • y)) ∂(gueBlocks D N) ∂(gueBlocks D N)
      = ∫ p, F (c₀ + GAF_arr D N (a • p.1 + b • p.2)) ∂((gueBlocks D N).prod (gueBlocks D N)) :=
        (integral_prod _ hfint).symm
    _ = ∫ w, F (c₀ + GAF_arr D N w) ∂(((gueBlocks D N).prod (gueBlocks D N)).map
          (fun p => a • p.1 + b • p.2)) :=
        (integral_map (GAF_measB_comb a b).aemeasurable hFm.aestronglyMeasurable).symm
    _ = ∫ w, F (c₀ + GAF_arr D N w) ∂((gueBlocks D N).map (fun w => σ • w)) := by
        rw [GAF_blocks_map_comb D N a b σ hσ hab]
    _ = ∫ z, F (c₀ + GAF_arr D N (σ • z)) ∂(gueBlocks D N) :=
        integral_map (GAF_meas_smulB σ measurable_id).aemeasurable hFm.aestronglyMeasurable
    _ = ∫ z, F (c₀ + σ • GAF_arr D N z) ∂(gueBlocks D N) := by
        simp only [GAF_arr_smul]

/-- One step of the flow (3.12) [eq:Ht] in law: the block-OU law at time `s + h` is the law of
`e^{-h/2} H + √(1 - e^{-h}) X` with `H` of law (3.13) [eq:Gauss_div] at time `s` and `X` an
independent block-diagonal GUE, tested on bounded measurable functions. -/
theorem gridExpStepA (D N : ℕ) (μ₀ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ₀]
    (s h : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h) (F : (Idx D N → Idx D N → ℂ) → ℂ) (hF : Measurable F)
    (B : ℝ) (hB : ∀ w, ‖F w‖ ≤ B) :
    ∫ H, F H ∂(blockOULaw D N μ₀ (s + h)) =
      ∫ H, (∫ x, F (Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) •
        Matrix.of.symm (blockH D N x)) ∂(gueBlocks D N)) ∂(blockOULaw D N μ₀ s) := by
  set γ := gueBlocks D N with hγ
  have hB0 : ∀ w, ‖F w‖ ≤ B := hB
  -- measurable bounded integrands are integrable on probability spaces
  have hFint : ∀ (c σ : ℝ), Integrable (fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
      F (c • p.1 + σ • GAF_arr D N p.2)) (μ₀.prod γ) := fun c σ =>
    Integrable.of_bound (hF.comp (GAF_meas_comb c σ)).aestronglyMeasurable B
      (ae_of_all _ fun p => hB0 _)
  -- exponential identities
  have hE1 : ∀ t : ℝ, 0 ≤ t → 0 ≤ 1 - Real.exp (-t) := fun t ht => by
    linarith [Real.exp_le_one_iff.2 (show -t ≤ 0 by linarith)]
  have hexpsq : ∀ t : ℝ, Real.exp (-t / 2) ^ 2 = Real.exp (-t) := fun t => by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hα : Real.exp (-h / 2) * Real.exp (-s / 2) = Real.exp (-(s + h) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexpadd : Real.exp (-(s + h)) = Real.exp (-s) * Real.exp (-h) := by
    rw [← Real.exp_add]; congr 1; ring
  have hσsq : (Real.exp (-h / 2) * Real.sqrt (1 - Real.exp (-s))) ^ 2 +
      Real.sqrt (1 - Real.exp (-h)) ^ 2 = Real.sqrt (1 - Real.exp (-(s + h))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hE1 s hs), Real.sq_sqrt (hE1 h hh),
      Real.sq_sqrt (hE1 (s + h) (by linarith)), hexpsq, hexpadd]
    ring
  -- the inner integral as a function of the starting array is measurable
  have hGm : StronglyMeasurable fun H : Idx D N → Idx D N → ℂ =>
      ∫ x, F (Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) • GAF_arr D N x) ∂γ :=
    (hF.comp (GAF_meas_comb (D := D) (N := N) (Real.exp (-h / 2))
      (Real.sqrt (1 - Real.exp (-h))))).stronglyMeasurable.integral_prod_right'
  -- unfold both laws into integrals over `μ₀ ⊗ γ`
  have hLHS : ∫ H, F H ∂(blockOULaw D N μ₀ (s + h)) =
      ∫ H₀, ∫ z, F (Real.exp (-(s + h) / 2) • H₀ +
        Real.sqrt (1 - Real.exp (-(s + h))) • GAF_arr D N z) ∂γ ∂μ₀ := by
    unfold blockOULaw
    rw [integral_map (GAF_meas_comb (D := D) (N := N) _ _).aemeasurable hF.aestronglyMeasurable,
      integral_prod _ (hFint _ _)]
  have hRHS : ∫ H, (∫ x, F (Real.exp (-h / 2) • H + Real.sqrt (1 - Real.exp (-h)) •
        Matrix.of.symm (blockH D N x)) ∂γ) ∂(blockOULaw D N μ₀ s) =
      ∫ H₀, ∫ x, (∫ y, F (Real.exp (-h / 2) • (Real.exp (-s / 2) • H₀ +
        Real.sqrt (1 - Real.exp (-s)) • GAF_arr D N x) +
          Real.sqrt (1 - Real.exp (-h)) • GAF_arr D N y) ∂γ) ∂γ ∂μ₀ := by
    unfold blockOULaw
    have hGint : Integrable (fun p : (Idx D N → Idx D N → ℂ) × (Fin D → Coords N) =>
        ∫ y, F (Real.exp (-h / 2) • (Real.exp (-s / 2) • p.1 +
          Real.sqrt (1 - Real.exp (-s)) • GAF_arr D N p.2) +
            Real.sqrt (1 - Real.exp (-h)) • GAF_arr D N y) ∂γ) (μ₀.prod γ) := by
      refine Integrable.of_bound ?_ B (ae_of_all _ fun p => ?_)
      · exact ((hGm.comp_measurable (GAF_meas_comb (D := D) (N := N) _ _)).aestronglyMeasurable)
      · refine (norm_integral_le_of_norm_le_const (ae_of_all _ fun y => hB0 _)).trans ?_
        simp
    rw [integral_map (GAF_meas_comb (D := D) (N := N) _ _).aemeasurable hGm.aestronglyMeasurable,
      integral_prod _ hGint]
  rw [hLHS, hRHS]
  refine integral_congr_ae (ae_of_all _ fun H₀ => ?_)
  have hpt : ∀ x y : Fin D → Coords N, F (Real.exp (-h / 2) • (Real.exp (-s / 2) • H₀ +
        Real.sqrt (1 - Real.exp (-s)) • GAF_arr D N x) +
          Real.sqrt (1 - Real.exp (-h)) • GAF_arr D N y) =
      F (Real.exp (-(s + h) / 2) • H₀ + GAF_arr D N
        ((Real.exp (-h / 2) * Real.sqrt (1 - Real.exp (-s))) • x +
          Real.sqrt (1 - Real.exp (-h)) • y)) := by
    intro x y
    congr 1
    rw [GAF_arr_add, GAF_arr_smul, GAF_arr_smul, ← hα]
    simp only [smul_add, smul_smul]
    abel
  simp only [hpt]
  exact (GAF_conv D N F hF B hB (Real.exp (-(s + h) / 2) • H₀)
    (Real.exp (-h / 2) * Real.sqrt (1 - Real.exp (-s))) (Real.sqrt (1 - Real.exp (-h)))
    (Real.sqrt (1 - Real.exp (-(s + h)))) (Real.sqrt_nonneg _) hσsq).symm

end RBMTransitionEdge

end
