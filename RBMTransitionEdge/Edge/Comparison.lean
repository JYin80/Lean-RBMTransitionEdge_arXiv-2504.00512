module

public import RBMTransitionEdge.Edge.CountExpand
public import RBMTransitionEdge.Edge.Sandwich
public import RBMTransitionEdge.Flow.Mix

@[expose] public section

/-!
# Lemma 4.3 [rescomY] and Lemma 4.2 [CVtV]

The bound (4.21) [eq:F2] of `E ℱ₂` along `H_t` of (4.1) [defVt] from the spectral sums
(4.17)–(4.20), rigidity and the eigenvector bound (3.4) [eq:extend:main_evector1]; the comparison
(4.7) [2comVVt] of Lemma 4.3 by the fundamental theorem of calculus in `t`; and Lemma 4.2 from
Lemma 4.3 by the joint sandwich.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Scalar and measure tools -/

/-- For `e < x`, eventually `K N^e ≤ N^x / 3`. -/
private lemma Cmp_absorb (K e x : ℝ) (he : e < x) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → K * (N : ℝ) ^ e ≤ (N : ℝ) ^ x / 3 := by
  have h := ((tendsto_rpow_atTop (by linarith : 0 < x - e)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (3 * K)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h1 : 3 * K ≤ (N : ℝ) ^ (x - e) := hN₁ N (le_trans (le_max_left _ _) hN)
  have h2 : (N : ℝ) ^ x = (N : ℝ) ^ (x - e) * (N : ℝ) ^ e := by
    rw [← Real.rpow_add hN0]; ring_nf
  have h3 : 0 ≤ (N : ℝ) ^ e := Real.rpow_nonneg hN0.le _
  rw [h2]
  nlinarith

/-- `x x^a = x^{1 + a}` for `x > 0`. -/
private lemma Cmp_mul_rpow (x a : ℝ) (hx : 0 < x) : x * x ^ a = x ^ (1 + a) := by
  rw [Real.rpow_add hx, Real.rpow_one]

/-- For `δ > 0`, eventually `K ≤ N^δ`. -/
private lemma Cmp_ev (K δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → K ≤ (N : ℝ) ^ δ := by
  have h := ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨N₀, hN₀⟩

/-- `‖E f‖ ≤ X + B₁ ε₁ + B₂ ε₂` when `|f| ≤ B₂` almost surely, `|f| ≤ B₁` off `T₂`, `|f| ≤ X`
off `T₁ ∪ T₂`, `P(T₁) ≤ ε₁` and `P(T₂) ≤ ε₂`. -/
private lemma Cmp_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℂ) (T₁ T₂ : Set α) (X B₁ B₂ ε₁ ε₂ : ℝ) (hX : 0 ≤ X) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hT₁ : μ T₁ ≤ ENNReal.ofReal ε₁)
    (hT₂ : μ T₂ ≤ ENNReal.ofReal ε₂)
    (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ B₂ ∧ (x ∉ T₂ → ‖f x‖ ≤ B₁) ∧ (x ∉ T₁ → x ∉ T₂ → ‖f x‖ ≤ X)) :
    ‖∫ x, f x ∂μ‖ ≤ X + B₁ * ε₁ + B₂ * ε₂ := by
  set S₁ := toMeasurable μ T₁ with hS₁d
  set S₂ := toMeasurable μ T₂ with hS₂d
  have hS₁ : MeasurableSet S₁ := measurableSet_toMeasurable μ T₁
  have hS₂ : MeasurableSet S₂ := measurableSet_toMeasurable μ T₂
  have hr₁ : μ.real S₁ ≤ ε₁ := by
    rw [measureReal_def, hS₁d, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε₁ hT₁
  have hr₂ : μ.real S₂ ≤ ε₂ := by
    rw [measureReal_def, hS₂d, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε₂ hT₂
  have hi₁ : Integrable (fun x => S₁.indicator (1 : α → ℝ) x) μ :=
    (integrable_const (1 : ℝ)).indicator hS₁
  have hi₂ : Integrable (fun x => S₂.indicator (1 : α → ℝ) x) μ :=
    (integrable_const (1 : ℝ)).indicator hS₂
  have hint₁ : Integrable (fun x => X + B₁ * S₁.indicator (1 : α → ℝ) x) μ :=
    (integrable_const X).add (hi₁.const_mul B₁)
  have hint : Integrable (fun x => X + B₁ * S₁.indicator (1 : α → ℝ) x +
      B₂ * S₂.indicator (1 : α → ℝ) x) μ := hint₁.add (hi₂.const_mul B₂)
  calc ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (X + B₁ * S₁.indicator (1 : α → ℝ) x + B₂ * S₂.indicator (1 : α → ℝ) x) ∂μ := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) hint ?_
      filter_upwards [hf] with x hx
      have i1 : 0 ≤ S₁.indicator (1 : α → ℝ) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      by_cases h2 : x ∈ S₂
      · rw [Set.indicator_of_mem h2, Pi.one_apply, mul_one]
        nlinarith [hx.1]
      · have hx2 : x ∉ T₂ := fun h => h2 (subset_toMeasurable μ T₂ h)
        rw [Set.indicator_of_notMem h2, mul_zero, add_zero]
        by_cases h1 : x ∈ S₁
        · rw [Set.indicator_of_mem h1, Pi.one_apply, mul_one]
          linarith [hx.2.1 hx2]
        · have hx1 : x ∉ T₁ := fun h => h1 (subset_toMeasurable μ T₁ h)
          rw [Set.indicator_of_notMem h1, mul_zero, add_zero]
          exact hx.2.2 hx1 hx2
    _ = X + B₁ * μ.real S₁ + B₂ * μ.real S₂ := by
      rw [integral_add hint₁ (hi₂.const_mul B₂), integral_add (integrable_const X)
        (hi₁.const_mul B₁), integral_const, integral_const_mul, integral_const_mul,
        integral_indicator_one hS₁, integral_indicator_one hS₂]
      simp
    _ ≤ X + B₁ * ε₁ + B₂ * ε₂ := by gcongr

/-- `μ(S₁ ∪ ⋃_a S₂(a) ∪ S₃ ∪ S₄) ≤ (D + 3) x` when each set has measure at most `x`. -/
private lemma Cmp_union_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (D : ℕ)
    (S₁ S₃ S₄ : Set α) (S₂ : Fin D → Set α) (x : ℝ) (hx : 0 ≤ x)
    (h₁ : μ S₁ ≤ ENNReal.ofReal x) (h₂ : ∀ a, μ (S₂ a) ≤ ENNReal.ofReal x)
    (h₃ : μ S₃ ≤ ENNReal.ofReal x) (h₄ : μ S₄ ≤ ENNReal.ofReal x) :
    μ (S₁ ∪ (⋃ a, S₂ a) ∪ S₃ ∪ S₄) ≤ ENNReal.ofReal (((D : ℝ) + 3) * x) := by
  have hU : μ (⋃ a, S₂ a) ≤ ENNReal.ofReal ((D : ℝ) * x) := by
    refine (measure_iUnion_fintype_le μ S₂).trans ?_
    calc ∑ a, μ (S₂ a) ≤ ∑ _a : Fin D, ENNReal.ofReal x := Finset.sum_le_sum fun a _ => h₂ a
      _ = ENNReal.ofReal ((D : ℝ) * x) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have e : ((D : ℝ) + 3) * x = x + (D : ℝ) * x + x + x := by ring
  rw [e, ENNReal.ofReal_add (by positivity) hx, ENNReal.ofReal_add (by positivity) hx,
    ENNReal.ofReal_add hx (by positivity)]
  refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans (add_le_add h₁ hU)) h₃)) h₄)

/-! ### The integrand of `entryF2` -/

section Integrand

variable {D N : ℕ}

/-- The one-entry substitution is smooth in the array and the value. -/
private lemma Cmp_setEntry_contDiff (i j : Idx D N) :
    ContDiff ℝ ∞ fun p : (Idx D N → Idx D N → ℂ) × ℂ => setEntry p.1 i j p.2 := by
  refine contDiff_pi.mpr fun k => contDiff_pi.mpr fun l => ?_
  unfold setEntry
  by_cases hij : i = j
  · simp only [hij, ite_true]
    split_ifs
    · exact Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp contDiff_snd)
    · exact (((ContinuousLinearMap.proj (R := ℝ) l).comp (ContinuousLinearMap.proj (R := ℝ) k)).comp
        (ContinuousLinearMap.fst ℝ (Idx D N → Idx D N → ℂ) ℂ)).contDiff
  · simp only [hij, ite_false]
    split_ifs
    · exact contDiff_snd
    · exact Complex.conjCLE.contDiff.comp contDiff_snd
    · exact (((ContinuousLinearMap.proj (R := ℝ) l).comp (ContinuousLinearMap.proj (R := ℝ) k)).comp
        (ContinuousLinearMap.fst ℝ (Idx D N → Idx D N → ℂ) ℂ)).contDiff

/-- `setEntry` of a Hermitian array is Hermitian. -/
private lemma Cmp_setEntry_herm (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (w : ℂ) : (Matrix.of (setEntry h i j w)).IsHermitian := by
  have e : symArr (setEntry h i j w) = setEntry h i j w := by
    rw [symArr_setEntry, symArr_of_isHermitian h hh]
  rw [← e]
  exact symArr_isHermitian _

/-- The partial derivative in the second variable of a smooth function on `E × ℂ` is smooth. -/
private lemma Cmp_fderiv_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E × ℂ → ℂ) (n : WithTop ℕ∞) {m : WithTop ℕ∞} (hG : ContDiff ℝ m G) (hnm : n + 1 ≤ m) :
    ContDiff ℝ n fun p : E × ℂ => fderiv ℝ (fun w => G (p.1, w)) p.2 :=
  ContDiff.fderiv (𝕜 := ℝ) (f := fun p w => G (p.1, w)) (g := Prod.snd)
    (hG.comp ((contDiff_fst (𝕜 := ℝ)).fst.prodMk contDiff_snd)) contDiff_snd hnm

/-- For a smooth `Φ`, `h ↦ ∂_w ∂_{w̄} Φ(setEntry h i j w)|_{w = h_{ij}}` is continuous. -/
private lemma Cmp_wirt_continuous (Φ : (Idx D N → Idx D N → ℂ) → ℂ) (hΦ : ContDiff ℝ ∞ Φ)
    (i j : Idx D N) :
    Continuous fun h => wirt 1 1 (fun w => Φ (setEntry h i j w)) (h i j) := by
  have hP : ContDiff ℝ ∞ fun p : (Idx D N → Idx D N → ℂ) × ℂ => Φ (setEntry p.1 i j p.2) :=
    hΦ.comp (Cmp_setEntry_contDiff i j)
  have hd1 : ContDiff ℝ 2 fun p : (Idx D N → Idx D N → ℂ) × ℂ =>
      fderiv ℝ (fun w => Φ (setEntry p.1 i j w)) p.2 :=
    Cmp_fderiv_contDiff _ 2 hP (WithTop.coe_le_coe.mpr le_top)
  have hQc : ContDiff ℝ 2 fun p : (Idx D N → Idx D N → ℂ) × ℂ =>
      dWbar (fun w => Φ (setEntry p.1 i j w)) p.2 := by
    have ha := hd1.clm_apply (contDiff_const (c := (1 : ℂ)))
    have hb := hd1.clm_apply (contDiff_const (c := Complex.I))
    have hab := (ha.add ((contDiff_const (c := Complex.I)).mul hb)).div_const (2 : ℂ)
    exact hab
  have hd2 : ContDiff ℝ 1 fun p : (Idx D N → Idx D N → ℂ) × ℂ =>
      fderiv ℝ (fun w => dWbar (fun w => Φ (setEntry p.1 i j w)) w) p.2 :=
    Cmp_fderiv_contDiff (fun p => dWbar (fun w => Φ (setEntry p.1 i j w)) p.2) 1 hQc (by norm_num)
  have hc : Continuous fun h : Idx D N → Idx D N → ℂ => (h, h i j) :=
    continuous_id.prodMk ((continuous_apply j).comp (continuous_apply i))
  have h2 := hd2.continuous.comp hc
  simp only [wirt, Function.iterate_one, dW]
  exact ((h2.clm_apply continuous_const).sub (continuous_const.mul
    (h2.clm_apply continuous_const))).div_const _

end Integrand

/-! ### Integrability of the integrand of `entryF2` -/

section Integrable

/-- The entries of `G` and `Im G` are at most `η⁻¹` for Hermitian `X` and `Im z = η > 0`. -/
private lemma Cmp_entries_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (η : ℝ) (hη : 0 < η) (hz : z.im = η) (a b : ι) :
    ‖res X z a b‖ ≤ η⁻¹ ∧ ‖imRes X z a b‖ ≤ η⁻¹ := by
  have hz0 : 0 < z.im := by rw [hz]; exact hη
  have hG : ∀ a b, ‖res X z a b‖ ≤ η⁻¹ := fun a b =>
    (norm_apply_le_opNorm _ a b).trans (by have := opNorm_res_le X hX z hz0; rwa [hz] at this)
  refine ⟨hG a b, ?_⟩
  have e : imRes X z a b = (2 * Complex.I)⁻¹ * (res X z a b - starRingEnd ℂ (res X z b a)) := by
    simp [imRes, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply]
  rw [e, norm_mul, norm_inv, norm_mul, Complex.norm_I]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have h3 := norm_sub_le (res X z a b) (starRingEnd ℂ (res X z b a))
  rw [Complex.norm_conj] at h3
  have h4 := hG a b
  have h5 := hG b a
  calc ((2 : ℝ) * 1)⁻¹ * ‖res X z a b - starRingEnd ℂ (res X z b a)‖
      ≤ ((2 : ℝ) * 1)⁻¹ * (η⁻¹ + η⁻¹) := by
        refine mul_le_mul_of_nonneg_left (h3.trans (by linarith)) (by positivity)
    _ = η⁻¹ := by ring

/-- (4.6) [derivative_bound_F] at `l = 6` with `C_* = max(C_6, 1)`: if `1 + ‖x‖ ≤ Y`, the
derivatives of `F` of orders `1, …, 6` at `x` are at most `C_* Y^{C_*}`. -/
private lemma Cmp_BF {n : ℕ} (F : (Fin n → ℝ) → ℝ) (CF : ℕ → ℝ)
    (hCF : ∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l)
    (x : Fin n → ℝ) (Y : ℝ) (hY : 1 + ‖x‖ ≤ Y) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 6) :
    ‖iteratedFDeriv ℝ k F x‖ ≤ max (CF 6) 1 * Y ^ max (CF 6) 1 := by
  have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have h0 : 0 < (1 + ‖x‖) ^ CF 6 := Real.rpow_pos_of_pos (by linarith) _
  have hCs : CF 6 ≤ max (CF 6) 1 := le_max_left _ _
  have hCs1 : (1 : ℝ) ≤ max (CF 6) 1 := le_max_right _ _
  calc ‖iteratedFDeriv ℝ k F x‖ ≤ CF 6 * (1 + ‖x‖) ^ CF 6 := hCF 6 k hk1 hk2 x
    _ ≤ max (CF 6) 1 * (1 + ‖x‖) ^ CF 6 := mul_le_mul_of_nonneg_right hCs h0.le
    _ ≤ max (CF 6) 1 * (1 + ‖x‖) ^ max (CF 6) 1 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hCs) (by linarith)
    _ ≤ max (CF 6) 1 * Y ^ max (CF 6) 1 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hY (by linarith)) (by linarith)

/-- `∂_w ∂_{w̄}` of a slice of `edgeFn` at a Hermitian array is at most
`K_w C_* (1 + R)^{C_*} max(1, η⁻¹)²` when `DN |E₂(m) - E₁(m)| / η ≤ R` for every `m`
(`edgeFn_wirt_le` with `Γ = Γ_I = max(1, η⁻¹)` and `edgeCount_abs_le`). -/
private lemma Cmp_wirt_bound (n : ℕ) :
    ∃ Kw : ℝ, 0 < Kw ∧ ∀ (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ), 0 < η →
      ∀ (F : (Fin n → ℝ) → ℝ), ContDiff ℝ ∞ F → ∀ CF : ℕ → ℝ,
      (∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l) →
      ∀ (E₁ E₂ : Fin n → ℝ) (R : ℝ), 0 ≤ R →
      (∀ m, ((D * N : ℕ) : ℝ) * |E₂ m - E₁ m| / η ≤ R) →
      ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → ∀ (i j : Idx D N) (w : ℂ),
        ‖wirt 1 1 (fun w' => (edgeFn D N A η F E₁ E₂ (setEntry h i j w') : ℂ)) w‖ ≤
          Kw * (max (CF 6) 1 * (1 + R) ^ max (CF 6) 1) * max 1 η⁻¹ * max 1 η⁻¹ := by
  obtain ⟨K, hK, H⟩ := edgeFn_wirt_le n 1 1 (by norm_num)
  refine ⟨K, hK, fun D N A η hη F hF CF hCF E₁ E₂ R hR hER h hh i j w => ?_⟩
  have hΓ1 : (1 : ℝ) ≤ max 1 η⁻¹ := le_max_left _ _
  have hX : (Matrix.of (setEntry h i j w) + lam D N A).IsHermitian :=
    (Cmp_setEntry_herm h hh i j w).add (lam_isHermitian D N A)
  have := H D N A η hη F hF E₁ E₂ h hh i j w (max (CF 6) 1 * (1 + R) ^ max (CF 6) 1)
    (max 1 η⁻¹) (max 1 η⁻¹) hΓ1 (by linarith) le_rfl ?_ ?_
  · simpa using this
  · intro k hk1 hk2
    refine Cmp_BF F CF hCF _ _ ?_ k hk1 (by omega)
    have : ‖fun m => edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j w)‖ ≤ R := by
      refine (pi_norm_le_iff_of_nonneg hR).mpr fun m => ?_
      rw [Real.norm_eq_abs]
      exact (edgeCount_abs_le D N A η (E₁ m) (E₂ m) hη (setEntry h i j w)
        (Cmp_setEntry_herm h hh i j w)).trans (hER m)
    linarith
  · intro r a b _ _
    have hz : (edgePt η E₁ E₂ r).im = η := by
      unfold edgePt
      split_ifs <;> simp
    have h1 := Cmp_entries_le _ hX (edgePt η E₁ E₂ r) η hη hz a b
    have h2 : η⁻¹ ≤ max 1 η⁻¹ := le_max_right _ _
    exact ⟨h1.1.trans h2, h1.2.trans h2⟩

/-- The integrand of `entryF2` at the entry `(i, j)` is integrable under the law of `H_t`, `t ≥ 0`:
it is a.s. equal to a continuous function and a.s. bounded. -/
private lemma Cmp_fij_int (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (ht : 0 ≤ t)
    (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η) {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (CF : ℕ → ℝ)
    (hCF : ∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l)
    (E₁ E₂ : Fin n → ℝ) (i j : Idx D N) :
    Integrable (fun h => wirt 1 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ))
      (h i j)) (ouMatLaw D N L t) := by
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  have hLL := hC' N L t ht
  have := hLL.prob
  obtain ⟨Kw, -, HKw⟩ := Cmp_wirt_bound n
  set Φ : (Idx D N → Idx D N → ℂ) → ℂ := fun h => ((edgeFn D N A η F E₁ E₂ (symArr h) : ℝ) : ℂ)
    with hΦd
  have hΦ : ContDiff ℝ ∞ Φ :=
    Complex.ofRealCLM.contDiff.comp
      (hF.comp (contDiff_pi.mpr fun m => edgeCount_contDiff D N A η (E₁ m) (E₂ m) hη))
  have hslice : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) =
        fun w => Φ (setEntry h i j w) := by
    intro h hh
    funext w
    simp only [hΦd, symArr_of_isHermitian _ (Cmp_setEntry_herm h hh i j w)]
  have hmeas : AEStronglyMeasurable (fun h => wirt 1 1
      (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) (h i j)) (ouMatLaw D N L t) :=
    (Cmp_wirt_continuous Φ hΦ i j).aestronglyMeasurable.congr
      (hLL.herm.mono fun h hh => by simp only [hslice h hh])
  set R : ℝ := ∑ m, ((D * N : ℕ) : ℝ) * |E₂ m - E₁ m| / η with hRd
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun m _ => by positivity
  have hER : ∀ m, ((D * N : ℕ) : ℝ) * |E₂ m - E₁ m| / η ≤ R := fun m =>
    Finset.single_le_sum (f := fun m => ((D * N : ℕ) : ℝ) * |E₂ m - E₁ m| / η)
      (fun m _ => by positivity) (Finset.mem_univ m)
  refine Integrable.of_bound hmeas
    (Kw * (max (CF 6) 1 * (1 + R) ^ max (CF 6) 1) * max 1 η⁻¹ * max 1 η⁻¹) ?_
  filter_upwards [hLL.herm] with h hh
  exact HKw D N A η hη F hF CF hCF E₁ E₂ R hR0 hER h hh i j _

/-- `E ℱ₂` as the expectation of the sum over the entries (`Cmp_fij_int`). -/
private lemma Cmp_entryF2_eq (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (ht : 0 ≤ t)
    (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η) {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (CF : ℕ → ℝ)
    (hCF : ∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l)
    (E₁ E₂ : Fin n → ℝ) :
    entryF2 (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t) =
      ∫ h, (∑ i, ∑ j, genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
        wirt 1 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) (h i j))
        ∂(ouMatLaw D N L t) := by
  have hI := Cmp_fij_int D N L t ht A η hη F hF CF hCF E₁ E₂
  unfold entryF2
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hI i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hI i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

/-- The weights of `ℱ₂` are at most `8`: `|κ'_{ij}((DN)⁻¹ - s_{ij})| ≤ 4 · 2` for `D, N ≥ 1`. -/
private lemma Cmp_weight_le (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (i j : Idx D N) :
    ‖genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ))‖ ≤ 8 := by
  have h1 : ‖genWt i j‖ ≤ 4 := by unfold genWt; split_ifs <;> norm_num
  have hDN : (1 : ℝ) ≤ ((D * N : ℕ) : ℝ) := by
    have : 1 ≤ D * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast this
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 : ‖(((D * N : ℕ) : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ hDN
  have h3 : ‖(varProf D N 1 i j : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold varProf
    split_ifs
    · rw [one_mul, sub_self, zero_mul, add_zero, abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ hNr
    · simp
  rw [norm_mul]
  calc ‖genWt i j‖ * ‖(((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)‖ ≤ 4 * (1 + 1) :=
        mul_le_mul h1 ((norm_sub_le _ _).trans (add_le_add h2 h3)) (norm_nonneg _) (by norm_num)
    _ = 8 := by norm_num

end Integrable

/-! ### The traces `X`, `Y` and the integrand of `ℱ₂` on the events -/

section Traces

variable {D N : ℕ}

/-- `D⁻¹ - E_a` is the diagonal matrix with entries `D⁻¹ - 1_{p₁ = a}`. -/
private lemma Cmp_diag_eq (a : Fin D) :
    ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a =
      Matrix.diagonal (fun p : Idx D N => ((D : ℂ))⁻¹ - if p.1 = a then 1 else 0) := by
  rw [Ea, Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]

/-- The entries of `D⁻¹ - E_a` are at most `1`. -/
private lemma Cmp_diag_le (a : Fin D) (p : Idx D N) :
    ‖((D : ℂ))⁻¹ - if p.1 = a then (1 : ℂ) else 0‖ ≤ 1 := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
    intro h0; subst h0; exact a.elim0)
  have hDi : ((D : ℂ))⁻¹ = (((D : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have hDi0 : 0 ≤ (D : ℝ)⁻¹ := by positivity
  have hDi1 : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
  split_ifs
  · rw [hDi, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_le]
    constructor <;> linarith
  · rw [hDi, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hDi0]
    exact hDi1

/-- The normalized trace of a matrix whose diagonal entries are at most `B ≥ 0`. -/
private lemma Cmp_ntr_le {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ p, ‖M p p‖ ≤ B) : ‖ntr M‖ ≤ B := by
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ‖M.trace‖ ≤ (Fintype.card ι : ℝ) * B := by
    calc ‖M.trace‖ ≤ ∑ p, ‖M p p‖ := norm_sum_le _ _
      _ ≤ ∑ _p : ι, B := Finset.sum_le_sum fun p _ => hB p
      _ = (Fintype.card ι : ℝ) * B := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · rw [h, Nat.cast_zero, _root_.inv_zero, zero_mul]; exact hB0
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast h
    calc ((Fintype.card ι : ℝ))⁻¹ * ‖M.trace‖ ≤ ((Fintype.card ι : ℝ))⁻¹ * ((Fintype.card ι) * B) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = B := by field_simp

/-- `|⟨Im G(z) (D⁻¹ - E_a)⟩| ≤ B` when the diagonal entries of `Im G(z)` are at most `B`. -/
private lemma Cmp_Y_le (X : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (a : Fin D) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ p, ‖imRes X z p p‖ ≤ B) : ‖edgeYterm D N X z a‖ ≤ B := by
  unfold edgeYterm
  rw [Cmp_diag_eq]
  refine Cmp_ntr_le _ B hB0 fun p => ?_
  rw [Matrix.mul_diagonal, norm_mul]
  exact (mul_le_mul (hB p) (Cmp_diag_le a p) (norm_nonneg _) hB0).trans (le_of_eq (mul_one B))

/-- The diagonal entries of `Im G` are `Im G_{pp}`. -/
private lemma Cmp_imRes_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (z : ℂ)
    (p : ι) : ‖imRes X z p p‖ = |(res X z p p).im| := by
  have e : imRes X z p p = (((res X z p p).im : ℝ) : ℂ) := by
    simp only [imRes, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
      smul_eq_mul]
    rw [show star (res X z p p) = starRingEnd ℂ (res X z p p) from rfl, Complex.sub_conj]
    field_simp
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]

/-- `|Im ⟨G(z)⟩| ≤ B` when the diagonal entries of `Im G(z)` are at most `B`. -/
private lemma Cmp_imtr_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (z : ℂ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ p, ‖imRes X z p p‖ ≤ B) : |(ntr (res X z)).im| ≤ B := by
  unfold ntr
  have hc : ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ))⁻¹ : ℝ) := by push_cast; rfl
  rw [hc, Complex.im_ofReal_mul, Matrix.trace, Complex.im_sum, abs_mul,
    abs_of_nonneg (by positivity)]
  have h1 : |∑ p, (Matrix.diag (res X z) p).im| ≤ (Fintype.card ι : ℝ) * B := by
    calc |∑ p, (Matrix.diag (res X z) p).im| ≤ ∑ p, |(Matrix.diag (res X z) p).im| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : ι, B := Finset.sum_le_sum fun p _ => by
          rw [Matrix.diag_apply, ← Cmp_imRes_diag]; exact hB p
      _ = (Fintype.card ι : ℝ) * B := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · rw [h, Nat.cast_zero, _root_.inv_zero, zero_mul]; exact hB0
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast h
    calc ((Fintype.card ι : ℝ))⁻¹ * |∑ p, (Matrix.diag (res X z) p).im|
        ≤ ((Fintype.card ι : ℝ))⁻¹ * ((Fintype.card ι) * B) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = B := by field_simp

/-- (4.16) [eq:roughXY] with `|Im ⟨G(z_k)⟩| ≤ B`, `Im z₁ = Im z₂ = η`: `|X(i, j; a)| ≤ B/η`. -/
private lemma Cmp_X_rough (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : X.IsHermitian) (z₁ z₂ : ℂ)
    (η : ℝ) (hη : 0 < η) (hz₁ : z₁.im = η) (hz₂ : z₂.im = η) (a : Fin D) (B : ℝ) (hB0 : 0 ≤ B)
    (h₁ : |(ntr (res X z₁)).im| ≤ B) (h₂ : |(ntr (res X z₂)).im| ≤ B) :
    ‖edgeXterm D N X z₁ z₂ a‖ ≤ B / η := by
  refine (edgeXterm_rough_le X hX z₁ z₂ (by rw [hz₁]; exact hη) (by rw [hz₂]; exact hη) a).trans ?_
  rw [hz₁, hz₂]
  have hB : 0 ≤ B / η := by positivity
  have hu : |(ntr (res X z₁)).im / η| ≤ B / η := by
    rw [abs_div, abs_of_pos hη]; exact div_le_div_of_nonneg_right h₁ hη.le
  have hv : |(ntr (res X z₂)).im / η| ≤ B / η := by
    rw [abs_div, abs_of_pos hη]; exact div_le_div_of_nonneg_right h₂ hη.le
  calc Real.sqrt ((ntr (res X z₁)).im / η * ((ntr (res X z₂)).im / η))
      ≤ Real.sqrt ((B / η) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        calc _ ≤ |(ntr (res X z₁)).im / η * ((ntr (res X z₂)).im / η)| := le_abs_self _
          _ = |(ntr (res X z₁)).im / η| * |(ntr (res X z₂)).im / η| := abs_mul _ _
          _ ≤ (B / η) * (B / η) := mul_le_mul hu hv (abs_nonneg _) hB
          _ = (B / η) ^ 2 := by ring
    _ = B / η := Real.sqrt_sq hB

/-- The block projection `E_a` has norm at most `1`. -/
private lemma Cmp_opNorm_Ea (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- The integrand of `ℱ₂` (`entryF2_integrand_le`) with `|X| ≤ P_X`, `|Y| ≤ P_Y` and
`|⟨(G - M) E_a⟩| ≤ P_G` at the `2n` points and their conjugates:
`≤ K B_F (D² P_X + D³ N P_Y P_G)`. -/
private lemma Cmp_F2_pt (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℕ, 2 ≤ D → ∀ N : ℕ, 1 ≤ N → ∀ (A : Matrix (Fin N) (Fin N) ℂ)
      (η : ℝ), 0 < η → ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ F → ∀ (E₁ E₂ : Fin n → ℝ)
      (h : Idx D N → Idx D N → ℂ), (Matrix.of h).IsHermitian → ∀ BF : ℝ,
      (∀ k : ℕ, 1 ≤ k → k ≤ 2 →
        ‖iteratedFDeriv ℝ k F (fun m => edgeCount D N A η (E₁ m) (E₂ m) h)‖ ≤ BF) →
      ∀ PX PY PG : ℝ, 0 ≤ PX → 0 ≤ PY → 0 ≤ PG →
      (∀ (r₁ r₂ : Fin n × Fin 2) (a : Fin D), ‖edgeXterm D N (Matrix.of h + lam D N A)
        (edgePt η E₁ E₂ r₁) (edgePt η E₁ E₂ r₂) a‖ ≤ PX) →
      (∀ (r : Fin n × Fin 2) (a : Fin D),
        ‖edgeYterm D N (Matrix.of h + lam D N A) (edgePt η E₁ E₂ r) a‖ ≤ PY) →
      (∀ (r : Fin n × Fin 2) (a : Fin D),
        ‖ntr ((res (Matrix.of h + lam D N A) (edgePt η E₁ E₂ r) -
          MExt (lam D N A) (edgePt η E₁ E₂ r)) * Ea D N a)‖ ≤ PG ∧
        ‖ntr ((res (Matrix.of h + lam D N A) (star (edgePt η E₁ E₂ r)) -
          MExt (lam D N A) (star (edgePt η E₁ E₂ r))) * Ea D N a)‖ ≤ PG) →
      ‖∑ i, ∑ j, genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
          wirt 1 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) (h i j)‖ ≤
        K * BF * ((D : ℝ) ^ 2 * PX + (D : ℝ) ^ 3 * N * (PY * PG)) := by
  obtain ⟨K2, hK2, H2⟩ := entryF2_integrand_le n
  refine ⟨K2 * (4 * (n : ℝ) ^ 2 + 4 * n + 1), by positivity, ?_⟩
  intro D hD N hN A η hη F hF E₁ E₂ h hh BF hBF PX PY PG hPX hPY hPG hX hY hG
  have hBF0 : 0 ≤ BF := (norm_nonneg _).trans (hBF 1 le_rfl (by norm_num))
  refine (H2 D hD N hN A η hη F hF E₁ E₂ h hh BF hBF).trans ?_
  have hS1 : ∑ r₁ : Fin n × Fin 2, ∑ r₂ : Fin n × Fin 2, ∑ a : Fin D,
      ‖edgeXterm D N (Matrix.of h + lam D N A) (edgePt η E₁ E₂ r₁) (edgePt η E₁ E₂ r₂) a‖ ≤
      ((n : ℝ) * 2) * ((n : ℝ) * 2) * D * PX := by
    calc _ ≤ ∑ _r₁ : Fin n × Fin 2, ∑ _r₂ : Fin n × Fin 2, ∑ _a : Fin D, PX :=
          Finset.sum_le_sum fun r₁ _ => Finset.sum_le_sum fun r₂ _ =>
            Finset.sum_le_sum fun a _ => hX r₁ r₂ a
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
          ring
  have hS2 : ∑ r : Fin n × Fin 2, ∑ a : Fin D,
      ‖edgeYterm D N (Matrix.of h + lam D N A) (edgePt η E₁ E₂ r) a‖ *
        (‖ntr ((res (Matrix.of h + lam D N A) (edgePt η E₁ E₂ r) -
            MExt (lam D N A) (edgePt η E₁ E₂ r)) * Ea D N a)‖ +
          ‖ntr ((res (Matrix.of h + lam D N A) (star (edgePt η E₁ E₂ r)) -
            MExt (lam D N A) (star (edgePt η E₁ E₂ r))) * Ea D N a)‖) ≤
      ((n : ℝ) * 2) * D * (PY * (PG + PG)) := by
    calc _ ≤ ∑ _r : Fin n × Fin 2, ∑ _a : Fin D, PY * (PG + PG) :=
          Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun a _ =>
            mul_le_mul (hY r a) (add_le_add (hG r a).1 (hG r a).2) (by positivity) hPY
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
          ring
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hDr : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have ha : 0 ≤ (D : ℝ) ^ 2 * PX := by positivity
  have hb : 0 ≤ (D : ℝ) ^ 3 * N * (PY * PG) := by positivity
  have key : (D : ℝ) * (((n : ℝ) * 2) * ((n : ℝ) * 2) * D * PX) +
      (D : ℝ) ^ 2 * N * (((n : ℝ) * 2) * D * (PY * (PG + PG))) ≤
      (4 * (n : ℝ) ^ 2 + 4 * n + 1) * ((D : ℝ) ^ 2 * PX + (D : ℝ) ^ 3 * N * (PY * PG)) := by
    have e : (D : ℝ) * (((n : ℝ) * 2) * ((n : ℝ) * 2) * D * PX) +
        (D : ℝ) ^ 2 * N * (((n : ℝ) * 2) * D * (PY * (PG + PG))) =
        4 * (n : ℝ) ^ 2 * ((D : ℝ) ^ 2 * PX) + 4 * n * ((D : ℝ) ^ 3 * N * (PY * PG)) := by ring
    rw [e]
    nlinarith [mul_nonneg hn ha, mul_nonneg (sq_nonneg (n : ℝ)) hb]
  calc K2 * BF * ((D : ℝ) * (∑ r₁ : Fin n × Fin 2, ∑ r₂ : Fin n × Fin 2, ∑ a : Fin D,
        ‖edgeXterm D N (Matrix.of h + lam D N A) (edgePt η E₁ E₂ r₁) (edgePt η E₁ E₂ r₂) a‖) +
      (D : ℝ) ^ 2 * N * (∑ r : Fin n × Fin 2, ∑ a : Fin D,
        ‖edgeYterm D N (Matrix.of h + lam D N A) (edgePt η E₁ E₂ r) a‖ *
          (‖ntr ((res (Matrix.of h + lam D N A) (edgePt η E₁ E₂ r) -
              MExt (lam D N A) (edgePt η E₁ E₂ r)) * Ea D N a)‖ +
            ‖ntr ((res (Matrix.of h + lam D N A) (star (edgePt η E₁ E₂ r)) -
              MExt (lam D N A) (star (edgePt η E₁ E₂ r))) * Ea D N a)‖)))
      ≤ K2 * BF * ((D : ℝ) * (((n : ℝ) * 2) * ((n : ℝ) * 2) * D * PX) +
        (D : ℝ) ^ 2 * N * (((n : ℝ) * 2) * D * (PY * (PG + PG)))) := by gcongr
    _ ≤ K2 * BF * ((4 * (n : ℝ) ^ 2 + 4 * n + 1) *
        ((D : ℝ) ^ 2 * PX + (D : ℝ) ^ 3 * N * (PY * PG))) := by gcongr
    _ = _ := by ring

end Traces


/-- The `2n` points `E_e(i) + iη` and their conjugates lie in `𝐃(1/4)` when `|E⁺| ≤ 21/10`,
`η = N^{-2/3-σ} ≤ 1/2` and the windows are within `N^{-2/3+σ}` of `E⁺`. -/
private lemma Cmp_points {n : ℕ} (N : ℕ) (hx1 : (1 : ℝ) ≤ N) (σ : ℝ) (hσ12 : σ < 1 / 12) (Ep : ℝ)
    (hEp : |Ep| ≤ 21 / 10) (hηh : (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) ≤ 1 / 2) (E₁ E₂ : Fin n → ℝ)
    (hwin : ∀ r : Fin n × Fin 2, |(if r.2 = 0 then E₁ r.1 else E₂ r.1) - Ep| ≤
      (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) (r : Fin n × Fin 2) :
    edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r ∈ specDom (1 / 4) N ∧
      star (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r) ∈ specDom (1 / 4) N := by
  have hx0 : (0 : ℝ) < N := by linarith
  have hη0 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) := Real.rpow_pos_of_pos hx0 _
  have hwlt : (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  set z := edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r with hz
  have hzim : z.im = (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) := by rw [hz]; unfold edgePt; simp
  have hre : z.re = (if r.2 = 0 then E₁ r.1 else E₂ r.1) := by rw [hz]; unfold edgePt; simp
  have hE : |(if r.2 = 0 then E₁ r.1 else E₂ r.1)| ≤ 31 / 10 := by
    have := abs_sub_abs_le_abs_sub (if r.2 = 0 then E₁ r.1 else E₂ r.1) Ep
    linarith [hwin r]
  have hn : ‖z‖ ≤ (1 / 4 : ℝ)⁻¹ := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hre, hzim, abs_of_pos hη0]
    have : ((1 / 4 : ℝ))⁻¹ = 4 := by norm_num
    rw [this]
    linarith
  have hexp : (-1 + 1 / 4 : ℝ) ≤ -(2 / 3 : ℝ) - σ := by linarith
  have hi : (N : ℝ) ^ (-1 + 1 / 4 : ℝ) ≤ |z.im| := by
    rw [hzim, abs_of_pos hη0]
    exact Real.rpow_le_rpow_of_exponent_le hx1 hexp
  have hn' : ‖star z‖ ≤ (1 / 4 : ℝ)⁻¹ := by rw [Complex.star_def, Complex.norm_conj]; exact hn
  have hi' : (N : ℝ) ^ (-1 + 1 / 4 : ℝ) ≤ |(star z).im| := by
    rw [Complex.star_def, Complex.conj_im, abs_neg]; exact hi
  exact ⟨⟨hn, hi⟩, ⟨hn', hi'⟩⟩

/-- On the local-law events (|A| ≤ K_r N^{2σ+σ/2} and (2.23) [eq:aver_local] with loss
`N^{σ/2}` at the `2n` points and their conjugates), with `|X| ≤ K₀ N^{e₁}`, `|Y| ≤ K₀ N^{e₂}`,
`e₁ ≤ e₀` and `1 + e₂ + (-1/3 + σ + σ/2) ≤ e₀`, the integrand of `ℱ₂` is at most
`K C_* (1 + K_r)^{C_*} (D² + D³) K₀ N^{(2σ+σ/2)C_* + e₀}`, `C_* = max(C_6, 1)`. -/
private lemma Cmp_event_bound (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℕ, 2 ≤ D → ∀ N : ℕ, 1 ≤ N → ∀ (A : Matrix (Fin N) (Fin N) ℂ)
      (σ : ℝ), 0 < σ → ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ F → ∀ CF : ℕ → ℝ,
      (∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l) →
      ∀ (E₁ E₂ : Fin n → ℝ) (h : Idx D N → Idx D N → ℂ), (Matrix.of h).IsHermitian →
      ∀ (K₀ Kr e₀ e₁ e₂ : ℝ), 0 ≤ K₀ → 0 < Kr → e₁ ≤ e₀ →
      1 + e₂ + (-(1 / 3 : ℝ) + σ + σ / 2) ≤ e₀ →
      (∀ (r₁ r₂ : Fin n × Fin 2) (a : Fin D), ‖edgeXterm D N (Matrix.of h + lam D N A)
        (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r₁)
        (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r₂) a‖ ≤ K₀ * (N : ℝ) ^ e₁) →
      (∀ (r : Fin n × Fin 2) (a : Fin D), ‖edgeYterm D N (Matrix.of h + lam D N A)
        (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r) a‖ ≤ K₀ * (N : ℝ) ^ e₂) →
      (∀ (r : Fin n × Fin 2) (a : Fin D),
        ‖ntr ((res (Matrix.of h + lam D N A) (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r) -
          MExt (lam D N A) (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r)) * Ea D N a)‖ ≤
            (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2) ∧
        ‖ntr ((res (Matrix.of h + lam D N A)
            (star (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r)) -
          MExt (lam D N A) (star (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r))) * Ea D N a)‖ ≤
            (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)) →
      (∀ m, |edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) (E₁ m) (E₂ m) h| ≤
        Kr * (N : ℝ) ^ (2 * σ + σ / 2)) →
      ‖∑ i, ∑ j, genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
          wirt 1 1 (fun w => (edgeFn D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) F E₁ E₂
            (setEntry h i j w) : ℂ)) (h i j)‖ ≤
        K * (max (CF 6) 1 * (1 + Kr) ^ max (CF 6) 1) * ((D : ℝ) ^ 2 + (D : ℝ) ^ 3) * K₀ *
          (N : ℝ) ^ ((2 * σ + σ / 2) * max (CF 6) 1 + e₀) := by
  obtain ⟨Kp, hKp, HKp⟩ := Cmp_F2_pt n
  refine ⟨Kp, hKp, ?_⟩
  intro D hD N hN1 A σ hσ F hF CF hCF E₁ E₂ h hh K₀ Kr e₀ e₁ e₂ hK₀ hKr he₁ he₂ hX hY hG hcnt
  have hx0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hη0 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) := Real.rpow_pos_of_pos hx0 _
  set Cs : ℝ := max (CF 6) 1 with hCsd
  have hCs1 : (1 : ℝ) ≤ Cs := le_max_right _ _
  have hp1 : 1 ≤ (N : ℝ) ^ (2 * σ + σ / 2) := Real.one_le_rpow hx1 (by positivity)
  have hBF : ∀ k : ℕ, 1 ≤ k → k ≤ 2 → ‖iteratedFDeriv ℝ k F
      (fun m => edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) (E₁ m) (E₂ m) h)‖ ≤
      Cs * ((1 + Kr) * (N : ℝ) ^ (2 * σ + σ / 2)) ^ Cs := by
    intro k hk1 hk2
    refine Cmp_BF F CF hCF _ _ ?_ k hk1 (by omega)
    have : ‖fun m => edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) (E₁ m) (E₂ m) h‖ ≤
        Kr * (N : ℝ) ^ (2 * σ + σ / 2) :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun m => by
        rw [Real.norm_eq_abs]; exact hcnt m
    nlinarith
  have hmain := HKp D hD N hN1 A _ hη0 F hF E₁ E₂ h hh _ hBF (K₀ * (N : ℝ) ^ e₁)
    (K₀ * (N : ℝ) ^ e₂) ((N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)) (by positivity) (by positivity)
    (by positivity) hX hY hG
  refine hmain.trans ?_
  have hBFe : ((1 + Kr) * (N : ℝ) ^ (2 * σ + σ / 2)) ^ Cs =
      (1 + Kr) ^ Cs * (N : ℝ) ^ ((2 * σ + σ / 2) * Cs) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hx0.le]
  have i1 : K₀ * (N : ℝ) ^ e₁ ≤ K₀ * (N : ℝ) ^ e₀ :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 he₁) hK₀
  have i2 : (N : ℝ) * (K₀ * (N : ℝ) ^ e₂ * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)) ≤
      K₀ * (N : ℝ) ^ e₀ := by
    have e : (N : ℝ) * (K₀ * (N : ℝ) ^ e₂ * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)) =
        K₀ * (N : ℝ) ^ (1 + e₂ + (-(1 / 3 : ℝ) + σ + σ / 2)) := by
      rw [Real.rpow_add hx0 (1 + e₂) (-(1 / 3 : ℝ) + σ + σ / 2), Real.rpow_add hx0 1 e₂,
        Real.rpow_one]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 he₂) hK₀
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have inner : (D : ℝ) ^ 2 * (K₀ * (N : ℝ) ^ e₁) + (D : ℝ) ^ 3 * N *
      (K₀ * (N : ℝ) ^ e₂ * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)) ≤
      ((D : ℝ) ^ 2 + (D : ℝ) ^ 3) * (K₀ * (N : ℝ) ^ e₀) := by
    have e : (D : ℝ) ^ 3 * N * (K₀ * (N : ℝ) ^ e₂ * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)) =
        (D : ℝ) ^ 3 * ((N : ℝ) * (K₀ * (N : ℝ) ^ e₂ * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2))) := by
      ring
    rw [e, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left i1 (by positivity))
      (mul_le_mul_of_nonneg_left i2 (by positivity))
  have hBF0 : 0 ≤ Kp * (Cs * ((1 + Kr) * (N : ℝ) ^ (2 * σ + σ / 2)) ^ Cs) := by positivity
  calc Kp * (Cs * ((1 + Kr) * (N : ℝ) ^ (2 * σ + σ / 2)) ^ Cs) *
        ((D : ℝ) ^ 2 * (K₀ * (N : ℝ) ^ e₁) + (D : ℝ) ^ 3 * N *
          (K₀ * (N : ℝ) ^ e₂ * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)))
      ≤ Kp * (Cs * ((1 + Kr) * (N : ℝ) ^ (2 * σ + σ / 2)) ^ Cs) *
        (((D : ℝ) ^ 2 + (D : ℝ) ^ 3) * (K₀ * (N : ℝ) ^ e₀)) :=
        mul_le_mul_of_nonneg_left inner hBF0
    _ = _ := by
      rw [hBFe, Real.rpow_add hx0 ((2 * σ + σ / 2) * Cs) e₀]
      ring

/-- Off the local-law events, for a Hermitian array, the integrand of `ℱ₂` is at most
`8 D² K_w C_* (1 + 2D)^{C_*} N^{2 + (1+2σ)C_* + 2(2/3+σ)}` (`Cmp_wirt_bound` with
`R = 2D N^{1+2σ}`, `η = N^{-2/3-σ} ≤ 1`, and `Cmp_weight_le`). -/
private lemma Cmp_bad_bound (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℕ, 1 ≤ D → ∀ N : ℕ, 1 ≤ N → ∀ (A : Matrix (Fin N) (Fin N) ℂ)
      (σ : ℝ), 0 < σ → ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ F → ∀ CF : ℕ → ℝ,
      (∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l) →
      ∀ (E₁ E₂ : Fin n → ℝ) (Ep : ℝ), (∀ m, |E₁ m - Ep| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
      (∀ m, |E₂ m - Ep| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
      ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      ‖∑ i, ∑ j, genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
          wirt 1 1 (fun w => (edgeFn D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) F E₁ E₂
            (setEntry h i j w) : ℂ)) (h i j)‖ ≤
        8 * (D : ℝ) ^ 2 * K * (max (CF 6) 1 * (1 + 2 * (D : ℝ)) ^ max (CF 6) 1) *
          (N : ℝ) ^ (2 + (1 + 2 * σ) * max (CF 6) 1 + (2 / 3 + σ) + (2 / 3 + σ)) := by
  obtain ⟨Kw, hKw, HKw⟩ := Cmp_wirt_bound n
  refine ⟨Kw, hKw, ?_⟩
  intro D hD N hN1 A σ hσ F hF CF hCF E₁ E₂ Ep hE₁ hE₂ h hh
  have hx0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hη0 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) := Real.rpow_pos_of_pos hx0 _
  set Cs : ℝ := max (CF 6) 1 with hCsd
  have hCs1 : (1 : ℝ) ≤ Cs := le_max_right _ _
  have hηinv : ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ))⁻¹ = (N : ℝ) ^ (2 / 3 + σ) := by
    rw [← Real.rpow_neg hx0.le]; congr 1; ring
  have hR0 : 0 ≤ 2 * (D : ℝ) * (N : ℝ) ^ (1 + 2 * σ) := by positivity
  have hER : ∀ m, ((D * N : ℕ) : ℝ) * |E₂ m - E₁ m| / (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) ≤
      2 * (D : ℝ) * (N : ℝ) ^ (1 + 2 * σ) := by
    intro m
    have hd : |E₂ m - E₁ m| ≤ 2 * (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) := by
      calc |E₂ m - E₁ m| ≤ |E₂ m - Ep| + |Ep - E₁ m| := abs_sub_le _ _ _
        _ ≤ _ := by rw [abs_sub_comm Ep]; linarith [hE₁ m, hE₂ m]
    rw [div_eq_mul_inv, hηinv]
    push_cast
    calc (D : ℝ) * N * |E₂ m - E₁ m| * (N : ℝ) ^ (2 / 3 + σ)
        ≤ (D : ℝ) * N * (2 * (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) * (N : ℝ) ^ (2 / 3 + σ) := by gcongr
      _ = 2 * (D : ℝ) * ((N : ℝ) * ((N : ℝ) ^ (-(2 / 3 : ℝ) + σ) * (N : ℝ) ^ (2 / 3 + σ))) := by
          ring
      _ = 2 * (D : ℝ) * (N : ℝ) ^ (1 + 2 * σ) := by
          rw [← Real.rpow_add hx0, Cmp_mul_rpow _ _ hx0]; congr 3; ring
  have hmax : max 1 ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ))⁻¹ = (N : ℝ) ^ (2 / 3 + σ) := by
    rw [hηinv]; exact max_eq_right (Real.one_le_rpow hx1 (by linarith))
  have h1R : (1 + 2 * (D : ℝ) * (N : ℝ) ^ (1 + 2 * σ)) ^ Cs ≤
      (1 + 2 * (D : ℝ)) ^ Cs * (N : ℝ) ^ ((1 + 2 * σ) * Cs) := by
    have hp : 1 ≤ (N : ℝ) ^ (1 + 2 * σ) := Real.one_le_rpow hx1 (by linarith)
    calc (1 + 2 * (D : ℝ) * (N : ℝ) ^ (1 + 2 * σ)) ^ Cs
        ≤ ((1 + 2 * (D : ℝ)) * (N : ℝ) ^ (1 + 2 * σ)) ^ Cs :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hx0.le]
  set W : ℝ := Kw * (Cs * (1 + 2 * (D : ℝ) * (N : ℝ) ^ (1 + 2 * σ)) ^ Cs) *
    (N : ℝ) ^ (2 / 3 + σ) * (N : ℝ) ^ (2 / 3 + σ) with hWd
  have hterm : ∀ i j : Idx D N, ‖genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
      wirt 1 1 (fun w => (edgeFn D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) F E₁ E₂
        (setEntry h i j w) : ℂ)) (h i j)‖ ≤ 8 * W := by
    intro i j
    have hw := HKw D N A _ hη0 F hF CF hCF E₁ E₂ _ hR0 hER h hh i j (h i j)
    rw [hmax] at hw
    rw [norm_mul]
    exact mul_le_mul (Cmp_weight_le D N hD hN1 i j) hw (norm_nonneg _) (by norm_num)
  have hW0 : 0 ≤ W := by positivity
  calc _ ≤ ∑ _i : Idx D N, ∑ _j : Idx D N, 8 * W :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm i j))
    _ = ((D : ℝ) * N) ^ 2 * (8 * W) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_mul]
        ring
    _ ≤ ((D : ℝ) * N) ^ 2 * (8 * (Kw * (Cs * ((1 + 2 * (D : ℝ)) ^ Cs *
          (N : ℝ) ^ ((1 + 2 * σ) * Cs))) * (N : ℝ) ^ (2 / 3 + σ) * (N : ℝ) ^ (2 / 3 + σ))) := by
        rw [hWd]; gcongr
    _ = _ := by
        rw [Real.rpow_add hx0 (2 + (1 + 2 * σ) * Cs + (2 / 3 + σ)) (2 / 3 + σ),
          Real.rpow_add hx0 (2 + (1 + 2 * σ) * Cs) (2 / 3 + σ),
          Real.rpow_add hx0 2 ((1 + 2 * σ) * Cs), Real.rpow_two]
        ring

/-- `‖Λ‖ ≤ 2‖A‖` is small and `|E⁺| ≤ 21/10` once `N^{δ_A} ≥ 20(1 + C_e)`, with `C_e` of
(A.2) [edge_close_to_edge_sc]. -/
private lemma Cmp_Eplus_le (D N : ℕ) [Nonempty (Idx D N)] (A : Matrix (Fin N) (Fin N) ℂ)
    (δA Ce : ℝ) (hCe : 0 < Ce)
    (HCe : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → |2 - Eplus Λ| + |2 + Eminus Λ| ≤ Ce * opNorm Λ)
    (hx0 : (0 : ℝ) < N) (hA : opNorm A ≤ (N : ℝ) ^ (-δA)) (hN : 20 * (1 + Ce) ≤ (N : ℝ) ^ δA) :
    |Eplus (lam D N A)| ≤ 21 / 10 := by
  have h2 : opNorm (lam D N A) ≤ 2 * (N : ℝ) ^ (-δA) := (opNorm_lam_le D N A).trans (by linarith)
  have h3 : (N : ℝ) ^ (-δA) = ((N : ℝ) ^ δA)⁻¹ := Real.rpow_neg hx0.le _
  have hp : 0 < (N : ℝ) ^ δA := Real.rpow_pos_of_pos hx0 _
  have h4 : (N : ℝ) ^ (-δA) * (20 * (1 + Ce)) ≤ 1 := by
    rw [h3, inv_mul_le_iff₀ hp]; linarith
  have hop0 : 0 ≤ opNorm (lam D N A) := norm_nonneg _
  have h5 : 0 ≤ (N : ℝ) ^ (-δA) := Real.rpow_nonneg hx0.le _
  have hl1 : opNorm (lam D N A) ≤ 1 / 10 := by nlinarith
  have hl2 : Ce * opNorm (lam D N A) ≤ 1 / 10 := by nlinarith
  have h1 := HCe (Idx D N) (lam D N A) (lam_isHermitian D N A) hl1
  have h6 : |2 - Eplus (lam D N A)| ≤ 1 / 10 := by
    linarith [abs_nonneg (2 + Eminus (lam D N A))]
  rw [abs_le] at h6 ⊢
  constructor <;> linarith

/-- `η = N^{-2/3-σ} ≤ 1/2` once `N^{2/3} ≥ 2`. -/
private lemma Cmp_eta_le (N : ℕ) (hx1 : (1 : ℝ) ≤ N) (σ : ℝ) (hσ : 0 < σ)
    (h2 : (2 : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ)) : (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) ≤ 1 / 2 := by
  have hx0 : (0 : ℝ) < N := by linarith
  have e1 : (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have e2 : (N : ℝ) ^ (-(2 / 3 : ℝ)) = ((N : ℝ) ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg hx0.le _
  have e4 : ((N : ℝ) ^ (2 / 3 : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-- (2.23) [eq:aver_local] with loss `N^{σ/2}` on `𝐃(1/4)` gives
`|⟨(G - M) E_a⟩| ≤ N^{-1/3+σ+σ/2}` at the `2n` points `E_e(i) + iη` and their conjugates. -/
private lemma Cmp_PG {n : ℕ} (D N : ℕ) (hx1 : (1 : ℝ) ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (σ : ℝ) (hσ12 : σ < 1 / 12) (Ep : ℝ) (hEp : |Ep| ≤ 21 / 10)
    (hηh : (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) ≤ 1 / 2) (E₁ E₂ : Fin n → ℝ)
    (hwin : ∀ r : Fin n × Fin 2, |(if r.2 = 0 then E₁ r.1 else E₂ r.1) - Ep| ≤
      (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) (h : Idx D N → Idx D N → ℂ)
    (hG : ∀ (a : Fin D) (z : ℂ), z ∈ specDom (1 / 4) N →
      ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) * Ea D N a)‖ ≤
        (N : ℝ) ^ (σ / 2) * (1 / ((N : ℝ) * |z.im|)))
    (r : Fin n × Fin 2) (a : Fin D) :
    ‖ntr ((res (Matrix.of h + lam D N A) (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r) -
        MExt (lam D N A) (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r)) * Ea D N a)‖ ≤
          (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2) ∧
      ‖ntr ((res (Matrix.of h + lam D N A)
          (star (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r)) -
        MExt (lam D N A) (star (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r))) * Ea D N a)‖ ≤
          (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2) := by
  have hx0 : (0 : ℝ) < N := by linarith
  have hη0 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) := Real.rpow_pos_of_pos hx0 _
  have hzim : (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r).im =
      (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) := by unfold edgePt; simp
  have hPGe : (N : ℝ) ^ (σ / 2) * (1 / ((N : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ) - σ))) =
      (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2) := by
    rw [Cmp_mul_rpow _ _ hx0, one_div, ← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]
    congr 1; ring
  have hz := Cmp_points N hx1 σ hσ12 Ep hEp hηh E₁ E₂ hwin r
  have h1 := hG a _ hz.1
  have h2 := hG a _ hz.2
  have a1 : |(edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r).im| =
      (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) := by rw [hzim, abs_of_pos hη0]
  have a2 : |(star (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r)).im| =
      (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) := by
    rw [Complex.star_def, Complex.conj_im, abs_neg, hzim, abs_of_pos hη0]
  rw [a1, hPGe] at h1
  rw [a2, hPGe] at h2
  exact ⟨h1, h2⟩

/-- The integrand of `ℱ₂` on the local-law events without the eigenvector bound: with
`|(Im G)_{pp}| ≤ K_e N^{-1/3+σ+σ/2}` at the `2n` points ((4.13)
[single_resolvent_local_law_bound2]) and (4.16) [eq:roughXY], it is at most
`K C_* (1 + K_r)^{C_*} (D² + D³) K_e N^{(2σ+σ/2)C_* + 1/3 + 3σ}`. -/
private lemma Cmp_mid_bound (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℕ, 2 ≤ D → ∀ N : ℕ, 1 ≤ N → ∀ (A : Matrix (Fin N) (Fin N) ℂ)
      (σ : ℝ), 0 < σ → σ < 1 / 12 → ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ F → ∀ CF : ℕ → ℝ,
      (∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l) →
      ∀ (E₁ E₂ : Fin n → ℝ) (Ep : ℝ), |Ep| ≤ 21 / 10 →
      (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) ≤ 1 / 2 →
      (∀ r : Fin n × Fin 2, |(if r.2 = 0 then E₁ r.1 else E₂ r.1) - Ep| ≤
        (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
      ∀ (Ke Kr : ℝ), 0 < Ke → 0 < Kr →
      ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      (∀ (a : Fin D) (z : ℂ), z ∈ specDom (1 / 4) N →
        ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) * Ea D N a)‖ ≤
          (N : ℝ) ^ (σ / 2) * (1 / ((N : ℝ) * |z.im|))) →
      (∀ E : ℝ, |E - Ep| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) → ∀ p q : Idx D N,
        ‖imRes (Matrix.of h + lam D N A)
          ((E : ℂ) + (((N : ℝ) ^ (-(2 / 3 : ℝ) - σ) : ℝ) : ℂ) * Complex.I) p q‖ ≤
            Ke * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2)) →
      (∀ m, |edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) (E₁ m) (E₂ m) h| ≤
        Kr * (N : ℝ) ^ (2 * σ + σ / 2)) →
      ‖∑ i, ∑ j, genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
          wirt 1 1 (fun w => (edgeFn D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) F E₁ E₂
            (setEntry h i j w) : ℂ)) (h i j)‖ ≤
        K * (max (CF 6) 1 * (1 + Kr) ^ max (CF 6) 1) * ((D : ℝ) ^ 2 + (D : ℝ) ^ 3) * Ke *
          (N : ℝ) ^ ((2 * σ + σ / 2) * max (CF 6) 1 + ((1 / 3 : ℝ) + 2 * σ + σ)) := by
  obtain ⟨Kp, hKp, HKp⟩ := Cmp_event_bound n
  refine ⟨Kp, hKp, ?_⟩
  intro D hD N hN1 A σ hσ hσ12 F hF CF hCF E₁ E₂ Ep hEp hηh hwin Ke Kr hKe hKr h hh hG him hc
  have hx0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hη0 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) := Real.rpow_pos_of_pos hx0 _
  have hηinv : ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ))⁻¹ = (N : ℝ) ^ (2 / 3 + σ) := by
    rw [← Real.rpow_neg hx0.le]; congr 1; ring
  have hzim : ∀ r, (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r).im =
      (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) := by
    intro r; unfold edgePt; simp
  have hX := hh.add (lam_isHermitian D N A)
  have himr : ∀ (r : Fin n × Fin 2) (p : Idx D N), ‖imRes (Matrix.of h + lam D N A)
      (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r) p p‖ ≤
        Ke * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2) := fun r p => him _ (hwin r) p p
  have hB0 : 0 ≤ Ke * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2) := by positivity
  have hXe : Ke * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2) / (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) =
      Ke * (N : ℝ) ^ ((1 / 3 : ℝ) + 2 * σ + σ / 2) := by
    rw [div_eq_mul_inv, hηinv, mul_assoc, ← Real.rpow_add hx0]; congr 2; ring
  have hXm : ∀ (r₁ r₂ : Fin n × Fin 2) (a : Fin D), ‖edgeXterm D N (Matrix.of h + lam D N A)
      (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r₁)
      (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r₂) a‖ ≤
        Ke * (N : ℝ) ^ ((1 / 3 : ℝ) + 2 * σ + σ / 2) := by
    intro r₁ r₂ a
    rw [← hXe]
    exact Cmp_X_rough _ hX _ _ _ hη0 (hzim r₁) (hzim r₂) a _ hB0
      (Cmp_imtr_le _ _ _ hB0 (himr r₁)) (Cmp_imtr_le _ _ _ hB0 (himr r₂))
  have hYm : ∀ (r : Fin n × Fin 2) (a : Fin D), ‖edgeYterm D N (Matrix.of h + lam D N A)
      (edgePt ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ r) a‖ ≤
        Ke * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + σ / 2) :=
    fun r a => Cmp_Y_le _ _ a _ hB0 (himr r)
  have he₁ : (1 / 3 : ℝ) + 2 * σ + σ / 2 ≤ (1 / 3 : ℝ) + 2 * σ + σ := by linarith
  have he₂ : 1 + (-(1 / 3 : ℝ) + σ + σ / 2) + (-(1 / 3 : ℝ) + σ + σ / 2) ≤
      (1 / 3 : ℝ) + 2 * σ + σ := by linarith
  exact HKp D hD N hN1 A σ hσ F hF CF hCF E₁ E₂ h hh Ke Kr _ _ _ hKe.le hKr he₁ he₂ hXm hYm
    (Cmp_PG D N hx1 A σ hσ12 Ep hEp hηh E₁ E₂ hwin h hG) hc

/-- (4.21) [eq:F2]: there is `c ∈ (0, 1]` (the exponent of (3.4) [eq:extend:main_evector1] for
`H_t`) such that for `F` with (4.6) [derivative_bound_F], `σ ∈ (0, 1/12)` and `2σ ≤ ε < c`,
uniformly in `t ∈ [0, 1/2]`, `L`, `A` with (2.4) [eq:condA1] at `k = 1` and the windows within
`N^{-2/3+σ}` of `E⁺`, `|E ℱ₂| ≤ N^{1/3 - c/3 + (3 + 3C_*)σ + 3ε}`, `C_* = max(C_6, 1)`,
`η = N^{-2/3-σ}`. -/
theorem edgeF2_expect_le (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (C : ℕ → ℝ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (n : ℕ) (F : (Fin n → ℝ) → ℝ) (CF : ℕ → ℝ), ContDiff ℝ ∞ F →
      (∀ l k : ℕ, 1 ≤ k → k ≤ l → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ CF l * (1 + ‖x‖) ^ CF l) →
    ∀ σ ε : ℝ, 0 < σ → σ < 1 / 12 → 2 * σ ≤ ε → ε < c →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t → t ≤ 1 / 2 →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      (N : ℝ) ^ ((1 / 3 : ℝ) + εA) ≤ hsNorm A → ∀ E₁ E₂ : Fin n → ℝ,
      (∀ m, |E₁ m - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
      (∀ m, |E₂ m - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ)) →
        ‖entryF2 (edgeFn D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) F E₁ E₂) (ouMatLaw D N L t)‖ ≤
          (N : ℝ) ^ ((1 / 3 : ℝ) - c / 3 + (3 + 3 * max (CF 6) 1) * σ + 3 * ε) := by
  obtain ⟨cQ, hcQ, NQ, hQ⟩ := evec_window D hD δA εA hδA hεA C
  obtain ⟨c, hcd⟩ : ∃ c : ℝ, c = min cQ 1 := ⟨_, rfl⟩
  have hc0 : 0 < c := hcd ▸ lt_min hcQ one_pos
  have hc1 : c ≤ 1 := hcd ▸ min_le_right _ _
  have hccQ : c ≤ cQ := hcd ▸ min_le_left _ _
  refine ⟨c, hc0, hc1, ?_⟩
  intro n F CF hF hCF σ ε hσ hσ12 hσε hεc
  obtain ⟨Cs, hCsd⟩ : ∃ Cs : ℝ, Cs = max (CF 6) 1 := ⟨_, rfl⟩
  rw [← hCsd]
  have hCs1 : (1 : ℝ) ≤ Cs := hCsd ▸ le_max_right _ _
  have hτ0 : 0 < σ / 2 := by positivity
  have hτσ : σ / 2 < 2 * σ := by linarith
  have hε0 : 0 < ε := by linarith
  obtain ⟨Kp, hKp, HKp⟩ := Cmp_event_bound n
  obtain ⟨Kd, hKd, HKd⟩ := Cmp_mid_bound n
  obtain ⟨Kw, hKw, HKw⟩ := Cmp_bad_bound n
  obtain ⟨Ks, hKs, HKs⟩ := edgeSpec_le D hD δA hδA
  obtain ⟨Ke, hKe, HKe⟩ := edgeRes_entry_le D hD δA hδA C
  obtain ⟨Kr, hKr, HKr⟩ := edgeCount_rough D hD δA hδA C
  obtain ⟨Ce, hCe, HCe⟩ := edge_close_to_edge_sc
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  -- the exponents: target, good event, eigenvector failure, local-law failure
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = (1 / 3 : ℝ) - c / 3 + (3 + 3 * Cs) * σ + 3 * ε := ⟨_, rfl⟩
  rw [← hTd]
  obtain ⟨eg, hegd⟩ : ∃ e : ℝ, e = (2 * σ + σ / 2) * Cs + ((1 / 3 : ℝ) - c / 3 + 2 * σ + 2 * ε) :=
    ⟨_, rfl⟩
  obtain ⟨em, hemd⟩ : ∃ e : ℝ, e = (2 * σ + σ / 2) * Cs + ((1 / 3 : ℝ) + 2 * σ + σ) := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ e : ℝ, e = 2 + (1 + 2 * σ) * Cs + (2 / 3 + σ) + (2 / 3 + σ) := ⟨_, rfl⟩
  have hD'0 : 0 < b + 1 := by rw [hbd]; nlinarith
  have hCsσ : 0 ≤ Cs * σ := by nlinarith
  have hTg : eg < T := by rw [hegd, hTd]; nlinarith
  have hTm : em + -c < T := by rw [hemd, hTd]; nlinarith
  have hTb : (-1 : ℝ) < T := by rw [hTd]; nlinarith
  -- the constants
  obtain ⟨Kg, hKgd⟩ : ∃ K : ℝ, K = Kp * (Cs * (1 + Kr) ^ Cs) * ((D : ℝ) ^ 2 + (D : ℝ) ^ 3) * Ks :=
    ⟨_, rfl⟩
  obtain ⟨Km, hKmd⟩ : ∃ K : ℝ, K = Kd * (Cs * (1 + Kr) ^ Cs) * ((D : ℝ) ^ 2 + (D : ℝ) ^ 3) * Ke :=
    ⟨_, rfl⟩
  obtain ⟨Kb, hKbd⟩ : ∃ K : ℝ, K = 8 * (D : ℝ) ^ 2 * Kw * (Cs * (1 + 2 * (D : ℝ)) ^ Cs) :=
    ⟨_, rfl⟩
  -- the thresholds
  obtain ⟨Ns, HNs⟩ := HKs c σ ε (σ / 2) hc0 hc1 hσ hσ12 hσε hεc hτ0 hτσ
  obtain ⟨Nl, HNl⟩ := samefort_local D (by omega) δA (1 / 4) hδA (by norm_num) C (σ / 2) hτ0
    (b + 1) hD'0
  obtain ⟨Ne, HNe⟩ := HKe σ hσ hσ12 (σ / 2) hτ0 (b + 1) hD'0
  obtain ⟨Nr, HNr⟩ := HKr σ hσ hσ12 (σ / 2) hτ0 (b + 1) hD'0
  obtain ⟨Na1, HNa1⟩ := Cmp_absorb Kg eg T hTg
  obtain ⟨Na2, HNa2⟩ := Cmp_absorb Km (em + -c) T hTm
  obtain ⟨Na3, HNa3⟩ := Cmp_absorb (Kb * ((D : ℝ) + 3)) (-1) T hTb
  obtain ⟨Nsm, HNsm⟩ := Cmp_ev (20 * (1 + Ce)) δA hδA
  obtain ⟨Nη, HNη⟩ := Cmp_ev 2 (2 / 3) (by norm_num)
  refine ⟨max (max (max NQ Ns) (max Nl Ne)) (max (max Nr Na1) (max (max Na2 Na3)
    (max (max Nsm Nη) 1))), ?_⟩
  intro N hN L t ht0 ht1 A hA hAhs E₁ E₂ hE₁ hE₂
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hNQ, hNs⟩, ⟨hNl, hNe⟩⟩, ⟨⟨hNr, hNa1⟩, ⟨⟨hNa2, hNa3⟩, ⟨⟨hNsm, hNη⟩, hN1⟩⟩⟩⟩ := hN
  have hx0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hLL := hC' N L t ht0
  have hprob := hLL.prob
  have hDN1 : 1 ≤ D * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hEp := Cmp_Eplus_le D N A δA Ce hCe HCe hx0 hA (HNsm N hNsm)
  have hηh := Cmp_eta_le N hx1 σ hσ (HNη N hNη)
  have hη0 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ) - σ) := Real.rpow_pos_of_pos hx0 _
  have hwin : ∀ r : Fin n × Fin 2, |(if r.2 = 0 then E₁ r.1 else E₂ r.1) - Eplus (lam D N A)| ≤
      (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) := by
    intro r; split_ifs; exacts [hE₁ _, hE₂ _]
  -- the events: rigidity, (2.23), (4.12)–(4.13), (4.8) (failure `≤ (D + 3) N^{-D'}`), and
  -- (3.4) at `k = 1` (failure `≤ N^{-c}`)
  have hR1 := (HNl N hNl L t ht0 A hA).2.2
  have hR2 := fun a : Fin D => (HNl N hNl L t ht0 A hA).2.1 (Ea D N a) (Cmp_opNorm_Ea a)
  have hR3 := HNe N hNe L t ht0 A hA
  have hR4 := HNr N hNr L t ht0 A hA
  have hT₂ := Cmp_union_le (ouMatLaw D N L t) D _ _ _ _ ((N : ℝ) ^ (-(b + 1)))
    (Real.rpow_nonneg hx0.le _) hR1 hR2 hR3 hR4
  have hhs1 : (N : ℝ) ^ ((1 / 3 : ℝ) + εA) * rk D N 1 ^ (-(1 / 3 : ℝ)) ≤ hsNorm A := by
    rw [rk_one D N hDN1, Real.one_rpow, mul_one]; exact hAhs
  have hT₁ := (hQ N hNQ L t ht0 ht1 A hA 1 le_rfl hDN1 hhs1).trans
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : -cQ ≤ -c)))
  have hKg0 : 0 ≤ Kg := by rw [hKgd]; positivity
  have hKm0 : 0 ≤ Km := by rw [hKmd]; positivity
  have hKb0 : 0 ≤ Kb := by rw [hKbd]; positivity
  -- (4.21) [eq:F2]
  rw [Cmp_entryF2_eq D N L t ht0 A _ hη0 F hF CF hCF E₁ E₂]
  refine (Cmp_int_le (ouMatLaw D N L t) _ _ _ (Kg * (N : ℝ) ^ eg) (Km * (N : ℝ) ^ em)
    (Kb * (N : ℝ) ^ b) ((N : ℝ) ^ (-c)) (((D : ℝ) + 3) * (N : ℝ) ^ (-(b + 1)))
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hT₁ hT₂
    ?_).trans ?_
  · filter_upwards [hLL.herm] with h hh
    refine ⟨?_, fun hx2 => ?_, fun hx1' hx2 => ?_⟩
    · -- off the local-law events
      have := HKw D (by omega) N hN1 A σ hσ F hF CF hCF E₁ E₂ _ hE₁ hE₂ h hh
      rw [← hCsd] at this
      rw [hKbd, hbd]
      exact this
    · -- on the local-law events
      simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hx2
      obtain ⟨⟨⟨-, n2⟩, n3⟩, n4⟩ := hx2
      have := HKd D hD N hN1 A σ hσ hσ12 F hF CF hCF E₁ E₂ _ hEp hηh hwin Ke Kr hKe hKr h hh
        (fun a z hz => not_lt.mp fun hlt => n2 a ⟨z, hz, hlt⟩)
        (fun E hE p q => not_lt.mp fun hlt => n3 ⟨E, hE, p, q, Or.inr hlt⟩)
        (fun m => not_lt.mp fun hlt => n4 ⟨E₁ m, E₂ m, hE₁ m, hE₂ m, hlt⟩)
      rw [← hCsd] at this
      rw [hKmd, hemd]
      exact this
    · -- on the local-law events and the eigenvector event
      simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hx2
      obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := hx2
      have hxc : (N : ℝ) ^ c ≤ (N : ℝ) ^ cQ := Real.rpow_le_rpow_of_exponent_le hx1 hccQ
      have hxc' : (N : ℝ) ^ (-cQ) ≤ (N : ℝ) ^ (-c) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hX := hh.add (lam_isHermitian D N A)
      have hS := HNs N hNs A hA _ hX (fun k hk1 hk2 => not_lt.mp fun hlt => n1 ⟨k, hk1, hk2, hlt⟩)
        (fun i j hi1 hi2 hj1 hj2 hi hj u w hu hw a => lt_of_lt_of_le
          (not_le.mp fun hle => hx1' ⟨i, j, hi1, hi2, hj1, hj2,
            by rw [Nat.cast_one]; exact hi.trans hxc, by rw [Nat.cast_one]; exact hj.trans hxc,
            u, w, hu, hw, a, hle⟩) hxc')
      have := HKp D hD N hN1 A σ hσ F hF CF hCF E₁ E₂ h hh Ks Kr
        ((1 / 3 : ℝ) - c / 3 + 2 * σ + 2 * ε) ((1 / 3 : ℝ) - c / 3 + 2 * σ + 2 * ε)
        (-(1 / 3 : ℝ) - c / 3 + σ + ε) hKs.le hKr le_rfl (by linarith)
        (fun r₁ r₂ a => (hS _ _ (hwin r₁) (hwin r₂) a).1)
        (fun r a => (hS _ _ (hwin r) (hwin r) a).2)
        (Cmp_PG D N hx1 A σ hσ12 _ hEp hηh E₁ E₂ hwin h
          (fun a z hz => not_lt.mp fun hlt => n2 a ⟨z, hz, hlt⟩))
        (fun m => not_lt.mp fun hlt => n4 ⟨E₁ m, E₂ m, hE₁ m, hE₂ m, hlt⟩)
      rw [← hCsd] at this
      rw [hKgd, hegd]
      exact this
  · have a1 := HNa1 N hNa1
    have a2 := HNa2 N hNa2
    have a3 := HNa3 N hNa3
    have e2 : Km * (N : ℝ) ^ em * (N : ℝ) ^ (-c) = Km * (N : ℝ) ^ (em + -c) := by
      rw [mul_assoc, ← Real.rpow_add hx0]
    have e3 : Kb * (N : ℝ) ^ b * (((D : ℝ) + 3) * (N : ℝ) ^ (-(b + 1))) =
        Kb * ((D : ℝ) + 3) * (N : ℝ) ^ (-1 : ℝ) := by
      have : (N : ℝ) ^ b * (N : ℝ) ^ (-(b + 1)) = (N : ℝ) ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      calc Kb * (N : ℝ) ^ b * (((D : ℝ) + 3) * (N : ℝ) ^ (-(b + 1))) =
          Kb * ((D : ℝ) + 3) * ((N : ℝ) ^ b * (N : ℝ) ^ (-(b + 1))) := by ring
        _ = _ := by rw [this]
    rw [e2, e3]
    linarith

/-- Lemma 4.3 [rescomY]: under (2.4) [eq:condA1] at `k = 1` there is `𝔠₀ > 0` such that for
`𝔠 ∈ (0, 𝔠₀]`, `𝔱 = N^{-1/3+𝔠}` and `F` with (4.6) [derivative_bound_F] there are `σ₀, δ > 0`
such that for `σ ∈ (0, σ₀)`, `η = N^{-2/3-σ}` and `E₁(i), E₂(i)` within `N^{-2/3+σ}` of `E⁺`, the
expectations in (4.7) [2comVVt] under `H_Λ` and `H_Λ(𝔱)` differ by at most `N^{-δ}`. -/
theorem rescomY (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA) (C : ℕ → ℝ) :
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
            ∂(ouMatLaw D N L (edgeTime N ct)))| ≤ (N : ℝ) ^ (-δ) := by
  obtain ⟨c, hc0, hc1, H1⟩ := edgeF2_expect_le D hD δA εA hδA hεA C
  refine ⟨min (c / 6) (1 / 20), lt_min (by positivity) (by norm_num), ?_⟩
  intro ct hct hctle n F CF hF hCF
  have hct1 : ct ≤ c / 6 := hctle.trans (min_le_left _ _)
  have hct2 : ct ≤ 1 / 20 := hctle.trans (min_le_right _ _)
  have hCs1 : (1 : ℝ) ≤ max (CF 6) 1 := le_max_right _ _
  refine ⟨c / (100 * (3 + 4 * max (CF 6) 1)), by positivity, c / 40, by positivity, ?_⟩
  intro σ hσ hσ0
  -- the exponents: `2σ ≤ ε < c`, `σ < 1/12`, and both exponents of `𝔱 |Φ'|` are `≤ -2δ`
  have hpos : (0 : ℝ) < 100 * (3 + 4 * max (CF 6) 1) := by positivity
  have h1 : σ * (100 * (3 + 4 * max (CF 6) 1)) < c := (lt_div_iff₀ hpos).mp hσ0
  have h2 : (3 + 3 * max (CF 6) 1) * σ * 100 ≤ c := by nlinarith
  have h3 : σ * 300 ≤ c := by nlinarith
  have hσ12 : σ < 1 / 12 := by linarith
  have hσε : 2 * σ ≤ c / 30 := by linarith
  have hεc : c / 30 < c := by linarith
  have hQ4 : -(1 / 3 : ℝ) + ct + ((1 / 3 : ℝ) - c / 3 + (3 + 3 * max (CF 6) 1) * σ +
      3 * (c / 30)) ≤ -(2 * (c / 40)) := by nlinarith
  have hQ5 : -(1 / 3 : ℝ) + ct + ((1 / 6 : ℝ) + (3 * max (CF 6) 1 + 3) * σ) ≤
      -(2 * (c / 40)) := by nlinarith
  obtain ⟨N₁, HN₁⟩ := edgeDeriv_sub_F2_le D hD δA hδA C n F CF hF hCF σ hσ hσ12
  obtain ⟨N₂, HN₂⟩ := H1 n F CF hF hCF σ (c / 30) hσ hσ12 hσε hεc
  obtain ⟨N₃, HN₃⟩ := Cmp_ev 2 (1 / 3 - 1 / 20) (by norm_num)
  obtain ⟨N₄, HN₄⟩ := Cmp_ev (3 / 2) (c / 40) (by positivity)
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) 1), fun N hN L A hA hAhs E₁ E₂ hE₁ hE₂ => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨hN₁, hN₂⟩, ⟨hN₃, hN₄⟩, hN1⟩ := hN
  have hx0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set x : ℝ := (N : ℝ) with hxd
  set η : ℝ := x ^ (-(2 / 3 : ℝ) - σ) with hηd
  have hη : 0 < η := Real.rpow_pos_of_pos hx0 _
  -- `𝔱 ∈ [0, 1/2]`
  have hT0 : 0 ≤ edgeTime N ct := Real.rpow_nonneg hx0.le _
  have hT12 : edgeTime N ct ≤ 1 / 2 := by
    have e1 : edgeTime N ct ≤ x ^ (-(1 / 3 - 1 / 20 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have e2 : x ^ (-(1 / 3 - 1 / 20 : ℝ)) = (x ^ (1 / 3 - 1 / 20 : ℝ))⁻¹ :=
      Real.rpow_neg hx0.le _
    have e3 : (2 : ℝ) ≤ x ^ (1 / 3 - 1 / 20 : ℝ) := HN₃ N hN₃
    have e4 : (x ^ (1 / 3 - 1 / 20 : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) e3
    linarith
  -- the derivative along `[0, 𝔱]`
  set M₀ : ℝ := x ^ ((1 / 6 : ℝ) + (3 * max (CF 6) 1 + 3) * σ) +
    1 / 2 * x ^ ((1 / 3 : ℝ) - c / 3 + (3 + 3 * max (CF 6) 1) * σ + 3 * (c / 30)) with hM₀
  have hder : ∀ t ∈ Set.uIoc (0 : ℝ) (edgeTime N ct),
      ‖entryDeriv (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t)‖ ≤ M₀ := by
    intro t ht
    rw [Set.uIoc_of_le hT0] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have ht1 : t ≤ 1 / 2 := ht.2.trans hT12
    have hd := HN₁ N hN₁ L t ht0 A hA E₁ E₂ hE₁ hE₂
    have hf := HN₂ N hN₂ L t ht0 ht1 A hA hAhs E₁ E₂ hE₁ hE₂
    have he : ‖(1 / 2 : ℂ) * (Real.exp (-t) : ℂ) *
        entryF2 (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t)‖ ≤
        1 / 2 * x ^ ((1 / 3 : ℝ) - c / 3 + (3 + 3 * max (CF 6) 1) * σ + 3 * (c / 30)) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hexp : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hn2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [hn2]
      calc 1 / 2 * Real.exp (-t) * ‖entryF2 (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t)‖
          ≤ 1 / 2 * 1 * ‖entryF2 (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t)‖ := by gcongr
        _ ≤ _ := by rw [mul_one]; gcongr
    have hn := norm_add_le (entryDeriv (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t) -
      (1 / 2 : ℂ) * (Real.exp (-t) : ℂ) * entryF2 (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t))
      ((1 / 2 : ℂ) * (Real.exp (-t) : ℂ) * entryF2 (edgeFn D N A η F E₁ E₂) (ouMatLaw D N L t))
    rw [sub_add_cancel] at hn
    exact hn.trans (add_le_add hd he)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hder
  have hftc := edgeExpect_ftc D N L A η hη n F hF E₁ E₂ (edgeTime N ct) hT0
  rw [← hftc, integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sub_zero, abs_of_nonneg hT0] at hint
  rw [abs_sub_comm]
  refine hint.trans ?_
  -- `N^{-2δ} + N^{-2δ}/2 ≤ N^{-δ}`
  have hδ := HN₄ N hN₄
  have eT : edgeTime N ct = x ^ (-(1 / 3 : ℝ) + ct) := rfl
  rw [eT, hM₀, add_mul, mul_assoc, ← Real.rpow_add hx0, ← Real.rpow_add hx0,
    add_comm _ (-(1 / 3 : ℝ) + ct), add_comm _ (-(1 / 3 : ℝ) + ct)]
  have b1 : x ^ (-(1 / 3 : ℝ) + ct + ((1 / 6 : ℝ) + (3 * max (CF 6) 1 + 3) * σ)) ≤
      x ^ (-(2 * (c / 40))) := Real.rpow_le_rpow_of_exponent_le hx1 hQ5
  have b2 : x ^ (-(1 / 3 : ℝ) + ct + ((1 / 3 : ℝ) - c / 3 + (3 + 3 * max (CF 6) 1) * σ +
      3 * (c / 30))) ≤ x ^ (-(2 * (c / 40))) := Real.rpow_le_rpow_of_exponent_le hx1 hQ4
  have b3 : x ^ (-(2 * (c / 40))) = x ^ (-(c / 40)) * x ^ (-(c / 40)) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have b4 : x ^ (-(c / 40)) = (x ^ (c / 40))⁻¹ := Real.rpow_neg hx0.le _
  have hp : 0 < x ^ (c / 40) := Real.rpow_pos_of_pos hx0 _
  have b5 : x ^ (-(c / 40)) ≤ 2 / 3 := by
    rw [b4, inv_eq_one_div, div_le_div_iff₀ hp (by norm_num)]; linarith
  have b6 : 0 ≤ x ^ (-(c / 40)) := Real.rpow_nonneg hx0.le _
  have b7 : x ^ (-(2 * (c / 40))) ≤ 2 / 3 * x ^ (-(c / 40)) := by
    rw [b3]; nlinarith
  nlinarith

/-- Lemma 4.2 [CVtV], uniformly in the scale `γ ∈ [1/2, 2]`: under (2.4) [eq:condA1] at `k = 1`
there is `𝔠₀ > 0` such that for `𝔠 ∈ (0, 𝔠₀]` and `𝔱 = N^{-1/3+𝔠}` the `n` largest eigenvalues
of `H_Λ(𝔱)` and of `H_Λ`, rescaled by `γ (DN)^{2/3}` at `E⁺`, have the same law up to `N^{-c}`
against `O`. -/
theorem CVtV (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA) (C : ℕ → ℝ) :
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
            ∂(ouMatLaw D N L 0))| ≤ (N : ℝ) ^ (-c) := by
  exact cvtv_of_rescomY D hD δA εA hδA hεA C (rescomY D hD δA εA hδA hεA C)

end RBMTransitionEdge

end
