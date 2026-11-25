module

public import RBMTransitionEdge.Model.Basic

@[expose] public section

/-!
# Min–max, Weyl and reflection for ordered eigenvalues

Courant–Fischer for `eigK`, Weyl's inequality `|λ_k(X + Y) - λ_k(X)| ≤ ‖Y‖`, the Lipschitz bound of
`t ↦ λ_k(H + tΛ)` used in the proof of Theorem 2.5 [theorem_localized_eigenvalue], and `λ_k(-X) = -λ_{n+1-k}(X)`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped NNReal ENNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `eigK X k` is the entry `k - 1` of `eigenvalues₀` when `k - 1 < card ι`. -/
private lemma MinMax_eigK_eq {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {k : ℕ}
    (h : k - 1 < Fintype.card ι) : eigK X k = hX.eigenvalues₀ ⟨k - 1, h⟩ := by
  simp [eigK, eigs, h, hX]

/-- The quadratic form `x^* X x` as an inner product on Euclidean space. -/
private lemma MinMax_form_eq_inner (X : Matrix ι ι ℂ) (x : ι → ℂ) :
    star x ⬝ᵥ (X *ᵥ x) =
      inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanLin X (WithLp.toLp 2 x)) := by
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
    dotProduct_comm]

omit [DecidableEq ι] in
/-- The squared norm `x^* x` as a squared Euclidean norm. -/
private lemma MinMax_norm_eq (x : ι → ℂ) :
    (star x ⬝ᵥ x).re = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rfl

omit [DecidableEq ι] in
/-- `x^* x > 0` for `x ≠ 0`. -/
private lemma MinMax_norm_pos {x : ι → ℂ} (hx : x ≠ 0) : 0 < (star x ⬝ᵥ x).re := by
  rw [MinMax_norm_eq]
  have : (WithLp.toLp 2 x : EuclideanSpace ℂ ι) ≠ 0 := by
    intro h
    exact hx (by simpa using congrArg WithLp.ofLp h)
  positivity

/-- `|x^* Y x| ≤ ‖Y‖ x^* x`. -/
private lemma MinMax_form_le_opNorm (Y : Matrix ι ι ℂ) (x : ι → ℂ) :
    |(star x ⬝ᵥ (Y *ᵥ x)).re| ≤ opNorm Y * (star x ⬝ᵥ x).re := by
  rw [MinMax_norm_eq, MinMax_form_eq_inner]
  set z : EuclideanSpace ℂ ι := WithLp.toLp 2 x
  have h1 : Matrix.toEuclideanLin Y z = Matrix.toEuclideanCLM (𝕜 := ℂ) Y z := rfl
  rw [h1]
  calc |(inner ℂ z (Matrix.toEuclideanCLM (𝕜 := ℂ) Y z)).re|
      ≤ ‖inner ℂ z (Matrix.toEuclideanCLM (𝕜 := ℂ) Y z)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖z‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Y z‖ := norm_inner_le_norm _ _
    _ ≤ ‖z‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) Y‖ * ‖z‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = opNorm Y * ‖z‖ ^ 2 := by rw [opNorm]; ring

omit [DecidableEq ι] in
/-- The quadratic form of a sum. -/
private lemma MinMax_form_add (X Y : Matrix ι ι ℂ) (x : ι → ℂ) :
    (star x ⬝ᵥ ((X + Y) *ᵥ x)).re = (star x ⬝ᵥ (X *ᵥ x)).re + (star x ⬝ᵥ (Y *ᵥ x)).re := by
  rw [add_mulVec, dotProduct_add, Complex.add_re]

omit [DecidableEq ι] in
/-- The quadratic form of `-X`. -/
private lemma MinMax_form_neg (X : Matrix ι ι ℂ) (x : ι → ℂ) :
    (star x ⬝ᵥ ((-X) *ᵥ x)).re = -(star x ⬝ᵥ (X *ᵥ x)).re := by
  rw [neg_mulVec, dotProduct_neg, Complex.neg_re]

/-- Spectral subspaces: for every set `S` of indices of `eigenvalues₀`, the span of the
corresponding eigenvectors has dimension `#S`, and on it the quadratic form is bounded below
(above) by every lower (upper) bound of the eigenvalues indexed by `S`. -/
private lemma MinMax_spectral_sub (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (S : Finset (Fin (Fintype.card ι))) :
    ∃ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = S.card ∧ ∀ x ∈ V,
      (∀ m : ℝ, (∀ j ∈ S, m ≤ hX.eigenvalues₀ j) →
        m * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (X *ᵥ x)).re) ∧
      (∀ m : ℝ, (∀ j ∈ S, hX.eigenvalues₀ j ≤ m) →
        (star x ⬝ᵥ (X *ᵥ x)).re ≤ m * (star x ⬝ᵥ x).re) := by
  set hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hX
  set b := hT.eigenvectorBasis finrank_euclideanSpace
  set μ := hX.eigenvalues₀
  have hμ : ∀ j, hT.eigenvalues finrank_euclideanSpace j = μ j := fun j => rfl
  -- the coefficients of `x` in the eigenbasis
  set c : (ι → ℂ) → Fin (Fintype.card ι) → ℂ := fun x j => inner ℂ (b j) (WithLp.toLp 2 x)
  have hform : ∀ x, (star x ⬝ᵥ (X *ᵥ x)).re = ∑ j, μ j * ‖c x j‖ ^ 2 := by
    intro x
    rw [MinMax_form_eq_inner, ← b.sum_inner_mul_inner, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hT (b j), hT.apply_eigenvectorBasis, inner_smul_left, hμ, ← inner_conj_symm,
      RCLike.conj_ofReal]
    have := RCLike.conj_mul (c x j)
    simp only [c] at this ⊢
    rw [mul_left_comm, this]
    norm_cast
  have hnorm : ∀ x, (star x ⬝ᵥ x).re = ∑ j, ‖c x j‖ ^ 2 := by
    intro x
    rw [MinMax_norm_eq, ← b.sum_sq_norm_inner_right]
  set v : Fin (Fintype.card ι) → (ι → ℂ) := fun j => WithLp.ofLp (b j)
  have hv : LinearIndependent ℂ v :=
    b.toBasis.linearIndependent.map' (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap
      (WithLp.linearEquiv 2 ℂ (ι → ℂ)).ker
  set f : S → (ι → ℂ) := fun j => v j.val
  have hf : LinearIndependent ℂ f := hv.comp _ Subtype.val_injective
  refine ⟨Submodule.span ℂ (Set.range f), ?_, ?_⟩
  · rw [finrank_span_eq_card hf, Fintype.card_coe]
  intro x hx
  have hc : ∀ j ∉ S, c x j = 0 := by
    intro j hj
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      have hij : j ≠ i.val := fun h => hj (h ▸ i.property)
      simp only [c, f, v, WithLp.toLp_ofLp]
      exact b.orthonormal.inner_eq_zero hij
    | zero => simp [c]
    | add y z _ _ hy hz =>
      simp only [c, WithLp.toLp_add, inner_add_right] at hy hz ⊢
      rw [hy, hz, add_zero]
    | smul a y _ hy =>
      simp only [c, WithLp.toLp_smul, inner_smul_right] at hy ⊢
      rw [hy, mul_zero]
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · rw [hform, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j ∈ S
    · exact mul_le_mul_of_nonneg_right (hm j hj) (by positivity)
    · simp [hc j hj]
  · rw [hform, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j ∈ S
    · exact mul_le_mul_of_nonneg_right (hm j hj) (by positivity)
    · simp [hc j hj]

omit [DecidableEq ι] in
/-- Two subspaces whose dimensions add up to more than `card ι` share a nonzero vector. -/
private lemma MinMax_inf_ne_bot (V W : Submodule ℂ (ι → ℂ))
    (h : Fintype.card ι < Module.finrank ℂ V + Module.finrank ℂ W) :
    ∃ x ∈ V, x ∈ W ∧ x ≠ 0 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h2 := Submodule.finrank_le (V ⊔ W)
  rw [Module.finrank_fintype_fun_eq_card] at h2
  have h3 : 0 < Module.finrank ℂ ↥(V ⊓ W) := by omega
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h3
  exact ⟨x, hx.1, hx.2, fun h => hx0 (by simp [h])⟩

/-- Courant–Fischer for `λ_k` (decreasing order), `1 ≤ k ≤ n`: some `k`-dimensional subspace has
Rayleigh quotients `≥ λ_k`, and every `k`-dimensional subspace has a nonzero vector with Rayleigh
quotient `≤ λ_k`. -/
theorem eigK_minmax (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card ι) :
    (∃ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = k ∧
        ∀ x ∈ V, eigK X k * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (X *ᵥ x)).re) ∧
      ∀ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = k →
        ∃ x ∈ V, x ≠ 0 ∧ (star x ⬝ᵥ (X *ᵥ x)).re ≤ eigK X k * (star x ⬝ᵥ x).re := by
  have hlt : k - 1 < Fintype.card ι := by omega
  set a : Fin (Fintype.card ι) := ⟨k - 1, hlt⟩
  rw [MinMax_eigK_eq hX hlt]
  refine ⟨?_, fun V hV => ?_⟩
  · obtain ⟨V, hV, hV'⟩ := MinMax_spectral_sub X hX (Finset.Iic a)
    refine ⟨V, ?_, fun x hx => (hV' x hx).1 _ fun j hj => ?_⟩
    · rw [hV, Fin.card_Iic]
      simp only [a]
      omega
    · exact hX.eigenvalues₀_antitone (Finset.mem_Iic.mp hj)
  · obtain ⟨W, hW, hW'⟩ := MinMax_spectral_sub X hX (Finset.Ici a)
    have hcard : Fintype.card ι < Module.finrank ℂ V + Module.finrank ℂ W := by
      rw [hV, hW, Fin.card_Ici]
      simp only [a]
      omega
    obtain ⟨x, hxV, hxW, hx0⟩ := MinMax_inf_ne_bot V W hcard
    exact ⟨x, hxV, hx0, (hW' x hxW).2 _ fun j hj =>
      hX.eigenvalues₀_antitone (Finset.mem_Ici.mp hj)⟩

/-- One half of Weyl's inequality, `λ_k(X) - λ_k(X + Y) ≤ ‖Y‖`, for `1 ≤ k ≤ card ι`. -/
private lemma MinMax_weyl_half (X Y : Matrix ι ι ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card ι) :
    eigK X k - eigK (X + Y) k ≤ opNorm Y := by
  obtain ⟨V, hV, hV'⟩ := (eigK_minmax X hX k hk1 hk).1
  obtain ⟨x, hxV, hx0, hx⟩ := (eigK_minmax (X + Y) (hX.add hY) k hk1 hk).2 V hV
  have h1 := hV' x hxV
  have h2 := MinMax_form_le_opNorm Y x
  have h3 := MinMax_norm_pos hx0
  rw [MinMax_form_add] at hx
  have h4 : (eigK X k - eigK (X + Y) k - opNorm Y) * (star x ⬝ᵥ x).re ≤ 0 := by
    nlinarith [neg_abs_le (star x ⬝ᵥ (Y *ᵥ x)).re]
  by_contra hcon
  have hcon := lt_of_not_ge hcon
  nlinarith

/-- `‖-Y‖ = ‖Y‖`. -/
private lemma MinMax_opNorm_neg (Y : Matrix ι ι ℂ) : opNorm (-Y) = opNorm Y := by
  rw [opNorm, opNorm, map_neg, norm_neg]

/-- `‖c Y‖ = |c| ‖Y‖`. -/
private lemma MinMax_opNorm_smul (c : ℂ) (Y : Matrix ι ι ℂ) : opNorm (c • Y) = ‖c‖ * opNorm Y := by
  rw [opNorm, opNorm, map_smul, norm_smul]

/-- Weyl's inequality `|λ_k(X + Y) - λ_k(X)| ≤ ‖Y‖`. -/
theorem eigK_add_sub_le (X Y : Matrix ι ι ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian) (k : ℕ) :
    |eigK (X + Y) k - eigK X k| ≤ opNorm Y := by
  by_cases h : k - 1 < Fintype.card ι
  · set k' := k - 1 + 1
    have hk' : ∀ M : Matrix ι ι ℂ, eigK M k = eigK M k' := by
      intro M
      simp only [eigK, k', Nat.add_sub_cancel]
    rw [hk', hk']
    have h1 := MinMax_weyl_half X Y hX hY k' (by omega) (by omega)
    have h2 := MinMax_weyl_half (X + Y) (-Y) (hX.add hY) hY.neg k' (by omega) (by omega)
    rw [add_neg_cancel_right, MinMax_opNorm_neg] at h2
    rw [abs_le]
    constructor <;> linarith
  · have h0 : ∀ M : Matrix ι ι ℂ, eigK M k = 0 := fun M => by simp [eigK, h]
    rw [h0, h0, sub_zero, abs_zero, opNorm]
    exact norm_nonneg _

/-- `|λ_k(H + tΛ) - λ_k(H + sΛ)| ≤ |t - s| ‖Λ‖`. -/
theorem eigK_line_lipschitz (H Λ : Matrix ι ι ℂ) (hH : H.IsHermitian) (hΛ : Λ.IsHermitian)
    (k : ℕ) (t s : ℝ) :
    |eigK (H + (t : ℂ) • Λ) k - eigK (H + (s : ℂ) • Λ) k| ≤ |t - s| * opNorm Λ := by
  have hsa : ∀ r : ℝ, IsSelfAdjoint (r : ℂ) := fun r => Complex.conj_ofReal r
  have hdiff : H + (t : ℂ) • Λ = (H + (s : ℂ) • Λ) + ((t - s : ℝ) : ℂ) • Λ := by
    rw [Complex.ofReal_sub, sub_smul]
    abel
  rw [hdiff]
  have := eigK_add_sub_le (H + (s : ℂ) • Λ) (((t - s : ℝ) : ℂ) • Λ) (hH.add (hΛ.smul (hsa s)))
    (hΛ.smul (hsa _)) k
  rwa [MinMax_opNorm_smul, Complex.norm_real, Real.norm_eq_abs] at this

/-- The reflection `λ_k(-X) = -λ_{n+1-k}(X)`, `1 ≤ k ≤ n`. -/
theorem eigK_neg (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card ι) : eigK (-X) k = -eigK X (Fintype.card ι + 1 - k) := by
  have hlt : Fintype.card ι + 1 - k - 1 < Fintype.card ι := by omega
  set a : Fin (Fintype.card ι) := ⟨Fintype.card ι + 1 - k - 1, hlt⟩
  rw [MinMax_eigK_eq hX hlt]
  set μ := -hX.eigenvalues₀ a
  -- a `k`-dimensional subspace on which the form of `-X` is `≥ μ`
  obtain ⟨V₁, hV₁, hV₁'⟩ := MinMax_spectral_sub X hX (Finset.Ici a)
  have hV₁k : Module.finrank ℂ V₁ = k := by
    rw [hV₁, Fin.card_Ici]
    simp only [a]
    omega
  -- every `k`-dimensional subspace has a nonzero vector where the form of `-X` is `≤ μ`
  have hB : ∀ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = k →
      ∃ x ∈ V, x ≠ 0 ∧ (star x ⬝ᵥ ((-X) *ᵥ x)).re ≤ μ * (star x ⬝ᵥ x).re := by
    intro V hV
    obtain ⟨W, hW, hW'⟩ := MinMax_spectral_sub X hX (Finset.Iic a)
    have hcard : Fintype.card ι < Module.finrank ℂ V + Module.finrank ℂ W := by
      rw [hV, hW, Fin.card_Iic]
      simp only [a]
      omega
    obtain ⟨x, hxV, hxW, hx0⟩ := MinMax_inf_ne_bot V W hcard
    refine ⟨x, hxV, hx0, ?_⟩
    have := (hW' x hxW).1 _ fun j hj => hX.eigenvalues₀_antitone (Finset.mem_Iic.mp hj)
    rw [MinMax_form_neg]
    simp only [μ]
    linarith
  obtain ⟨hA', hB'⟩ := eigK_minmax (-X) hX.neg k hk1 hk
  apply le_antisymm
  · obtain ⟨V, hV, hV'⟩ := hA'
    obtain ⟨x, hxV, hx0, hx⟩ := hB V hV
    have h1 := hV' x hxV
    have h3 := MinMax_norm_pos hx0
    by_contra hcon
    have hcon := lt_of_not_ge hcon
    nlinarith
  · obtain ⟨x, hxV, hx0, hx⟩ := hB' V₁ hV₁k
    have h1 := (hV₁' x hxV).2 _ fun j hj => hX.eigenvalues₀_antitone (Finset.mem_Ici.mp hj)
    have h3 := MinMax_norm_pos hx0
    rw [MinMax_form_neg] at hx
    by_contra hcon
    have hcon := lt_of_not_ge hcon
    simp only [μ] at hcon
    nlinarith

end RBMTransitionEdge

end
