module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Tools.MinMax

@[expose] public section

/-!
# Eigenvalues along a line

The derivative of `t ↦ λ_k(X + tY)` where it exists, and the fundamental theorem of calculus for it,
for the eigenvalue flows of §3 and §5.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sesquilinear form `y^* X x` as an inner product on Euclidean space. -/
private lemma EigDeriv_form_eq_inner (X : Matrix ι ι ℂ) (y x : ι → ℂ) :
    star y ⬝ᵥ (X *ᵥ x) =
      inner ℂ (WithLp.toLp 2 y) (Matrix.toEuclideanLin X (WithLp.toLp 2 x)) := by
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
    dotProduct_comm]

omit [DecidableEq ι] in
/-- The squared norm `x^* x` as a squared Euclidean norm. -/
private lemma EigDeriv_norm_eq (x : ι → ℂ) :
    (star x ⬝ᵥ x).re = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rfl

/-- `|Re y^* Y w| ≤ ‖Y‖ ‖y‖ ‖w‖` in Euclidean norms. -/
private lemma EigDeriv_bil_le (Y : Matrix ι ι ℂ) (y w : ι → ℂ) :
    |(star y ⬝ᵥ (Y *ᵥ w)).re| ≤
      opNorm Y * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ *
        ‖(WithLp.toLp 2 w : EuclideanSpace ℂ ι)‖ := by
  rw [EigDeriv_form_eq_inner]
  set z : EuclideanSpace ℂ ι := WithLp.toLp 2 y
  set z' : EuclideanSpace ℂ ι := WithLp.toLp 2 w
  have h1 : Matrix.toEuclideanLin Y z' = Matrix.toEuclideanCLM (𝕜 := ℂ) Y z' := rfl
  rw [h1]
  calc |(inner ℂ z (Matrix.toEuclideanCLM (𝕜 := ℂ) Y z')).re|
      ≤ ‖inner ℂ z (Matrix.toEuclideanCLM (𝕜 := ℂ) Y z')‖ := Complex.abs_re_le_norm _
    _ ≤ ‖z‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Y z'‖ := norm_inner_le_norm _ _
    _ ≤ ‖z‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) Y‖ * ‖z'‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = opNorm Y * ‖z‖ * ‖z'‖ := by rw [opNorm]; ring


/-- An orthonormal eigenbasis of a Hermitian matrix, ordered by `eigenvalues₀`. -/
private def EigDeriv_basis {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    OrthonormalBasis (Fin (Fintype.card ι)) ℂ (EuclideanSpace ℂ ι) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM).eigenvectorBasis finrank_euclideanSpace

/-- `M b_j = λ_j b_j` for the eigenbasis. -/
private lemma EigDeriv_basis_apply {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (j : Fin (Fintype.card ι)) :
    Matrix.toEuclideanLin M (EigDeriv_basis hM j) =
      (hM.eigenvalues₀ j : ℂ) • EigDeriv_basis hM j :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM).apply_eigenvectorBasis finrank_euclideanSpace j

/-- The coordinate `⟨b_j, x⟩` of `x` in the eigenbasis. -/
private def EigDeriv_coef {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (x : ι → ℂ)
    (j : Fin (Fintype.card ι)) : ℂ :=
  inner ℂ (EigDeriv_basis hM j) (WithLp.toLp 2 x)

/-- The vector `Σ_j φ_j b_j`. -/
private def EigDeriv_vec {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (φ : Fin (Fintype.card ι) → ℂ) : ι → ℂ :=
  WithLp.ofLp ((EigDeriv_basis hM).repr.symm (WithLp.toLp 2 φ))

private lemma EigDeriv_coef_vec {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (φ : Fin (Fintype.card ι) → ℂ) (j : Fin (Fintype.card ι)) :
    EigDeriv_coef hM (EigDeriv_vec hM φ) j = φ j := by
  simp only [EigDeriv_coef, EigDeriv_vec, WithLp.toLp_ofLp]
  rw [← OrthonormalBasis.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]

private lemma EigDeriv_vec_coef {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (x : ι → ℂ) :
    EigDeriv_vec hM (EigDeriv_coef hM x) = x := by
  simp only [EigDeriv_vec]
  have : WithLp.toLp 2 (EigDeriv_coef hM x) = (EigDeriv_basis hM).repr (WithLp.toLp 2 x) := by
    ext j
    simp [EigDeriv_coef, OrthonormalBasis.repr_apply_apply]
  rw [this, LinearIsometryEquiv.symm_apply_apply]

private lemma EigDeriv_vec_add {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (φ ψ : Fin (Fintype.card ι) → ℂ) :
    EigDeriv_vec hM (φ + ψ) = EigDeriv_vec hM φ + EigDeriv_vec hM ψ := by
  simp only [EigDeriv_vec]
  have : (WithLp.toLp 2 (φ + ψ) : EuclideanSpace ℂ (Fin (Fintype.card ι))) =
      WithLp.toLp 2 φ + WithLp.toLp 2 ψ := rfl
  rw [this, map_add]
  rfl

/-- The form in eigen-coordinates, `x^* M x = Σ λ_j |c_j|²`. -/
private lemma EigDeriv_form {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (x : ι → ℂ) :
    (star x ⬝ᵥ (M *ᵥ x)).re =
      ∑ j, hM.eigenvalues₀ j * ‖EigDeriv_coef hM x j‖ ^ 2 := by
  set hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  set b := EigDeriv_basis hM
  rw [EigDeriv_form_eq_inner, ← b.sum_inner_mul_inner, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hT (b j), EigDeriv_basis_apply, inner_smul_left, ← inner_conj_symm, Complex.conj_ofReal]
  have := RCLike.conj_mul (EigDeriv_coef hM x j)
  simp only [EigDeriv_coef] at this ⊢
  rw [mul_left_comm, this]
  rw [Complex.re_ofReal_mul]
  congr 1
  norm_cast

/-- The norm in eigen-coordinates, `x^* x = Σ |c_j|²`. -/
private lemma EigDeriv_norm_sum {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (x : ι → ℂ) :
    (star x ⬝ᵥ x).re = ∑ j, ‖EigDeriv_coef hM x j‖ ^ 2 := by
  rw [EigDeriv_norm_eq, ← (EigDeriv_basis hM).sum_sq_norm_inner_right]
  rfl


/-- `Σ φ_j b_j` is an eigenvector of `M` for `μ` when `φ` is supported on `{λ_j = μ}`. -/
private lemma EigDeriv_vec_eig {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (φ : Fin (Fintype.card ι) → ℂ) (μ : ℝ)
    (hφ : ∀ j, φ j ≠ 0 → hM.eigenvalues₀ j = μ) :
    M *ᵥ EigDeriv_vec hM φ = (μ : ℂ) • EigDeriv_vec hM φ := by
  set hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  set b := EigDeriv_basis hM
  set z : EuclideanSpace ℂ ι := b.repr.symm (WithLp.toLp 2 φ) with hz
  have hcoef : ∀ j, inner ℂ (b j) z = φ j := by
    intro j
    rw [← OrthonormalBasis.repr_apply_apply, hz, LinearIsometryEquiv.apply_symm_apply]
  have key : Matrix.toEuclideanLin M z = (μ : ℂ) • z := by
    apply b.repr.injective
    ext j
    rw [OrthonormalBasis.repr_apply_apply, ← hT (b j) z, EigDeriv_basis_apply, inner_smul_left,
      Complex.conj_ofReal, map_smul, PiLp.smul_apply, OrthonormalBasis.repr_apply_apply, hcoef]
    by_cases h : φ j = 0
    · simp [h]
    · rw [hφ j h, smul_eq_mul]
  have := congrArg WithLp.ofLp key
  simpa [EigDeriv_vec, hz, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using this

/-- Spectral subspaces: for every set `S` of indices, a subspace of dimension `#S` whose vectors
have vanishing eigen-coordinates outside `S`. -/
private lemma EigDeriv_span {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (S : Finset (Fin (Fintype.card ι))) :
    ∃ V : Submodule ℂ (ι → ℂ), Module.finrank ℂ V = S.card ∧
      ∀ x ∈ V, ∀ j ∉ S, EigDeriv_coef hM x j = 0 := by
  set b := EigDeriv_basis hM
  set v : Fin (Fintype.card ι) → (ι → ℂ) := fun j => WithLp.ofLp (b j)
  have hv : LinearIndependent ℂ v :=
    b.toBasis.linearIndependent.map' (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap
      (WithLp.linearEquiv 2 ℂ (ι → ℂ)).ker
  set f : S → (ι → ℂ) := fun j => v j.val
  have hf : LinearIndependent ℂ f := hv.comp _ Subtype.val_injective
  refine ⟨Submodule.span ℂ (Set.range f), ?_, ?_⟩
  · rw [finrank_span_eq_card hf, Fintype.card_coe]
  intro x hx j hj
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    have hij : j ≠ i.val := fun h => hj (h ▸ i.property)
    simp only [EigDeriv_coef, f, v, WithLp.toLp_ofLp]
    exact b.orthonormal.inner_eq_zero hij
  | zero => simp [EigDeriv_coef]
  | add y z _ _ hy hz =>
    simp only [EigDeriv_coef, WithLp.toLp_add, inner_add_right] at hy hz ⊢
    rw [hy, hz, add_zero]
  | smul a y _ hy =>
    simp only [EigDeriv_coef, WithLp.toLp_smul, inner_smul_right] at hy ⊢
    rw [hy, mul_zero]


/-- A gap: all eigenvalues strictly above `μ` are at least `μ + g`, for some `g > 0`. -/
private lemma EigDeriv_gap {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (μ : ℝ) :
    ∃ g : ℝ, 0 < g ∧ ∀ j, μ < hM.eigenvalues₀ j → μ + g ≤ hM.eigenvalues₀ j := by
  set T : Finset ℝ := (Finset.univ.filter fun j => μ < hM.eigenvalues₀ j).image
    (fun j => hM.eigenvalues₀ j - μ) with hT
  refine ⟨(insert 1 T).min' (Finset.insert_nonempty 1 T), ?_, fun j hj => ?_⟩
  · rw [Finset.lt_min'_iff]
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact one_pos
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
      have := (Finset.mem_filter.mp hj).2
      linarith
  · have := Finset.min'_le (insert 1 T) (hM.eigenvalues₀ j - μ)
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)))
    linarith

/-- Splitting a vector whose eigen-coordinates vanish below `μ` into the part above `μ` (with a gap
`g`) and the part in the eigenspace of `μ`. -/
private lemma EigDeriv_split {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (μ g : ℝ)
    (hgap : ∀ j, μ < hM.eigenvalues₀ j → μ + g ≤ hM.eigenvalues₀ j)
    (x : ι → ℂ) (hx : ∀ j, hM.eigenvalues₀ j < μ → EigDeriv_coef hM x j = 0) :
    ∃ y w : ι → ℂ, x = y + w ∧ M *ᵥ w = (μ : ℂ) • w ∧
      (star x ⬝ᵥ x).re = (star y ⬝ᵥ y).re + (star w ⬝ᵥ w).re ∧
      μ * (star x ⬝ᵥ x).re + g * (star y ⬝ᵥ y).re ≤ (star x ⬝ᵥ (M *ᵥ x)).re := by
  set c := EigDeriv_coef hM x with hc
  set φy : Fin (Fintype.card ι) → ℂ := fun j => if μ < hM.eigenvalues₀ j then c j else 0 with hφy
  set φw : Fin (Fintype.card ι) → ℂ := fun j => if hM.eigenvalues₀ j = μ then c j else 0 with hφw
  have hsum : c = φy + φw := by
    ext j
    simp only [hφy, hφw, Pi.add_apply]
    rcases lt_trichotomy (hM.eigenvalues₀ j) μ with h | h | h
    · have h1 : ¬ μ < hM.eigenvalues₀ j := not_lt.mpr h.le
      have h2 : ¬ hM.eigenvalues₀ j = μ := h.ne
      simp [h1, h2, hx j h]
    · have h1 : ¬ μ < hM.eigenvalues₀ j := by rw [h]; exact lt_irrefl _
      simp [h]
    · have h2 : ¬ hM.eigenvalues₀ j = μ := h.ne'
      simp [h, h2]
  have hpt : ∀ j, ‖c j‖ ^ 2 = ‖φy j‖ ^ 2 + ‖φw j‖ ^ 2 := by
    intro j
    rcases lt_trichotomy (hM.eigenvalues₀ j) μ with h | h | h
    · have h1 : ¬ μ < hM.eigenvalues₀ j := not_lt.mpr h.le
      have h2 : ¬ hM.eigenvalues₀ j = μ := h.ne
      simp [hφy, hφw, h1, h2, hx j h]
    · have h1 : ¬ μ < hM.eigenvalues₀ j := by rw [h]; exact lt_irrefl _
      simp [hφy, hφw, h]
    · have h2 : ¬ hM.eigenvalues₀ j = μ := h.ne'
      simp [hφy, hφw, h, h2]
  have hge : ∀ j, μ * ‖c j‖ ^ 2 + g * ‖φy j‖ ^ 2 ≤ hM.eigenvalues₀ j * ‖c j‖ ^ 2 := by
    intro j
    rcases lt_trichotomy (hM.eigenvalues₀ j) μ with h | h | h
    · have h1 : ¬ μ < hM.eigenvalues₀ j := not_lt.mpr h.le
      simp [hφy, h1, hx j h]
    · have h1 : ¬ μ < hM.eigenvalues₀ j := by rw [h]; exact lt_irrefl _
      simp [hφy, h]
    · have := hgap j h
      simp only [hφy, h, ↓reduceIte]
      nlinarith [sq_nonneg ‖c j‖]
  refine ⟨EigDeriv_vec hM φy, EigDeriv_vec hM φw, ?_, ?_, ?_, ?_⟩
  · rw [← EigDeriv_vec_add, ← hsum, hc, EigDeriv_vec_coef]
  · refine EigDeriv_vec_eig hM φw μ fun j hj => ?_
    by_contra hne
    exact hj (by simp [hφw, hne])
  · rw [EigDeriv_norm_sum hM, EigDeriv_norm_sum hM, EigDeriv_norm_sum hM]
    simp only [EigDeriv_coef_vec]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hpt j
  · rw [EigDeriv_form hM, EigDeriv_norm_sum hM, EigDeriv_norm_sum hM]
    simp only [EigDeriv_coef_vec]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hge j


/-- `eigK X k` is the entry `k - 1` of `eigenvalues₀` when `k - 1 < card ι`. -/
private lemma EigDeriv_eigK_eq {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {k : ℕ}
    (h : k - 1 < Fintype.card ι) : eigK X k = hX.eigenvalues₀ ⟨k - 1, h⟩ := by
  simp [eigK, eigs, h, hX]

omit [DecidableEq ι] in
/-- `x^* x > 0` for `x ≠ 0`. -/
private lemma EigDeriv_norm_pos {x : ι → ℂ} (hx : x ≠ 0) : 0 < (star x ⬝ᵥ x).re := by
  rw [EigDeriv_norm_eq]
  have : (WithLp.toLp 2 x : EuclideanSpace ℂ ι) ≠ 0 := by
    intro h
    exact hx (by simpa using congrArg WithLp.ofLp h)
  positivity

omit [DecidableEq ι] in
/-- The quadratic form of `M + δΛ`. -/
private lemma EigDeriv_form_line (M Λ : Matrix ι ι ℂ) (δ : ℝ) (x : ι → ℂ) :
    (star x ⬝ᵥ ((M + (δ : ℂ) • Λ) *ᵥ x)).re =
      (star x ⬝ᵥ (M *ᵥ x)).re + δ * (star x ⬝ᵥ (Λ *ᵥ x)).re := by
  rw [add_mulVec, dotProduct_add, Complex.add_re, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, Complex.re_ofReal_mul]

omit [DecidableEq ι] in
/-- The quadratic form of a sum of two vectors. -/
private lemma EigDeriv_form_add (Λ : Matrix ι ι ℂ) (y w : ι → ℂ) :
    (star (y + w) ⬝ᵥ (Λ *ᵥ (y + w))).re = (star y ⬝ᵥ (Λ *ᵥ y)).re + (star w ⬝ᵥ (Λ *ᵥ w)).re +
      ((star y ⬝ᵥ (Λ *ᵥ w)).re + (star w ⬝ᵥ (Λ *ᵥ y)).re) := by
  simp only [star_add, add_dotProduct, dotProduct_add, Matrix.mulVec_add, Complex.add_re]
  ring


/-- The one-sided lower bound for `λ_k(M + δΛ)`, `δ > 0`: if `Re w^*Λw ≥ r |w|²` on the
eigenspace of `λ_k(M)`, then `λ_k(M + δΛ) ≥ λ_k(M) + δ r - C δ²` for small `δ` (second-order
perturbation with a spectral gap, for the one-sided derivative in the proof of (5.24) [ygfyz]). -/
private lemma EigDeriv_lower (M Λ : Matrix ι ι ℂ) (hM : M.IsHermitian) (hΛ : Λ.IsHermitian)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card ι) (r : ℝ)
    (hr : ∀ w : ι → ℂ, M *ᵥ w = (eigK M k : ℂ) • w →
      r * (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ (Λ *ᵥ w)).re) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      eigK M k + δ * r - C * δ ^ 2 ≤ eigK (M + (δ : ℂ) • Λ) k := by
  have hlt : k - 1 < Fintype.card ι := by omega
  set a : Fin (Fintype.card ι) := ⟨k - 1, hlt⟩ with ha
  set μ : ℝ := eigK M k with hμ
  have hμa : μ = hM.eigenvalues₀ a := EigDeriv_eigK_eq hM hlt
  obtain ⟨V, hVdim, hVc⟩ := EigDeriv_span hM (Finset.Iic a)
  have hVk : Module.finrank ℂ V = k := by
    rw [hVdim, Fin.card_Iic]
    simp only [a]
    omega
  obtain ⟨g, hg, hgap⟩ := EigDeriv_gap hM μ
  set L : ℝ := opNorm Λ with hL
  have hL0 : 0 ≤ L := norm_nonneg _
  set C : ℝ := 2 * L ^ 2 / g with hC
  have hCg : C * g = 2 * L ^ 2 := by rw [hC]; field_simp
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, g / (2 * (|L + r| + 1)), by positivity, fun δ hδ hδ₀ => ?_⟩
  have hδL : δ * (L + r) ≤ g / 2 := by
    have h1 : δ * (|L + r| + 1) ≤ g / 2 := by
      calc δ * (|L + r| + 1) ≤ g / (2 * (|L + r| + 1)) * (|L + r| + 1) :=
            mul_le_mul_of_nonneg_right hδ₀ (by positivity)
        _ = g / 2 := by field_simp
    nlinarith [le_abs_self (L + r), abs_nonneg (L + r)]
  have hMδ : (M + (δ : ℂ) • Λ).IsHermitian :=
    hM.add (hΛ.smul (Complex.conj_ofReal δ : IsSelfAdjoint (δ : ℂ)))
  obtain ⟨x, hxV, hx0, hx⟩ := (eigK_minmax (M + (δ : ℂ) • Λ) hMδ k hk1 hk).2 V hVk
  have hxpos := EigDeriv_norm_pos hx0
  -- split `x`
  have hxc : ∀ j, hM.eigenvalues₀ j < μ → EigDeriv_coef hM x j = 0 := by
    intro j hj
    refine hVc x hxV j fun hmem => ?_
    have := hM.eigenvalues₀_antitone (Finset.mem_Iic.mp hmem)
    rw [← hμa] at this
    exact absurd hj (not_lt.mpr this)
  obtain ⟨y, w, hxyw, hw, hnorm, hform⟩ := EigDeriv_split hM μ g hgap x hxc
  -- the estimates
  set X := (star x ⬝ᵥ x).re with hX
  set Y := (star y ⬝ᵥ y).re with hY
  set W := (star w ⬝ᵥ w).re with hW
  set ny : ℝ := ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ with hny
  set nw : ℝ := ‖(WithLp.toLp 2 w : EuclideanSpace ℂ ι)‖ with hnw
  have hYn : Y = ny ^ 2 := EigDeriv_norm_eq y
  have hWn : W = nw ^ 2 := EigDeriv_norm_eq w
  have hny0 : 0 ≤ ny := norm_nonneg _
  have hnw0 : 0 ≤ nw := norm_nonneg _
  have hly : -(L * ny * ny) ≤ (star y ⬝ᵥ (Λ *ᵥ y)).re := (abs_le.mp (EigDeriv_bil_le Λ y y)).1
  have hc1 : -(L * ny * nw) ≤ (star y ⬝ᵥ (Λ *ᵥ w)).re := (abs_le.mp (EigDeriv_bil_le Λ y w)).1
  have hc2 : -(L * nw * ny) ≤ (star w ⬝ᵥ (Λ *ᵥ y)).re := (abs_le.mp (EigDeriv_bil_le Λ w y)).1
  have hlw : r * W ≤ (star w ⬝ᵥ (Λ *ᵥ w)).re := hr w hw
  have hΛx : (star x ⬝ᵥ (Λ *ᵥ x)).re ≥ -(L * ny * ny) + r * W - 2 * (L * ny * nw) := by
    rw [hxyw, EigDeriv_form_add]
    linarith [mul_comm (L * nw) ny, mul_assoc L nw ny, mul_assoc L ny nw, mul_comm nw ny]
  have hAMGM : 0 ≤ g / 2 * ny ^ 2 + C * δ ^ 2 * nw ^ 2 - 2 * δ * L * ny * nw := by
    have e : g * (g / 2 * ny ^ 2 + C * δ ^ 2 * nw ^ 2 - 2 * δ * L * ny * nw) =
        (g * ny - 2 * δ * L * nw) ^ 2 / 2 := by
      calc _ = g / 2 * g * ny ^ 2 + (C * g) * δ ^ 2 * nw ^ 2 - 2 * g * δ * L * ny * nw := by ring
        _ = _ := by rw [hCg]; ring
    have : 0 ≤ g * (g / 2 * ny ^ 2 + C * δ ^ 2 * nw ^ 2 - 2 * δ * L * ny * nw) := by
      rw [e]; positivity
    exact nonneg_of_mul_nonneg_right this hg
  have hlow : (μ + δ * r - C * δ ^ 2) * X ≤ (star x ⬝ᵥ ((M + (δ : ℂ) • Λ) *ᵥ x)).re := by
    rw [EigDeriv_form_line]
    have h1 : δ * (-(L * ny * ny) + r * W - 2 * (L * ny * nw)) ≤ δ * (star x ⬝ᵥ (Λ *ᵥ x)).re :=
      mul_le_mul_of_nonneg_left hΛx hδ.le
    have h2 : 0 ≤ ny ^ 2 * (g / 2 - δ * (L + r)) := mul_nonneg (sq_nonneg _) (by linarith)
    have h3 : 0 ≤ C * δ ^ 2 * ny ^ 2 := by positivity
    rw [hnorm, hYn, hWn] at hform ⊢
    rw [hWn] at h1
    nlinarith [h1, h2, h3, hAMGM, hform]
  have := hlow.trans hx
  exact le_of_mul_le_mul_right this hxpos

omit [DecidableEq ι] in
/-- `Re (star v ⬝ v) = Σ ‖v_i‖²`. -/
private lemma EigDeriv_dot_re (v : ι → ℂ) : (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

omit [DecidableEq ι] in
private lemma EigDeriv_N_smul (s : ℝ) (w : ι → ℂ) :
    (star ((s : ℂ) • w) ⬝ᵥ ((s : ℂ) • w)).re = s ^ 2 * (star w ⬝ᵥ w).re := by
  have : star ((s : ℂ) • w) ⬝ᵥ ((s : ℂ) • w) = ((s ^ 2 : ℝ) : ℂ) * (star w ⬝ᵥ w) := by
    simp [star_smul, smul_dotProduct, dotProduct_smul]
    ring
  rw [this, Complex.re_ofReal_mul]

omit [DecidableEq ι] in
private lemma EigDeriv_l_smul (Λ : Matrix ι ι ℂ) (s : ℝ) (w : ι → ℂ) :
    (star ((s : ℂ) • w) ⬝ᵥ (Λ *ᵥ ((s : ℂ) • w))).re = s ^ 2 * (star w ⬝ᵥ (Λ *ᵥ w)).re := by
  have : star ((s : ℂ) • w) ⬝ᵥ (Λ *ᵥ ((s : ℂ) • w)) = ((s ^ 2 : ℝ) : ℂ) * (star w ⬝ᵥ (Λ *ᵥ w)) := by
    simp [star_smul, smul_dotProduct, dotProduct_smul, Matrix.mulVec_smul]
    ring
  rw [this, Complex.re_ofReal_mul]

omit [DecidableEq ι] in
private lemma EigDeriv_l_cont (Λ : Matrix ι ι ℂ) :
    Continuous fun w : ι → ℂ => (star w ⬝ᵥ (Λ *ᵥ w)).re := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  fun_prop

omit [DecidableEq ι] in
private lemma EigDeriv_N_cont :
    Continuous fun w : ι → ℂ => (star w ⬝ᵥ w).re := by
  simp only [dotProduct, Pi.star_apply]
  fun_prop

omit [DecidableEq ι] in
private lemma EigDeriv_mulVec_cont (M : Matrix ι ι ℂ) :
    Continuous fun w : ι → ℂ => M *ᵥ w := by
  exact Continuous.matrix_mulVec continuous_const continuous_id


omit [DecidableEq ι] in
/-- A nonzero vector of the eigenspace rescales to a unit one, with `ℓ(w) = ℓ(w') ‖w‖²`. -/
private lemma EigDeriv_normalize (M Λ : Matrix ι ι ℂ) (μ : ℝ) (w : ι → ℂ) (hw : w ≠ 0)
    (hMw : M *ᵥ w = (μ : ℂ) • w) :
    ∃ w' : ι → ℂ, M *ᵥ w' = (μ : ℂ) • w' ∧ (star w' ⬝ᵥ w').re = 1 ∧
      (star w ⬝ᵥ (Λ *ᵥ w)).re = (star w' ⬝ᵥ (Λ *ᵥ w')).re * (star w ⬝ᵥ w).re := by
  have hpos : 0 < (star w ⬝ᵥ w).re := by
    rw [EigDeriv_dot_re]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr (by simpa using hi)) 2)
      (Finset.single_le_sum (f := fun i => ‖w i‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i))
  set N := (star w ⬝ᵥ w).re with hN
  set s : ℝ := (Real.sqrt N)⁻¹ with hs
  have hs2 : s ^ 2 * N = 1 := by
    rw [hs, inv_pow, Real.sq_sqrt hpos.le]
    exact inv_mul_cancel₀ hpos.ne'
  refine ⟨(s : ℂ) • w, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, hMw, smul_comm]
  · rw [EigDeriv_N_smul]; exact hs2
  · rw [EigDeriv_l_smul]
    calc (star w ⬝ᵥ (Λ *ᵥ w)).re = (s ^ 2 * N) * (star w ⬝ᵥ (Λ *ᵥ w)).re := by rw [hs2, one_mul]
      _ = _ := by ring

omit [DecidableEq ι] in
/-- The realisation step: if `d` lies between the extreme values of the form `Re w^*Λw` over unit
vectors of the eigenspace (expressed through the one-sided facts `hL`, `hU`), it is attained by a
unit eigenvector. -/
private lemma EigDeriv_realize (M Λ : Matrix ι ι ℂ) (μ d : ℝ)
    (hne : ∃ u : ι → ℂ, M *ᵥ u = (μ : ℂ) • u ∧ u ≠ 0)
    (hL : ∀ r : ℝ, (∀ w : ι → ℂ, M *ᵥ w = (μ : ℂ) • w →
      r * (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ (Λ *ᵥ w)).re) → r ≤ d)
    (hU : ∀ r : ℝ, (∀ w : ι → ℂ, M *ᵥ w = (μ : ℂ) • w →
      (star w ⬝ᵥ (Λ *ᵥ w)).re ≤ r * (star w ⬝ᵥ w).re) → d ≤ r) :
    ∃ u : ι → ℂ, M *ᵥ u = (μ : ℂ) • u ∧ ∑ i, ‖u i‖ ^ 2 = 1 ∧
      d = (star u ⬝ᵥ (Λ *ᵥ u)).re := by
  set K : Set (ι → ℂ) := {w | M *ᵥ w = (μ : ℂ) • w ∧ (star w ⬝ᵥ w).re = 1} with hK
  have hKc : IsClosed K := by
    have h1 : IsClosed {w : ι → ℂ | M *ᵥ w = (μ : ℂ) • w} :=
      isClosed_eq (EigDeriv_mulVec_cont M) (by fun_prop)
    have h2 : IsClosed {w : ι → ℂ | (star w ⬝ᵥ w).re = 1} :=
      isClosed_eq EigDeriv_N_cont continuous_const
    exact h1.inter h2
  have hKb : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : ι → ℂ)) (r := 1)).subset fun w hw => ?_
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : ‖w i‖ ^ 2 ≤ 1 := by
      rw [← hw.2, EigDeriv_dot_re]
      exact Finset.single_le_sum (f := fun i => ‖w i‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i)
    nlinarith [norm_nonneg (w i)]
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  obtain ⟨u0, hu0, hu00⟩ := hne
  obtain ⟨w0, hw0, hw0n, -⟩ := EigDeriv_normalize M Λ μ u0 hu00 hu0
  have hKne : K.Nonempty := ⟨w0, hw0, hw0n⟩
  obtain ⟨xm, hxmK, hxm⟩ := hKcpt.exists_isMinOn hKne (EigDeriv_l_cont Λ).continuousOn
  obtain ⟨xp, hxpK, hxp⟩ := hKcpt.exists_isMaxOn hKne (EigDeriv_l_cont Λ).continuousOn
  have hN0 : ∀ w : ι → ℂ, 0 ≤ (star w ⬝ᵥ w).re := fun w => by
    rw [EigDeriv_dot_re]; positivity
  -- the extremal values bound the form on the whole eigenspace
  have hlo : ∀ w : ι → ℂ, M *ᵥ w = (μ : ℂ) • w →
      (star xm ⬝ᵥ (Λ *ᵥ xm)).re * (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ (Λ *ᵥ w)).re := by
    intro w hw
    by_cases hw0 : w = 0
    · simp [hw0]
    · obtain ⟨w', hw', hw'n, hl⟩ := EigDeriv_normalize M Λ μ w hw0 hw
      have h1 : (star xm ⬝ᵥ (Λ *ᵥ xm)).re ≤ (star w' ⬝ᵥ (Λ *ᵥ w')).re :=
        isMinOn_iff.mp hxm _ ⟨hw', hw'n⟩
      rw [hl]
      exact mul_le_mul_of_nonneg_right h1 (hN0 w)
  have hhi : ∀ w : ι → ℂ, M *ᵥ w = (μ : ℂ) • w →
      (star w ⬝ᵥ (Λ *ᵥ w)).re ≤ (star xp ⬝ᵥ (Λ *ᵥ xp)).re * (star w ⬝ᵥ w).re := by
    intro w hw
    by_cases hw0 : w = 0
    · simp [hw0]
    · obtain ⟨w', hw', hw'n, hl⟩ := EigDeriv_normalize M Λ μ w hw0 hw
      have h1 : (star w' ⬝ᵥ (Λ *ᵥ w')).re ≤ (star xp ⬝ᵥ (Λ *ᵥ xp)).re :=
        isMaxOn_iff.mp hxp _ ⟨hw', hw'n⟩
      rw [hl]
      exact mul_le_mul_of_nonneg_right h1 (hN0 w)
  have hdlo : (star xm ⬝ᵥ (Λ *ᵥ xm)).re ≤ d := hL _ hlo
  have hdhi : d ≤ (star xp ⬝ᵥ (Λ *ᵥ xp)).re := hU _ hhi
  -- the segment from `xm` to `xp`
  set x : ℝ → (ι → ℂ) := fun s => ((1 - s : ℝ) : ℂ) • xm + (s : ℂ) • xp with hx
  set G : ℝ → ℝ := fun s => (star (x s) ⬝ᵥ (Λ *ᵥ x s)).re - d * (star (x s) ⬝ᵥ x s).re with hG
  have hxc : Continuous x := by
    simp only [hx]
    fun_prop
  have hGc : Continuous G :=
    ((EigDeriv_l_cont Λ).comp hxc).sub (continuous_const.mul (EigDeriv_N_cont.comp hxc))
  have hx0' : x 0 = xm := by simp [hx]
  have hx1' : x 1 = xp := by simp [hx]
  have hG0 : G 0 ≤ 0 := by
    simp only [hG, hx0', hxmK.2]
    linarith
  have hG1 : 0 ≤ G 1 := by
    simp only [hG, hx1', hxpK.2]
    linarith
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc zero_le_one hGc.continuousOn ⟨hG0, hG1⟩
  have hxs : M *ᵥ x s = (μ : ℂ) • x s := by
    simp only [hx, Matrix.mulVec_add, Matrix.mulVec_smul, hxmK.1, hxpK.1, smul_add]
    rw [smul_comm (μ : ℂ), smul_comm (μ : ℂ)]
  by_cases hxs0 : x s = 0
  · -- degenerate segment: `xp = - xm` up to the scalars, so both extremal values agree
    have hv : ((1 - s : ℝ) : ℂ) • xm = ((-s : ℝ) : ℂ) • xp := by
      have h := hxs0
      simp only [hx] at h
      rw [eq_neg_of_add_eq_zero_left h, ← neg_smul, ← Complex.ofReal_neg]
    have hN := congrArg (fun v : ι → ℂ => (star v ⬝ᵥ v).re) hv
    have hℓ := congrArg (fun v : ι → ℂ => (star v ⬝ᵥ (Λ *ᵥ v)).re) hv
    simp only [EigDeriv_N_smul, EigDeriv_l_smul, hxmK.2, hxpK.2, mul_one] at hN hℓ
    have hs12 : s = 1 / 2 := by nlinarith
    have hsq : (1 - s) ^ 2 = (-s) ^ 2 := hN
    have hne : (-s) ^ 2 ≠ 0 := by rw [hs12]; norm_num
    have heq : (star xm ⬝ᵥ (Λ *ᵥ xm)).re = (star xp ⬝ᵥ (Λ *ᵥ xp)).re := by
      rw [hsq] at hℓ
      exact mul_left_cancel₀ hne hℓ
    refine ⟨xm, hxmK.1, ?_, by linarith⟩
    rw [← EigDeriv_dot_re]; exact hxmK.2
  · obtain ⟨u, hu, hun, hl⟩ := EigDeriv_normalize M Λ μ (x s) hxs0 hxs
    have hpos : 0 < (star (x s) ⬝ᵥ x s).re := by
      rw [EigDeriv_dot_re]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hxs0
      exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr (by simpa using hi)) 2)
        (Finset.single_le_sum (f := fun i => ‖x s i‖ ^ 2) (fun j _ => by positivity)
          (Finset.mem_univ i))
    refine ⟨u, hu, by rw [← EigDeriv_dot_re]; exact hun, ?_⟩
    have hGs : (star (x s) ⬝ᵥ (Λ *ᵥ x s)).re = d * (star (x s) ⬝ᵥ x s).re := by
      have := hs; simp only [hG] at this; linarith
    rw [hl] at hGs
    exact (mul_right_cancel₀ hpos.ne' hGs).symm


/-- The one-sided upper bound for `λ_k(M + δΛ)`, `δ > 0`, from the lower bound for `(-M, -Λ)` and
the reflection `λ_k(-X) = -λ_{n+1-k}(X)`. -/
private lemma EigDeriv_upper (M Λ : Matrix ι ι ℂ) (hM : M.IsHermitian) (hΛ : Λ.IsHermitian)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card ι) (r : ℝ)
    (hr : ∀ w : ι → ℂ, M *ᵥ w = (eigK M k : ℂ) • w →
      (star w ⬝ᵥ (Λ *ᵥ w)).re ≤ r * (star w ⬝ᵥ w).re) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      eigK (M + (δ : ℂ) • Λ) k ≤ eigK M k + δ * r + C * δ ^ 2 := by
  have hsa : ∀ r : ℝ, IsSelfAdjoint (r : ℂ) := fun r => Complex.conj_ofReal r
  set k' := Fintype.card ι + 1 - k with hk'
  have hk'1 : 1 ≤ k' := by omega
  have hk'n : k' ≤ Fintype.card ι := by omega
  have hkk : Fintype.card ι + 1 - k' = k := by omega
  have hneg : ∀ X : Matrix ι ι ℂ, X.IsHermitian → eigK (-X) k' = -eigK X k := fun X hX => by
    rw [eigK_neg X hX k' hk'1 hk'n, hkk]
  have hr' : ∀ w : ι → ℂ, (-M) *ᵥ w = (eigK (-M) k' : ℂ) • w →
      (-r) * (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ ((-Λ) *ᵥ w)).re := by
    intro w hw
    rw [hneg M hM, Complex.ofReal_neg, neg_smul, Matrix.neg_mulVec, neg_inj] at hw
    rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
    linarith [hr w hw]
  obtain ⟨C, δ₀, hδ₀, hb⟩ := EigDeriv_lower (-M) (-Λ) hM.neg hΛ.neg k' hk'1 hk'n (-r) hr'
  refine ⟨C, δ₀, hδ₀, fun δ hδ hδ' => ?_⟩
  have h := hb δ hδ hδ'
  have hMδ : (M + (δ : ℂ) • Λ).IsHermitian := hM.add (hΛ.smul (hsa δ))
  have e : -M + (δ : ℂ) • (-Λ) = -(M + (δ : ℂ) • Λ) := by
    rw [smul_neg, neg_add]
  rw [e, hneg _ hMδ, hneg M hM] at h
  linarith


/-- At a point of differentiability of `t ↦ λ_k(H + tΛ)`, the derivative is `u*Λu` for some unit
eigenvector `u` of `λ_k(H + tΛ)` (the step behind (5.24) [ygfyz]). -/
theorem eigK_line_deriv (H Λ : Matrix ι ι ℂ) (hH : H.IsHermitian) (hΛ : Λ.IsHermitian) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card ι) (t d : ℝ)
    (hd : HasDerivAt (fun s : ℝ => eigK (H + (s : ℂ) • Λ) k) d t) :
    ∃ u : ι → ℂ, IsUnitEigvec (H + (t : ℂ) • Λ) (eigK (H + (t : ℂ) • Λ) k) u ∧
      d = (star u ⬝ᵥ (Λ *ᵥ u)).re := by
  have hsa : ∀ r : ℝ, IsSelfAdjoint (r : ℂ) := fun r => Complex.conj_ofReal r
  set M : Matrix ι ι ℂ := H + (t : ℂ) • Λ with hMdef
  have hM : M.IsHermitian := hH.add (hΛ.smul (hsa t))
  set μ : ℝ := eigK M k with hμ
  have hf : ∀ δ : ℝ, eigK (H + ((t + δ : ℝ) : ℂ) • Λ) k = eigK (M + (δ : ℂ) • Λ) k := by
    intro δ
    congr 1
    rw [hMdef, Complex.ofReal_add, add_smul, add_assoc]
  have hslope := hd.tendsto_slope_zero_right
  -- `d ≥ r` for every `r` with `Re w^*Λw ≥ r |w|²` on the eigenspace
  have hlower : ∀ r : ℝ, (∀ w : ι → ℂ, M *ᵥ w = (μ : ℂ) • w →
      r * (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ (Λ *ᵥ w)).re) → r ≤ d := by
    intro r hr
    obtain ⟨C, δ₀, hδ₀, hb⟩ := EigDeriv_lower M Λ hM hΛ k hk1 hk r hr
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), r - C * δ ≤
        δ⁻¹ • (eigK (H + ((t + δ : ℝ) : ℂ) • Λ) k - eigK M k) := by
      filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
      rw [hf, smul_eq_mul, le_inv_mul_iff₀ hδ.1]
      nlinarith [hb δ hδ.1 hδ.2.le]
    have hlim : Tendsto (fun δ : ℝ => r - C * δ) (𝓝[>] 0) (𝓝 r) := by
      have : Tendsto (fun δ : ℝ => r - C * δ) (𝓝 0) (𝓝 (r - C * 0)) :=
        (continuous_const.sub (continuous_const.mul continuous_id)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hlim hslope hev
  -- `d ≤ r` for every `r` with `Re w^*Λw ≤ r |w|²` on the eigenspace
  have hupper : ∀ r : ℝ, (∀ w : ι → ℂ, M *ᵥ w = (μ : ℂ) • w →
      (star w ⬝ᵥ (Λ *ᵥ w)).re ≤ r * (star w ⬝ᵥ w).re) → d ≤ r := by
    intro r hr
    obtain ⟨C, δ₀, hδ₀, hb⟩ := EigDeriv_upper M Λ hM hΛ k hk1 hk r hr
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        δ⁻¹ • (eigK (H + ((t + δ : ℝ) : ℂ) • Λ) k - eigK M k) ≤ r + C * δ := by
      filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
      rw [hf, smul_eq_mul, inv_mul_le_iff₀ hδ.1]
      nlinarith [hb δ hδ.1 hδ.2.le]
    have hlim : Tendsto (fun δ : ℝ => r + C * δ) (𝓝[>] 0) (𝓝 r) := by
      have : Tendsto (fun δ : ℝ => r + C * δ) (𝓝 0) (𝓝 (r + C * 0)) :=
        (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hslope hlim hev
  -- the eigenspace is nontrivial
  have hlt : k - 1 < Fintype.card ι := by omega
  set a : Fin (Fintype.card ι) := ⟨k - 1, hlt⟩ with ha
  have hμa : μ = hM.eigenvalues₀ a := EigDeriv_eigK_eq hM hlt
  have hne : ∃ u : ι → ℂ, M *ᵥ u = (μ : ℂ) • u ∧ u ≠ 0 := by
    refine ⟨EigDeriv_vec hM (Pi.single a 1), EigDeriv_vec_eig hM _ μ fun j hj => ?_, ?_⟩
    · have : j = a := by
        by_contra hja
        exact hj (by simp [hja])
      rw [this, hμa]
    · intro h0
      have := EigDeriv_coef_vec hM (Pi.single a 1) a
      rw [h0] at this
      simp [EigDeriv_coef] at this
  obtain ⟨u, hu, hun, hdu⟩ := EigDeriv_realize M Λ μ d hne hlower hupper
  exact ⟨u, ⟨hu, hun⟩, hdu⟩

/-- The first equality of (5.24) [ygfyz]: `λ_k(H + Λ) - λ_k(H) = ∫₀¹ λ_k'(t) dt` (the function is
Lipschitz, hence absolutely continuous). -/
theorem eigK_line_ftc (H Λ : Matrix ι ι ℂ) (hH : H.IsHermitian) (hΛ : Λ.IsHermitian) (k : ℕ) :
    eigK (H + Λ) k - eigK H k =
      ∫ t in (0 : ℝ)..1, deriv (fun s : ℝ => eigK (H + (s : ℂ) • Λ) k) t := by
  have hlip : LipschitzWith (Real.toNNReal (opNorm Λ))
      (fun s : ℝ => eigK (H + (s : ℂ) • Λ) k) := by
    refine LipschitzWith.of_dist_le_mul fun s s' => ?_
    have hn : 0 ≤ opNorm Λ := norm_nonneg _
    have := eigK_line_lipschitz H Λ hH hΛ k s s'
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hn]
    linarith [mul_comm |s - s'| (opNorm Λ)]
  have hac := (hlip.lipschitzOnWith (s := Set.uIcc (0 : ℝ) 1)).absolutelyContinuousOnInterval
  have := hac.integral_deriv_eq_sub
  simp only [Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul, add_zero] at this
  rw [this]

end RBMTransitionEdge

end
