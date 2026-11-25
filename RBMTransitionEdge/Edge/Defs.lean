module

public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.LocalLaw.OU
public import RBMTransitionEdge.Localized.Reflect

@[expose] public section

/-!
# Definitions of §4 and the elementary identities behind Lemma 4.1 and Theorem 2.2

The time `𝔱`, the GUE of (4.3) [eq:eq_in_law_H] on `Idx D N`, the matrix `V` of the proof of
Lemma 4.1 [CVtG], the moments and free-convolution data used there, `η_*`-regularity, the
external input EI-1 (`LandonYauEdge`), the argument of `F` in (4.7) [2comVVt], the right half of
Theorem 2.2 [MixEV]; the rescaling of resolvents and eigenvalues, (4.3) on arrays, and the
reflection identities for the left edge.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff Pointwise

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The time `𝔱 = N^{-1/3+𝔠}` of Lemmas 4.1 [CVtG] and 4.2 [CVtV]. -/
def edgeTime (N : ℕ) (ct : ℝ) : ℝ := (N : ℝ) ^ (-(1 / 3 : ℝ) + ct)

/-- The GUE `W` of size `DN` of (4.3) [eq:eq_in_law_H], written on the index set `Idx D N`. -/
def gueIdx (D N : ℕ) (x : Coords (D * N)) : Matrix (Idx D N) (Idx D N) ℂ :=
  (wig (D * N) x).submatrix finProdFinEquiv finProdFinEquiv

/-- `V = e^{-𝔱/2} H + Λ` of the proof of Lemma 4.1 [CVtG], `𝔱 = N^{-1/3+𝔠}`. -/
def edgeV (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (ct : ℝ) (w : Fin D → Coords N) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  ((Real.exp (-edgeTime N ct / 2) : ℝ) : ℂ) • blockH D N w + lam D N A

/-- The moment `∫ ρ_V(x) (ξ - x)^{-j} dx` of the density `ρ_V(x) = c ρ_Λ(cx)`, `ρ_Λ` the density
(2.19) [eq:density_rhoN] for `Λ` (proof of Lemma 4.1 [CVtG]; `c = 1` gives `ρ_Λ` itself). -/
def rhoMom {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (c : ℝ) (j : ℕ)
    (ξ : ℝ) : ℝ :=
  ∫ x, c * rho Λ (c * x) / (ξ - x) ^ j

/-- The eigenvalues of `X` satisfy (2.24) [eq:rigidity] with loss `N^{τ'}` against the quantiles
(2.20) [eq:gammak] of `ρ_N` for `Λ = lam D N A`. -/
def IsRigid (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (τ' : ℝ)
    (X : Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
    |eigK X k - quant (rho (lam D N A)) (D * N) k| ≤
      (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(2 / 3 : ℝ)) * rk D N k ^ (-(1 / 3 : ℝ)))

/-- The moment `⟨(ξ - X)^{-j}⟩ = (card ι)⁻¹ Σ_i (ξ - λ_i)^{-j}` of the eigenvalues of `X` at a
real point `ξ` (proof of Lemma 4.1 [CVtG]). -/
def fcMom {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (j : ℕ) (ξ : ℝ) : ℝ :=
  (∑ i, 1 / (ξ - eigs X i) ^ j) / Fintype.card ι

/-- The point `ξ_fc > λ_1(X)` with `t ⟨(ξ - X)^{-2}⟩ = 1`, as the infimum of
`{ξ > λ_1 : t ⟨(ξ - X)^{-2}⟩ ≤ 1}`: the subordination point of the right edge of the free
convolution of the eigenvalue distribution of `X` with the semicircle law of variance `t`
(proof of Lemma 4.1 [CVtG]). -/
def fcXi {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  sInf {ξ : ℝ | eigK X 1 < ξ ∧ t * fcMom X 2 ξ ≤ 1}

/-- The right edge `E_fc = ξ_fc + t ⟨(ξ_fc - X)^{-1}⟩` of the free convolution of the eigenvalue
distribution of `X` with the semicircle law of variance `t` (proof of Lemma 4.1 [CVtG]). -/
def fcEdge {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  fcXi X t + t * fcMom X 1 (fcXi X t)

/-- The curvature `γ_fc = t⁻¹ ⟨(ξ_fc - X)^{-3}⟩^{-1/3}` at the right edge of the same free
convolution, normalized as in (2.6) [eq:def_gamma] (proof of Lemma 4.1 [CVtG]). -/
def fcGamma {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  t⁻¹ * fcMom X 3 (fcXi X t) ^ (-(1 / 3 : ℝ))

/-- `η_*`-regularity of `X` at `E₀`, `η_* = N^{-2/3+a}`, constants `c_V`, `C_V` (proof of
Lemma 4.1 [CVtG]): `Im ⟨(X - z)⁻¹⟩ ∼ √(κ+η)` for `E ∈ [E₀ - c_V, E₀]` and `∼ η/√(κ+η)` for
`E ∈ [E₀, E₀ + c_V]`, `z = E + iη`, `η ∈ [η_*, 10]`, `κ = |E - E₀|`; no eigenvalue above
`E₀ + η_*`; `‖X‖ ≤ N^{C_V}`. -/
def etaRegular {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ) (a cV CV : ℝ)
    (X : Matrix ι ι ℂ) (E₀ : ℝ) : Prop :=
  (∀ E η : ℝ, E₀ - cV ≤ E → E ≤ E₀ → (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ η → η ≤ 10 →
    CV⁻¹ * Real.sqrt (|E - E₀| + η) ≤ (ntr (res X ((E : ℂ) + (η : ℂ) * Complex.I))).im ∧
      (ntr (res X ((E : ℂ) + (η : ℂ) * Complex.I))).im ≤ CV * Real.sqrt (|E - E₀| + η)) ∧
  (∀ E η : ℝ, E₀ ≤ E → E ≤ E₀ + cV → (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ≤ η → η ≤ 10 →
    CV⁻¹ * (η / Real.sqrt (|E - E₀| + η)) ≤ (ntr (res X ((E : ℂ) + (η : ℂ) * Complex.I))).im ∧
      (ntr (res X ((E : ℂ) + (η : ℂ) * Complex.I))).im ≤ CV * (η / Real.sqrt (|E - E₀| + η))) ∧
  eigK X 1 ≤ E₀ + (N : ℝ) ^ (-(2 / 3 : ℝ) + a) ∧
  opNorm X ≤ (N : ℝ) ^ CV

/-- The external input of Lemma 4.1 [CVtG] ([landon2017edgestatisticsdysonbrownian,
Definition 2.1, Theorem 2.2, Lemma 2.3]): for `D ≥ 2`, `𝔠 ∈ (0, 1/10)`, `a ∈ (0, 2𝔠)`,
`c_V, C_V > 0` and a smooth compactly supported `O`, there are `c > 0` and `N₀` such that for
`N ≥ N₀`, every Hermitian `V` of size `DN` that is `N^{-2/3+a}`-regular at some `E₀`, and
`t' = 1 - e^{-𝔱}`, `𝔱 = N^{-1/3+𝔠}`, the `n` largest eigenvalues of `V + √t' W`, `W` a GUE,
rescaled by `γ_fc (DN)^{2/3}` at `E_fc`, have the law of the `n` largest eigenvalues of a GUE up
to `N^{-c}` against `O`. -/
def LandonYauEdge : Prop :=
  ∀ D : ℕ, 2 ≤ D → ∀ ct : ℝ, 0 < ct → ct < 1 / 10 → ∀ a : ℝ, 0 < a → a < 2 * ct →
    ∀ cV CV : ℝ, 0 < cV → 0 < CV →
    ∀ n : ℕ, ∀ O : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ O → HasCompactSupport O →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ V : Matrix (Idx D N) (Idx D N) ℂ, V.IsHermitian → ∀ E₀ : ℝ, etaRegular N a cV CV V E₀ →
      |(∫ x, O (fun i => fcGamma V (1 - Real.exp (-edgeTime N ct)) *
            ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) * (fcEdge V (1 - Real.exp (-edgeTime N ct)) -
              eigK (V + ((Real.sqrt (1 - Real.exp (-edgeTime N ct)) : ℝ) : ℂ) • gueIdx D N x)
                ((i : ℕ) + 1))) ∂(gueLaw (D * N))) -
        (∫ x, O (fun i => ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
            (2 - eigK (wig (D * N) x) ((i : ℕ) + 1))) ∂(gueLaw (D * N)))| ≤ (N : ℝ) ^ (-c)

/-- `DN ∫_{E₁}^{E₂} Im ⟨(h + Λ - y - iη)⁻¹⟩ dy`, `Λ = lam D N A`, the argument of `F` in
(4.7) [2comVVt] of Lemma 4.3 [rescomY]. -/
def edgeCount (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ)
    (h : Idx D N → Idx D N → ℂ) : ℝ :=
  ((D * N : ℕ) : ℝ) *
    ∫ y in E₁..E₂, (ntr (res (Matrix.of h + lam D N A) ((y : ℂ) + (η : ℂ) * Complex.I))).im

/-- The right-edge half of Theorem 2.2 [MixEV]: the first conjunct of `MixEVStatement`, with the
same quantifiers. -/
def MixEVRightStatement : Prop :=
  ∀ D : ℕ, 2 ≤ D → ∀ δA εA : ℝ, 0 < δA → 0 < εA → ∀ C : ℕ → ℝ,
    ∀ n : ℕ, ∀ O : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ O → HasCompactSupport O →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : EntryLaws C,
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
    (N : ℝ) ^ ((1 / 3 : ℝ) + εA) ≤ hsNorm A →
    |(∫ w, O (fun i => gammaPlus (lam D N A) * ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
          (Eplus (lam D N A) - eigK (HLam D N A w) ((i : ℕ) + 1))) ∂(blockLaw D N L)) -
      (∫ w, O (fun i => ((D * N : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
          (2 - eigK (wig (D * N) w) ((i : ℕ) + 1))) ∂(gueLaw (D * N)))| ≤ (N : ℝ) ^ (-c)

/-- The determinant of `c⁻¹ • B` is a unit exactly when that of `B` is, for a nonzero scalar. -/
private lemma Defs_isUnit_det_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    {c : ℂ} (hc : c ≠ 0) : IsUnit (c⁻¹ • B).det ↔ IsUnit B.det := by
  rw [Matrix.det_smul]
  have h : IsUnit (c⁻¹ ^ Fintype.card ι) := (isUnit_iff_ne_zero.mpr (inv_ne_zero hc)).pow _
  exact h.mul_left_iff

/-- The rescaling of the resolvent behind the proof of Lemma 4.1 [CVtG]:
`(c⁻¹ X - z)⁻¹ = c (X - cz)⁻¹` for real `c ≠ 0`. -/
theorem res_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (c : ℝ) (hc : c ≠ 0)
    (z : ℂ) : res (((c : ℂ))⁻¹ • X) z = (c : ℂ) • res X ((c : ℂ) * z) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have h : ((c : ℂ))⁻¹ • X - z • (1 : Matrix ι ι ℂ) =
      ((c : ℂ))⁻¹ • (X - ((c : ℂ) * z) • (1 : Matrix ι ι ℂ)) := by
    rw [smul_sub, smul_smul, inv_mul_cancel_left₀ hc']
  unfold res
  rw [h]
  by_cases hu : IsUnit (X - ((c : ℂ) * z) • (1 : Matrix ι ι ℂ)).det
  · let _ : Invertible ((c : ℂ)⁻¹) := invertibleOfNonzero (inv_ne_zero hc')
    rw [Matrix.inv_smul _ _ hu, invOf_eq_inv, inv_inv]
  · have hu' : ¬ IsUnit (((c : ℂ))⁻¹ • (X - ((c : ℂ) * z) • (1 : Matrix ι ι ℂ))).det :=
      fun h' => hu ((Defs_isUnit_det_smul _ hc').mp h')
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hu', Matrix.nonsing_inv_apply_not_isUnit _ hu,
      smul_zero]

/-- The Hermitian form of `(c : ℂ) • X` is `c` times that of `X`. -/
private lemma Defs_form_smul {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) (c : ℝ)
    (x : ι → ℂ) :
    (star x ⬝ᵥ (((c : ℂ) • X) *ᵥ x)).re = c * (star x ⬝ᵥ (X *ᵥ x)).re := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- `x^* x > 0` for `x ≠ 0`. -/
private lemma Defs_norm_pos {ι : Type*} [Fintype ι] {x : ι → ℂ} (hx : x ≠ 0) :
    0 < (star x ⬝ᵥ x).re := by
  have h1 : (star x ⬝ᵥ x).re = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    rfl
  rw [h1]
  have : (WithLp.toLp 2 x : EuclideanSpace ℂ ι) ≠ 0 := by
    intro h
    exact hx (by simpa using congrArg WithLp.ofLp h)
  positivity

/-- One inequality of `λ_k(cX) = c λ_k(X)` for `1 ≤ k ≤ card ι`, `c > 0`. -/
private lemma Defs_eigK_smul_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (c : ℝ) (hc : 0 < c) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card ι) :
    c * eigK X k ≤ eigK ((c : ℂ) • X) k := by
  have hY : ((c : ℂ) • X).IsHermitian := hX.smul (Complex.conj_ofReal c)
  obtain ⟨⟨V, hV, hV'⟩, -⟩ := eigK_minmax X hX k hk1 hk
  obtain ⟨x, hxV, hx0, hxle⟩ := (eigK_minmax ((c : ℂ) • X) hY k hk1 hk).2 V hV
  have h1 := hV' x hxV
  rw [Defs_form_smul] at hxle
  have hpos := Defs_norm_pos hx0
  have : c * eigK X k * (star x ⬝ᵥ x).re ≤ eigK ((c : ℂ) • X) k * (star x ⬝ᵥ x).re := by
    calc c * eigK X k * (star x ⬝ᵥ x).re = c * (eigK X k * (star x ⬝ᵥ x).re) := by ring
      _ ≤ c * (star x ⬝ᵥ (X *ᵥ x)).re := mul_le_mul_of_nonneg_left h1 hc.le
      _ ≤ _ := hxle
  exact le_of_mul_le_mul_right this hpos

/-- The other inequality of `λ_k(cX) = c λ_k(X)` for `1 ≤ k ≤ card ι`, `c > 0`. -/
private lemma Defs_eigK_smul_ge {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (c : ℝ) (hc : 0 < c) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card ι) :
    eigK ((c : ℂ) • X) k ≤ c * eigK X k := by
  have hY : ((c : ℂ) • X).IsHermitian := hX.smul (Complex.conj_ofReal c)
  obtain ⟨⟨V, hV, hV'⟩, -⟩ := eigK_minmax ((c : ℂ) • X) hY k hk1 hk
  obtain ⟨x, hxV, hx0, hxle⟩ := (eigK_minmax X hX k hk1 hk).2 V hV
  have h1 := hV' x hxV
  rw [Defs_form_smul] at h1
  have hpos := Defs_norm_pos hx0
  have : eigK ((c : ℂ) • X) k * (star x ⬝ᵥ x).re ≤ c * eigK X k * (star x ⬝ᵥ x).re := by
    calc eigK ((c : ℂ) • X) k * (star x ⬝ᵥ x).re ≤ c * (star x ⬝ᵥ (X *ᵥ x)).re := h1
      _ ≤ c * (eigK X k * (star x ⬝ᵥ x).re) := mul_le_mul_of_nonneg_left hxle hc.le
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hpos

/-- The eigenvalues scale with the matrix: `λ_k(cX) = c λ_k(X)` for `c > 0` (proof of
Lemma 4.1 [CVtG]). -/
theorem eigK_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (c : ℝ) (hc : 0 < c) (k : ℕ) : eigK ((c : ℂ) • X) k = c * eigK X k := by
  by_cases h : k - 1 < Fintype.card ι
  · have e : ∀ Z : Matrix ι ι ℂ, eigK Z k = eigK Z (k - 1 + 1) := fun Z => by
      simp [eigK]
    rw [e, e X]
    exact le_antisymm (Defs_eigK_smul_ge X hX c hc _ (by omega) (by omega))
      (Defs_eigK_smul_le X hX c hc _ (by omega) (by omega))
  · simp [eigK, h]

/-- Every entry of `wig n c` is a measurable function of the coordinates `c`. -/
private lemma Defs_measurable_wig (n : ℕ) (i j : Fin n) :
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

/-- The array of coordinates `blockEmb D N w` is a measurable function of `w`. -/
private lemma Defs_measurable_blockEmb (D N : ℕ) : Measurable (blockEmb D N) := by
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
private lemma Defs_measurable_phi0 (D N : ℕ) (t : ℝ) :
    Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.exp (-t / 2) • blockEmb D N p.1 + Real.sqrt (1 - Real.exp (-t)) • p.2 := by
  have h1 : Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.exp (-t / 2) • blockEmb D N p.1 :=
    ((Defs_measurable_blockEmb D N).comp measurable_fst).const_smul (Real.exp (-t / 2))
  have h2 : Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.sqrt (1 - Real.exp (-t)) • p.2 :=
    measurable_snd.const_smul (Real.sqrt (1 - Real.exp (-t)))
  exact h1.add h2

/-- The array `Matrix.of.symm ((wig (DN) c).submatrix _ _)` is a measurable function of the
coordinates `c`. -/
private lemma Defs_measurable_psi (D N : ℕ) :
    Measurable fun c : Coords (D * N) => Matrix.of.symm
      ((wig (D * N) c).submatrix finProdFinEquiv finProdFinEquiv) :=
  measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q =>
    Defs_measurable_wig (D * N) (finProdFinEquiv p) (finProdFinEquiv q)

/-- (4.3) [eq:eq_in_law_H] on arrays: `ouMatLaw D N L t` is the image of `blockLaw ⊗ gueLaw (DN)`
under `(w, x) ↦ e^{-t/2} H(w) + √(1 - e^{-t}) W(x)`. -/
theorem ouMatLaw_eq_map (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) :
    ouMatLaw D N L t = ((blockLaw D N L).prod (gueLaw (D * N))).map fun p =>
      Matrix.of.symm (((Real.exp (-t / 2) : ℝ) : ℂ) • blockH D N p.1 +
        ((Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ) • gueIdx D N p.2) := by
  unfold ouMatLaw ouLaw
  rw [Measure.map_map (Defs_measurable_psi D N) (Defs_measurable_phi0 D N t)]
  congr 1
  funext u
  funext p q
  change wig (D * N) (Real.exp (-t / 2) • blockEmb D N u.1 + Real.sqrt (1 - Real.exp (-t)) • u.2)
      (finProdFinEquiv p) (finProdFinEquiv q) =
    (((Real.exp (-t / 2) : ℝ) : ℂ) • blockH D N u.1 +
      ((Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ) • gueIdx D N u.2) p q
  rw [wig_add, wig_smul, wig_smul]
  have h := congrFun (congrFun (wig_blockEmb D N u.1) p) q
  simp only [Matrix.submatrix_apply] at h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h, gueIdx,
    Matrix.submatrix_apply]

/-- `H_Λ` with coupling `-A` at the configuration `-w` is `-H_Λ` (left edge of Theorem 2.2
[MixEV]). -/
theorem HLam_neg (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin D → Coords N) :
    HLam D N (-A) (-w) = -HLam D N A w := by
  have hw : ∀ (n : ℕ) (v : Coords n), wig n (-v) = -wig n v := fun n v => by
    ext i j
    simp only [wig, Matrix.neg_apply]
    by_cases h : i = j
    · simp [h]
    · by_cases h' : i < j <;> simp [h, h']
  have hb : blockH D N (-w) = -blockH D N w := by
    ext p q
    simp only [blockH, Matrix.neg_apply, Pi.neg_apply]
    split_ifs <;> simp [hw]
  have hl : lam D N (-A) = -lam D N A := by
    ext p q
    simp only [lam, Matrix.neg_apply, star_neg]
    split_ifs <;> simp [add_comm]
  unfold HLam
  rw [hb, hl, neg_add]

/-- On an empty index set `m = 0`, hence `ρ_Λ = 0`. -/
private lemma Defs_rho_empty {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (Λ : Matrix ι ι ℂ) (x : ℝ) : rho Λ x = 0 := by
  have hm : ∀ z : ℂ, mSol Λ z = 0 := fun z => by
    unfold mSol
    rw [dite_eq_right_iff]
    rintro ⟨w, hw, hw'⟩
    have h0 : Fintype.card ι = 0 := Fintype.card_eq_zero
    simp only [ntr, h0, Nat.cast_zero, _root_.inv_zero, zero_mul] at hw'
    rw [hw'] at hw
    simp at hw
  unfold rho
  simp only [hm, Complex.zero_im]
  rw [(tendsto_const_nhds (x := (0 : ℝ)) (f := 𝓝[>] (0 : ℝ))).limUnder_eq]
  simp

/-- `ρ_{-Λ}(x) = ρ_Λ(-x)` for Hermitian `Λ` on any index set (2.19) [eq:density_rhoN]. -/
private lemma Defs_rho_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (x : ℝ) : rho (-Λ) x = rho Λ (-x) := by
  rcases isEmpty_or_nonempty ι with h | h
  · rw [Defs_rho_empty, Defs_rho_empty]
  · exact Reflect_rho_neg hΛ x

/-- The support of `ρ_{-Λ}` is the reflection of that of `ρ_Λ`. -/
private lemma Defs_support_rho_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) : Function.support (rho (-Λ)) = -Function.support (rho Λ) := by
  ext x
  simp [Function.mem_support, Set.mem_neg, Defs_rho_neg Λ hΛ]

/-- The image of `𝓝[<] (-e)` under negation is `𝓝[>] e`. -/
private lemma Defs_map_neg_nhdsLT (e : ℝ) :
    Filter.map (fun E : ℝ => -E) (𝓝[<] (-e)) = 𝓝[>] e := by
  refine le_antisymm tendsto_neg_nhdsLT_neg ?_
  have h2 : Filter.map (fun E : ℝ => -E) (𝓝[>] e) ≤ 𝓝[<] (-e) := by
    simp
  calc 𝓝[>] e = Filter.map (fun E : ℝ => -E) (Filter.map (fun E : ℝ => -E) (𝓝[>] e)) := by
        rw [Filter.map_map]; simp
    _ ≤ _ := Filter.map_mono h2

/-- `E⁻(Λ) = -E⁺(-Λ)` and `γ₋(Λ) = γ₊(-Λ)` for Hermitian `Λ`, from `ρ_{-Λ}(x) = ρ_Λ(-x)` of
(2.19) [eq:density_rhoN] and (2.6) [eq:def_gamma]. -/
theorem edge_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) : Eminus Λ = -Eplus (-Λ) ∧ gammaMinus Λ = gammaPlus (-Λ) := by
  have hE : Eplus (-Λ) = -Eminus Λ := by
    unfold Eplus Eminus
    rw [Defs_support_rho_neg Λ hΛ, Real.sSup_neg]
  have hfun : (fun E : ℝ => rho (-Λ) E / Real.sqrt (-Eminus Λ - E)) =
      (fun E : ℝ => rho Λ E / Real.sqrt (E - Eminus Λ)) ∘ (fun E : ℝ => -E) := by
    funext E
    simp only [Function.comp, Defs_rho_neg Λ hΛ]
    have : -E - Eminus Λ = -Eminus Λ - E := by ring
    rw [this]
  have hlim : limUnder (𝓝[<] (-Eminus Λ)) (fun E : ℝ => rho (-Λ) E / Real.sqrt (-Eminus Λ - E)) =
      limUnder (𝓝[>] (Eminus Λ)) (fun E : ℝ => rho Λ E / Real.sqrt (E - Eminus Λ)) := by
    unfold limUnder
    rw [hfun, ← Filter.map_map, Defs_map_neg_nhdsLT]
  refine ⟨by rw [hE, neg_neg], ?_⟩
  unfold gammaMinus gammaPlus
  rw [hE, hlim]

end RBMTransitionEdge

end
