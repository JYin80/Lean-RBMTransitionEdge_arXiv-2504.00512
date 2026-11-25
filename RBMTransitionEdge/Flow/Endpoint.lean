module

public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.Tools.Resolvent

@[expose] public section

/-!
# The quantities of Theorem 2.1

The matrices `L` of (3.1) [def_ML] and Definition 3.2 [defLK3], and the deterministic steps from
(3.4) [eq:extend:main_evector1] to Theorem 2.1 [mix]: the eigenvector projection bound
(3.5) [eq:bdd_spec] and the trace identity.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The `D × D` matrix `L(z₁, z₂)` of (3.1) [def_ML]: `L_{ab} = D ⟨G(z₁) E_a G(z₂) E_b⟩`,
`G(z) = (h + Λ - z)⁻¹`. -/
def Lmat {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (h : Idx D N → Idx D N → ℂ)
    (z₁ z₂ : ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun a b => (D : ℂ) *
    ntr (res (Matrix.of h + Λ) z₁ * Ea D N a * res (Matrix.of h + Λ) z₂ * Ea D N b)

/-- The expectation `E L(z₁, z₂)` of (3.1) [def_ML] under the law `μ`, entrywise. -/
def ELmat {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z₁ z₂ : ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun a b => ∫ h, Lmat Λ h z₁ z₂ a b ∂μ

/-- The tensor `L(z₁, z₂, z₃)` of Definition 3.2 [defLK3]:
`L_{a₁a₂a₃} = D ⟨G₁ E_{a₁} G₂ E_{a₂} G₃ E_{a₃}⟩`. -/
def Lten3 {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (h : Idx D N → Idx D N → ℂ)
    (z₁ z₂ z₃ : ℂ) : Fin D → Fin D → Fin D → ℂ :=
  fun a₁ a₂ a₃ => (D : ℂ) * ntr (res (Matrix.of h + Λ) z₁ * Ea D N a₁ *
    res (Matrix.of h + Λ) z₂ * Ea D N a₂ * res (Matrix.of h + Λ) z₃ * Ea D N a₃)

/-- The `ℓ²` norm of a `D × D × D` tensor, as in Lemma 3.6 [lemma_G_large]. -/
def ten3Norm {D : ℕ} (T : Fin D → Fin D → Fin D → ℂ) : ℝ :=
  Real.sqrt (∑ a, ∑ b, ∑ c, ‖T a b c‖ ^ 2)

/-- `z̄ z = ‖z‖²` as a complex number. -/
private lemma Endpoint_star_mul (z : ℂ) : star z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- `Im G = η G G^*` for Hermitian `X`, `z = E + iη`, `η > 0`, with `G(z̄) = G(z)^*`. -/
private lemma Endpoint_imRes {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    (2 * Complex.I)⁻¹ • (res X z - res X (star z)) = (z.im : ℂ) • (res X z * (res X z)ᴴ) := by
  obtain ⟨h1, h2⟩ := res_mul_sub X hX z hz
  have hs : res X (star z) = (res X z)ᴴ := res_conj X hX z hz
  have hX' : (X - z • (1 : Matrix ι ι ℂ))ᴴ = X - star z • (1 : Matrix ι ι ℂ) := by
    rw [Matrix.conjTranspose_sub, hX.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  have k1 : (X - star z • (1 : Matrix ι ι ℂ)) * (res X z)ᴴ = 1 := by
    have := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, hX', Matrix.conjTranspose_one] at this
  have e : res X z - (res X z)ᴴ = (z - star z) • (res X z * (res X z)ᴴ) := by
    have e1 : res X z * ((X - star z • (1 : Matrix ι ι ℂ)) - (X - z • (1 : Matrix ι ι ℂ))) *
        (res X z)ᴴ = res X z - (res X z)ᴴ := by
      rw [mul_sub, sub_mul, mul_assoc, k1, mul_one, h2, one_mul]
    rw [← e1]
    have : (X - star z • (1 : Matrix ι ι ℂ)) - (X - z • (1 : Matrix ι ι ℂ)) =
        (z - star z) • (1 : Matrix ι ι ℂ) := by
      rw [sub_smul]
      abel
    rw [this, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [hs, e, smul_smul]
  have hz2 : z - star z = (2 * Complex.I) * (z.im : ℂ) := by
    rw [Complex.star_def, Complex.sub_conj]
    push_cast
    ring
  rw [hz2, inv_mul_cancel_left₀ (by simp)]

/-- Double Cauchy-Schwarz: `|u^* C w|² ≤ Σ_{ij} |C_{ij}|²` for unit vectors `u`, `w`. -/
private lemma Endpoint_cs {ι : Type*} [Fintype ι] (C : Matrix ι ι ℂ) (u w : ι → ℂ)
    (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hw : ∑ i, ‖w i‖ ^ 2 = 1) :
    ‖star u ⬝ᵥ (C *ᵥ w)‖ ^ 2 ≤ ∑ i, ∑ j, ‖C i j‖ ^ 2 := by
  have h1 : ‖star u ⬝ᵥ (C *ᵥ w)‖ ≤ ∑ p : ι × ι, (‖u p.1‖ * ‖w p.2‖) * ‖C p.1 p.2‖ := by
    rw [Fintype.sum_prod_type]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul, norm_star]
    ring_nf
    exact le_refl _
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun p => ‖u p.1‖ * ‖w p.2‖) (fun p => ‖C p.1 p.2‖)
  have h3 : ∑ p : ι × ι, (‖u p.1‖ * ‖w p.2‖) ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [mul_pow, ← Finset.mul_sum, hu, hw, mul_one]
  have h4 : ∑ p : ι × ι, ‖C p.1 p.2‖ ^ 2 = ∑ i, ∑ j, ‖C i j‖ ^ 2 :=
    Fintype.sum_prod_type (fun p : ι × ι => ‖C p.1 p.2‖ ^ 2)
  rw [h3, one_mul, h4] at h2
  calc ‖star u ⬝ᵥ (C *ᵥ w)‖ ^ 2
      ≤ (∑ p : ι × ι, (‖u p.1‖ * ‖w p.2‖) * ‖C p.1 p.2‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- `tr(C C) = Σ_{ij} |C_{ij}|²` (real part) for Hermitian `C`. -/
private lemma Endpoint_trace_sq {ι : Type*} [Fintype ι] (C : Matrix ι ι ℂ) (hC : C.IsHermitian) :
    (C * C).trace.re = ∑ i, ∑ j, ‖C i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : C i j = star (C j i) := (hC.apply i j).symm
  rw [h, Endpoint_star_mul, norm_star]
  norm_cast

/-- An eigenvector of `X` with real eigenvalue `e` is an eigenvector of `G(z)` with eigenvalue
`(e - z)⁻¹`. -/
private lemma Endpoint_res_eigvec {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (e : ℝ) (v : ι → ℂ) (hv : X *ᵥ v = (e : ℂ) • v) :
    res X z *ᵥ v = ((e : ℂ) - z)⁻¹ • v := by
  have hne : (e : ℂ) - z ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have h1 : (X - z • (1 : Matrix ι ι ℂ)) *ᵥ v = ((e : ℂ) - z) • v := by
    rw [Matrix.sub_mulVec, hv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
  have h2 : v = ((e : ℂ) - z) • (res X z *ᵥ v) := by
    have := congrArg (fun y => res X z *ᵥ y) h1
    simp only [Matrix.mulVec_mulVec, (res_mul_sub X hX z hz).2, Matrix.one_mulVec,
      Matrix.mulVec_smul] at this
    exact this
  calc res X z *ᵥ v = ((e : ℂ) - z)⁻¹ • (((e : ℂ) - z) • (res X z *ᵥ v)) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = ((e : ℂ) - z)⁻¹ • v := by rw [← h2]

/-- The spectral step of the proof of Theorem 2.1 [mix] (basis-free (3.5) [eq:bdd_spec]): for
Hermitian `X`, `z = E + iη`, `η > 0`, unit eigenvectors `u, w` with eigenvalues in
`[E - η, E + η]` and Hermitian `B`, `|u^* B w|² ≤ 4 η² tr(Im G B Im G B)`. -/
theorem evec_proj_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (u w : ι → ℂ) (e₁ e₂ : ℝ) (hu : IsUnitEigvec X e₁ u) (hw : IsUnitEigvec X e₂ w)
    (h₁ : |e₁ - z.re| ≤ z.im) (h₂ : |e₂ - z.re| ≤ z.im) :
    ‖star u ⬝ᵥ (B *ᵥ w)‖ ^ 2 ≤ 4 * z.im ^ 2 *
      (((2 * Complex.I)⁻¹ • (res X z - res X (star z))) * B *
        ((2 * Complex.I)⁻¹ • (res X z - res X (star z))) * B).trace.re := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hw1, hw2⟩ := hw
  rw [Endpoint_imRes X hX z hz]
  set G := res X z with hG
  set C : Matrix ι ι ℂ := Gᴴ * B * G with hC
  have hCh : C.IsHermitian := by
    unfold Matrix.IsHermitian
    simp [hC, Matrix.conjTranspose_mul, hB.eq, mul_assoc]
  have htr : ((z.im : ℂ) • (G * Gᴴ) * B * ((z.im : ℂ) • (G * Gᴴ)) * B).trace =
      ((z.im ^ 2 : ℝ) : ℂ) * (C * C).trace := by
    have e1 : (z.im : ℂ) • (G * Gᴴ) * B * ((z.im : ℂ) • (G * Gᴴ)) * B =
        ((z.im ^ 2 : ℝ) : ℂ) • (G * (Gᴴ * B * G * Gᴴ * B)) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      push_cast
      simp only [mul_assoc, sq]
    have e2 : (G * (Gᴴ * B * G * Gᴴ * B)).trace = (C * C).trace := by
      rw [Matrix.trace_mul_comm]
      simp only [hC, mul_assoc]
    rw [e1, Matrix.trace_smul, e2, smul_eq_mul]
  rw [htr, Complex.re_ofReal_mul, Endpoint_trace_sq C hCh]
  set S := ∑ i, ∑ j, ‖C i j‖ ^ 2 with hS
  have hs := Endpoint_cs C u w hu2 hw2
  have hGu : G *ᵥ u = ((e₁ : ℂ) - z)⁻¹ • u := Endpoint_res_eigvec X hX z hz e₁ u hu1
  have hGw : G *ᵥ w = ((e₂ : ℂ) - z)⁻¹ • w := Endpoint_res_eigvec X hX z hz e₂ w hw1
  have hne : ∀ e : ℝ, (e : ℂ) - z ≠ 0 := fun e h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  set t := star u ⬝ᵥ (B *ᵥ w) with ht
  set s := star u ⬝ᵥ (C *ᵥ w) with hsdef
  have hts : t = star ((e₁ : ℂ) - z) * ((e₂ : ℂ) - z) * s := by
    have h1 : s = star (((e₁ : ℂ) - z)⁻¹) * ((e₂ : ℂ) - z)⁻¹ * t := by
      have h2 : C *ᵥ w = Gᴴ *ᵥ (B *ᵥ (G *ᵥ w)) := by
        rw [hC, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have h3 : star u ⬝ᵥ (Gᴴ *ᵥ (B *ᵥ (G *ᵥ w))) = star (G *ᵥ u) ⬝ᵥ (B *ᵥ (G *ᵥ w)) := by
        rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]
      rw [hsdef, h2, h3, hGu, hGw, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
        ht, smul_eq_mul]
      ring
    rw [h1]
    have a1 : star ((e₁ : ℂ) - z) ≠ 0 := star_ne_zero.mpr (hne e₁)
    have a2 : ((e₂ : ℂ) - z) ≠ 0 := hne e₂
    rw [star_inv₀]
    field_simp
  have hq : ∀ e : ℝ, |e - z.re| ≤ z.im → ‖(e : ℂ) - z‖ ^ 2 ≤ 2 * z.im ^ 2 := by
    intro e he
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
    have := sq_le_sq' (abs_le.mp he).1 (abs_le.mp he).2
    nlinarith [this]
  have hq1 := hq e₁ h₁
  have hq2 := hq e₂ h₂
  have hnorm : ‖t‖ ^ 2 = ‖(e₁ : ℂ) - z‖ ^ 2 * ‖(e₂ : ℂ) - z‖ ^ 2 * ‖s‖ ^ 2 := by
    rw [hts, norm_mul, norm_mul, norm_star]
    ring
  have hη : 0 ≤ z.im ^ 2 := sq_nonneg _
  have hprod : ‖(e₁ : ℂ) - z‖ ^ 2 * ‖(e₂ : ℂ) - z‖ ^ 2 ≤ 2 * z.im ^ 2 * (2 * z.im ^ 2) :=
    mul_le_mul hq1 hq2 (sq_nonneg _) (by positivity)
  calc ‖t‖ ^ 2 = ‖(e₁ : ℂ) - z‖ ^ 2 * ‖(e₂ : ℂ) - z‖ ^ 2 * ‖s‖ ^ 2 := hnorm
    _ ≤ 2 * z.im ^ 2 * (2 * z.im ^ 2) * ‖s‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hprod (sq_nonneg _)
    _ ≤ 2 * z.im ^ 2 * (2 * z.im ^ 2) * S :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 4 * z.im ^ 2 * (z.im ^ 2 * S) := by ring

/-- `N · (D · ⟨M⟩) = tr M` on `Idx D N`, with no condition on `D`, `N` (both sides vanish when the
index set is empty). -/
private lemma Endpoint_N_mul_D_ntr {D N : ℕ} (M : Matrix (Idx D N) (Idx D N) ℂ) :
    (N : ℂ) * ((D : ℂ) * ntr M) = M.trace := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    simp [Matrix.trace]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [Matrix.trace]
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold ntr
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  field_simp

/-- Bilinear expansion of `tr(A B C B)` for `B = Σ_x β_x E_x`. -/
private lemma Endpoint_trace_expand {D N : ℕ} (A C : Matrix (Idx D N) (Idx D N) ℂ)
    (β : Fin D → ℝ) :
    (A * (∑ x, (β x : ℂ) • Ea D N x) * C * (∑ x, (β x : ℂ) • Ea D N x)).trace =
      ∑ x, ∑ y, (β x : ℂ) * (β y : ℂ) * (A * Ea D N x * C * Ea D N y).trace := by
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ring

/-- The trace of `A B C B` for `B = Σ_x β_x E_x` through `Lmat`-type normalized traces. -/
private lemma Endpoint_trace_eq_N_mul {D N : ℕ} (A C : Matrix (Idx D N) (Idx D N) ℂ)
    (β : Fin D → ℝ) :
    (A * (∑ x, (β x : ℂ) • Ea D N x) * C * (∑ x, (β x : ℂ) • Ea D N x)).trace =
      (N : ℂ) * ∑ x, ∑ y, (β x : ℂ) * (β y : ℂ) *
        ((D : ℂ) * ntr (A * Ea D N x * C * Ea D N y)) := by
  rw [Endpoint_trace_expand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Endpoint_N_mul_D_ntr]
  ring

/-- The trace identity of the proof of Theorem 2.1 [mix]: for `B = Σ_x β_x E_x`,
`tr(Im G B Im G B) = N Σ_{x,y} β_x β_y 𝓛_{xy}`,
`𝓛 = (L(z, z̄) + L(z̄, z) - L(z, z) - L(z̄, z̄))/4` with `L` of (3.1) [def_ML]. -/
theorem trImGB_eq {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (h : Idx D N → Idx D N → ℂ)
    (z : ℂ) (β : Fin D → ℝ) :
    (((2 * Complex.I)⁻¹ • (res (Matrix.of h + Λ) z - res (Matrix.of h + Λ) (star z))) *
        (∑ x, (β x : ℂ) • Ea D N x) *
        ((2 * Complex.I)⁻¹ • (res (Matrix.of h + Λ) z - res (Matrix.of h + Λ) (star z))) *
        (∑ x, (β x : ℂ) • Ea D N x)).trace =
      (N : ℂ) * ∑ x, ∑ y, (β x : ℂ) * (β y : ℂ) * ((1 / 4 : ℂ) *
        (Lmat Λ h z (star z) x y + Lmat Λ h (star z) z x y - Lmat Λ h z z x y -
          Lmat Λ h (star z) (star z) x y)) := by
  set G₁ := res (Matrix.of h + Λ) z with hG₁
  set G₂ := res (Matrix.of h + Λ) (star z) with hG₂
  set B : Matrix (Idx D N) (Idx D N) ℂ := ∑ x, (β x : ℂ) • Ea D N x with hB
  have hc : ((2 * Complex.I)⁻¹ : ℂ) * (2 * Complex.I)⁻¹ = -(1 / 4 : ℂ) := by
    rw [← mul_inv, mul_mul_mul_comm, Complex.I_mul_I]
    norm_num
  have e1 : (((2 * Complex.I)⁻¹ • (G₁ - G₂)) * B * ((2 * Complex.I)⁻¹ • (G₁ - G₂)) * B).trace =
      -(1 / 4 : ℂ) * ((G₁ * B * G₁ * B).trace - (G₁ * B * G₂ * B).trace -
        (G₂ * B * G₁ * B).trace + (G₂ * B * G₂ * B).trace) := by
    rw [← hc]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_smul,
      Matrix.trace_sub, smul_eq_mul]
    ring
  rw [e1, Endpoint_trace_eq_N_mul, Endpoint_trace_eq_N_mul, Endpoint_trace_eq_N_mul,
    Endpoint_trace_eq_N_mul]
  simp only [Lmat, hG₁, hG₂, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- `‖E_a u‖² - 1/D = u^*(E_a - D⁻¹) u` for a unit vector `u` (Theorem 2.1 [mix]). -/
theorem blockMass_sub_eq {D N : ℕ} (u : Idx D N → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) (a : Fin D) :
    ((blockMass u a - (D : ℝ)⁻¹ : ℝ) : ℂ) =
      star u ⬝ᵥ ((Ea D N a - ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *ᵥ u) := by
  have h1 : star u ⬝ᵥ (Ea D N a *ᵥ u) = ((blockMass u a : ℝ) : ℂ) := by
    simp only [Ea, blockMass, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply,
      Fintype.sum_prod_type]
    push_cast
    rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ite_true, one_mul]
      exact Endpoint_star_mul (u (a, j))
    · intro b _ hb
      simp [hb]
    · simp
  have h2 : star u ⬝ᵥ (u : Idx D N → ℂ) = 1 := by
    have : star u ⬝ᵥ u = ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply]
      push_cast
      exact Finset.sum_congr rfl fun i _ => Endpoint_star_mul (u i)
    rw [this, hu]
    simp
  rw [Matrix.sub_mulVec, dotProduct_sub, h1, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, h2]
  push_cast
  simp

end RBMTransitionEdge

end
