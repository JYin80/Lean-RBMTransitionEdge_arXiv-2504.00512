module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Model.Deterministic
public import RBMTransitionEdge.Det.Core
public import RBMTransitionEdge.Det.Edge
public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.Det.Taylor
public import RBMTransitionEdge.Det.Density

@[expose] public section

/-!
# The shifts of the localized phase

The spectral parameter `z₁` of (5.1) [eq:z1], the shifts `Δ_ev` of (5.2)
[definition_shift_eigenvector] and `Δ_e` of (5.19) [definition_shift_eigenvalue], and Lemma A.3
[lemma_modification_of_shift]: both shifts are `γ_k - γ_k^sc` up to errors below the rigidity
scale.
-/

open MeasureTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The imaginary part `η = N^{-2/3+ε} 𝔯(k)^{-1/3}` of (5.1) [eq:z1] and (5.20) [eq:z1t]. -/
def etaK (D N k : ℕ) (ε : ℝ) : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * rk D N k ^ (-(1 / 3 : ℝ))

/-- `z₁ = γ_k + iη` of (5.1) [eq:z1], with `γ_k` the quantile (2.20) [eq:gammak] of `ρ_N`. -/
def zOne {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (k : ℕ) (ε : ℝ) : ℂ :=
  (quant (rho Λ) (D * N) k : ℂ) + (etaK D N k ε : ℂ) * Complex.I

/-- `Δ_ev(z) = Re(z + m(z) + 1/m(z))` of (5.2) [definition_shift_eigenvector]. -/
def shiftEv {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ) : ℝ :=
  (z + mExt Λ z + (mExt Λ z)⁻¹).re

/-- `Δ(t) = ⟨M_t(z_t) Λ M_t(z_t)^*⟩ / ⟨M_t(z_t) M_t(z_t)^*⟩` of (5.19)
[definition_shift_eigenvalue], with `M_t` the matrix (2.17) [def_G0] for `tΛ` and
`z_t = γ_k(t) + iη` of (5.20) [eq:z1t]. -/
def shiftT {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (k : ℕ) (ε t : ℝ) : ℝ :=
  (ntr (MExt ((t : ℂ) • Λ) (zOne ((t : ℂ) • Λ) k ε) * Λ *
      (MExt ((t : ℂ) • Λ) (zOne ((t : ℂ) • Λ) k ε))ᴴ) /
    ntr (MExt ((t : ℂ) • Λ) (zOne ((t : ℂ) • Λ) k ε) *
      (MExt ((t : ℂ) • Λ) (zOne ((t : ℂ) • Λ) k ε))ᴴ)).re

/-- `Δ_e(k, η) = ∫₀¹ Δ(t) dt` of (5.19) [definition_shift_eigenvalue]. -/
def shiftE {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (k : ℕ) (ε : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, shiftT Λ k ε t


/-! ### Spectral form of `m`, `M` for the family `tΛ` -/

attribute [local irreducible] mSol

section ShiftSpec

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `U diag(d) U^*` for a unitary `U`. -/
private def Sh_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (diagonal d)

private lemma Sh_cd_mul (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    Sh_cd U d * Sh_cd U e = Sh_cd U (fun j => d j * e j) := by
  rw [Sh_cd, Sh_cd, Sh_cd, ← map_mul, diagonal_mul_diagonal]

private lemma Sh_cd_one (U : Matrix.unitaryGroup ι ℂ) : Sh_cd U (fun _ => 1) = 1 := by
  rw [Sh_cd, diagonal_one, map_one]

private lemma Sh_cd_smul (U : Matrix.unitaryGroup ι ℂ) (c : ℂ) (d : ι → ℂ) :
    c • Sh_cd U d = Sh_cd U (fun j => c * d j) := by
  rw [Sh_cd, Sh_cd, ← map_smul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

private lemma Sh_cd_sub (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    Sh_cd U d - Sh_cd U e = Sh_cd U (fun j => d j - e j) := by
  rw [Sh_cd, Sh_cd, Sh_cd, ← map_sub, diagonal_sub]

private lemma Sh_cd_sub_smul_one (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (c : ℂ) :
    Sh_cd U d - c • (1 : Matrix ι ι ℂ) = Sh_cd U (fun j => d j - c) := by
  rw [← Sh_cd_one U, Sh_cd_smul, Sh_cd_sub]
  simp

private lemma Sh_cd_pow (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (l : ℕ) :
    Sh_cd U d ^ l = Sh_cd U (fun j => d j ^ l) := by
  rw [Sh_cd, Sh_cd, ← map_pow, diagonal_pow]
  rfl

private lemma Sh_cd_conjTranspose (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    (Sh_cd U d)ᴴ = Sh_cd U (fun j => star (d j)) := by
  rw [← star_eq_conjTranspose, Sh_cd, Sh_cd, ← map_star, star_eq_conjTranspose,
    diagonal_conjTranspose]
  rfl

private lemma Sh_ntr_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    ntr (Sh_cd U d) = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, d j := by
  rw [ntr, Sh_cd, Unitary.conjStarAlgAut_apply, trace_mul_comm, ← mul_assoc,
    Unitary.star_mul_self_of_mem U.property, one_mul, trace_diagonal]

private lemma Sh_cd_inv (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (h : ∀ j, d j ≠ 0) :
    (Sh_cd U d)⁻¹ = Sh_cd U (fun j => (d j)⁻¹) := by
  apply inv_eq_right_inv
  rw [Sh_cd_mul]
  simp only [mul_inv_cancel₀ (h _)]
  exact Sh_cd_one U

private lemma Sh_cd_real_smul (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (s : ℝ) :
    (s : ℂ) • Sh_cd U (fun j => (μ j : ℂ)) = Sh_cd U (fun j => ((s * μ j : ℝ) : ℂ)) := by
  rw [Sh_cd_smul]
  congr 1
  funext j
  push_cast
  ring

/-- Every eigenvalue of a Hermitian matrix is bounded by the operator norm. -/
private lemma Sh_eig_le {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (j : ι) :
    |hΛ.eigenvalues j| ≤ opNorm Λ := by
  have hv : ‖hΛ.eigenvectorBasis j‖ = 1 := hΛ.eigenvectorBasis.norm_eq_one j
  have hT : Matrix.toEuclideanCLM (𝕜 := ℂ) Λ (hΛ.eigenvectorBasis j) =
      ((hΛ.eigenvalues j : ℂ)) • hΛ.eigenvectorBasis j := by
    apply WithLp.ofLp_injective
    rw [Matrix.ofLp_toEuclideanCLM, hΛ.mulVec_eigenvectorBasis, WithLp.ofLp_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have := (Matrix.toEuclideanCLM (𝕜 := ℂ) Λ).le_opNorm (hΛ.eigenvectorBasis j)
  rw [hT, norm_smul, hv, mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
  exact this

/-- A Hermitian matrix is `U diag(μ) U^*` with real `μ`, `|μ_j| ≤ ‖Λ‖`. -/
private lemma Sh_decomp {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ),
      Λ = Sh_cd U (fun j => (μ j : ℂ)) ∧ ∀ j, |μ j| ≤ opNorm Λ :=
  ⟨_, _, hΛ.spectral_theorem, Sh_eig_le hΛ⟩

private lemma Sh_herm_smul {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (t : ℝ) :
    ((t : ℂ) • Λ).IsHermitian :=
  hΛ.smul (by simp [IsSelfAdjoint])

private lemma Sh_opNorm_smul (Λ : Matrix ι ι ℂ) (t : ℝ) :
    opNorm ((t : ℂ) • Λ) = |t| * opNorm Λ := by
  unfold opNorm
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]

private lemma Sh_ne_of_im (x : ℝ) {w : ℂ} (h : 0 < w.im) : (x : ℂ) - w ≠ 0 := by
  intro e
  have := congrArg Complex.im e
  simp at this
  linarith

/-- The spectral form of `m_t(z)` and `M_t(z)` for `Λ = U diag(μ) U^*` and `Im z > 0`:
`m = n⁻¹ Σ_j (tμ_j - w)⁻¹` with `w = z + m`, and `M = U diag((tμ_j - w)⁻¹) U^*`. -/
private lemma Sh_bridge [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (t : ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    0 < (mSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z).im ∧
      mSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z = ((Fintype.card ι : ℂ))⁻¹ *
        ∑ j, (((t * μ j : ℝ) : ℂ) - (z + mSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z))⁻¹ ∧
      MSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z = Sh_cd U (fun j =>
        (((t * μ j : ℝ) : ℂ) - (z + mSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z))⁻¹) := by
  have hH : ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))).IsHermitian := by
    rw [Sh_cd_real_smul]
    have : (Sh_cd U (fun j => ((t * μ j : ℝ) : ℂ))) =
        Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (diagonal (fun j => ((t * μ j : ℝ) : ℂ))) := rfl
    rw [this, Unitary.conjStarAlgAut_apply]
    refine (isHermitian_diagonal_of_self_adjoint _ ?_).isSelfAdjoint.conjugate _ |>.isHermitian
    ext j; simp
  obtain ⟨h1, h2, -⟩ := mSol_spec _ hH z hz
  set m := mSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z
  have hw : 0 < (z + m).im := by simp; linarith
  have hM : MSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z =
      Sh_cd U (fun j => (((t * μ j : ℝ) : ℂ) - (z + m))⁻¹) := by
    show ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)) - (z + m) • (1 : Matrix ι ι ℂ))⁻¹ = _
    rw [Sh_cd_real_smul, Sh_cd_sub_smul_one, Sh_cd_inv _ _ fun j => Sh_ne_of_im _ hw]
  refine ⟨h1, ?_, hM⟩
  calc m = ntr (MSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z) := h2
    _ = _ := by rw [hM, Sh_ntr_cd]

end ShiftSpec

/-! ### Scalar estimates for the normalized sums over the spectrum of `tΛ` -/

section ShiftScalar

variable {ι : Type*} [Fintype ι]

/-- `|ν - w| ≥ (8/9)|w| ≥ 4/5` for `|ν| ≤ 1/10 ≤ |w| - 4/5`. -/
private lemma Sh_res_bd (x : ℝ) {w : ℂ} (hx : |x| ≤ 1 / 10) (hw : 9 / 10 ≤ ‖w‖) :
    (x : ℂ) - w ≠ 0 ∧ ‖((x : ℂ) - w)⁻¹‖ ≤ 5 / 4 ∧ ‖((x : ℂ) - w)⁻¹‖ * ‖w‖ ≤ 9 / 8 := by
  have h1 : ‖w‖ - |x| ≤ ‖(x : ℂ) - w‖ := by
    have := norm_sub_norm_le w (x : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    rw [norm_sub_rev]; linarith
  have h2 : 8 / 9 * ‖w‖ ≤ ‖(x : ℂ) - w‖ := by linarith
  have h3 : (0 : ℝ) < ‖(x : ℂ) - w‖ := by nlinarith
  refine ⟨norm_pos_iff.1 h3, ?_, ?_⟩
  · rw [norm_inv]
    rw [inv_le_comm₀ h3 (by norm_num)]
    nlinarith
  · rw [norm_inv, inv_mul_le_iff₀ h3]
    nlinarith

/-- `w (ν - w)⁻¹ = -1 + ν (ν - w)⁻¹`. -/
private lemma Sh_X_eq (x : ℝ) {w : ℂ} (h : (x : ℂ) - w ≠ 0) :
    w * ((x : ℂ) - w)⁻¹ = -1 + (x : ℂ) * ((x : ℂ) - w)⁻¹ := by
  field_simp
  ring

/-- `|ν (ν - w)⁻¹| ≤ (5/4)|ν| ≤ 1/8`. -/
private lemma Sh_nua_bd (x : ℝ) {w : ℂ} (hx : |x| ≤ 1 / 10) (hw : 9 / 10 ≤ ‖w‖) :
    ‖(x : ℂ) * ((x : ℂ) - w)⁻¹‖ ≤ 5 / 4 * |x| ∧ ‖(x : ℂ) * ((x : ℂ) - w)⁻¹‖ ≤ 1 / 8 ∧
      (x : ℂ) - w ≠ 0 := by
  obtain ⟨hne, h2, -⟩ := Sh_res_bd x hx hw
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨?_, ?_, hne⟩
  · nlinarith [abs_nonneg x]
  · nlinarith [abs_nonneg x]

/-- `| |X|² - |Y|² | ≤ |X - Y| (|X| + |Y|)`. -/
private lemma Sh_sq_sub (X Y : ℂ) : |‖X‖ ^ 2 - ‖Y‖ ^ 2| ≤ ‖X - Y‖ * (‖X‖ + ‖Y‖) := by
  have h := abs_norm_sub_norm_le X Y
  rw [show ‖X‖ ^ 2 - ‖Y‖ ^ 2 = (‖X‖ - ‖Y‖) * (‖X‖ + ‖Y‖) by ring, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖X‖ + ‖Y‖)]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- A weighted average `Σ μ f / Σ f` with weights `f_j ∈ [3/4, 4/3]`, `|f_j - 1| ≤ c₁|μ_j|`,
`Σ μ = 0`, is at most `(4/3) c₁ n⁻¹ Σ μ²`. -/
private lemma Sh_wavg_bd [Nonempty ι] (μ f : ι → ℝ) (c₁ : ℝ) (hc₁ : 0 ≤ c₁) (hμ0 : ∑ j, μ j = 0)
    (hf : ∀ j, 3 / 4 ≤ f j) (hf1 : ∀ j, |f j - 1| ≤ c₁ * |μ j|) :
    |(∑ j, μ j * f j) / ∑ j, f j| ≤
      4 / 3 * c₁ * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hS : 3 / 4 * (Fintype.card ι : ℝ) ≤ ∑ j, f j := by
    calc 3 / 4 * (Fintype.card ι : ℝ) = ∑ _j : ι, (3 / 4 : ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j _ => hf j
  have hS0 : 0 < ∑ j, f j := by linarith
  have e : ∑ j, μ j * f j = ∑ j, μ j * (f j - 1) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hμ0, sub_zero]
  have h1 : |∑ j, μ j * (f j - 1)| ≤ c₁ * ∑ j, μ j ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    calc |μ j| * |f j - 1| ≤ |μ j| * (c₁ * |μ j|) := by gcongr; exact hf1 j
      _ = c₁ * μ j ^ 2 := by rw [← sq_abs (μ j)]; ring
  rw [e, abs_div, abs_of_pos hS0, div_le_iff₀ hS0]
  have hsq : 0 ≤ ∑ j, μ j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  calc |∑ j, μ j * (f j - 1)| ≤ c₁ * ∑ j, μ j ^ 2 := h1
    _ = 4 / 3 * c₁ * ((Fintype.card ι : ℝ)⁻¹ * ∑ j, μ j ^ 2) * (3 / 4 * Fintype.card ι) := by
        field_simp
    _ ≤ _ := by gcongr

end ShiftScalar

section ShiftScalar2

variable {ι : Type*} [Fintype ι]

/-- Lipschitz bound for weighted averages: weights `f, g ∈ [3/4, 4/3]` with `|g_j - 1| ≤ c₁|μ_j|`
and `|f_j - g_j| ≤ c₂ |μ_j| δ`, `Σ μ = 0`, `|μ_j| ≤ 1/10`. -/
private lemma Sh_wavg_lip [Nonempty ι] (μ f g : ι → ℝ) (c₁ c₂ δ : ℝ) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hδ : 0 ≤ δ) (hμ0 : ∑ j, μ j = 0) (hμ : ∀ j, |μ j| ≤ 1 / 10)
    (hf : ∀ j, 3 / 4 ≤ f j) (hg : ∀ j, 3 / 4 ≤ g j) (hg' : ∀ j, g j ≤ 4 / 3)
    (hg1 : ∀ j, |g j - 1| ≤ c₁ * |μ j|) (hfg : ∀ j, |f j - g j| ≤ c₂ * |μ j| * δ) :
    |(∑ j, μ j * f j) / (∑ j, f j) - (∑ j, μ j * g j) / (∑ j, g j)| ≤
      16 / 9 * c₂ * (4 / 3 + c₁ / 10) * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) * δ := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hSf : 3 / 4 * n ≤ ∑ j, f j := by
    calc 3 / 4 * n = ∑ _j : ι, (3 / 4 : ℝ) := by simp [n, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j _ => hf j
  have hSg : 3 / 4 * n ≤ ∑ j, g j := by
    calc 3 / 4 * n = ∑ _j : ι, (3 / 4 : ℝ) := by simp [n, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j _ => hg j
  have hSg' : ∑ j, g j ≤ 4 / 3 * n := by
    calc ∑ j, g j ≤ ∑ _j : ι, (4 / 3 : ℝ) := Finset.sum_le_sum fun j _ => hg' j
      _ = 4 / 3 * n := by simp [n, mul_comm]
  set Q := ∑ j, μ j ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => sq_nonneg _
  have e1 : ∑ j, μ j * g j = ∑ j, μ j * (g j - 1) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hμ0, sub_zero]
  have b1 : |∑ j, μ j * (f j - g j)| ≤ c₂ * δ * Q := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hQ, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    calc |μ j| * |f j - g j| ≤ |μ j| * (c₂ * |μ j| * δ) := by gcongr; exact hfg j
      _ = c₂ * δ * μ j ^ 2 := by rw [← sq_abs (μ j)]; ring
  have b2 : |∑ j, μ j * (g j - 1)| ≤ c₁ * Q := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hQ, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    calc |μ j| * |g j - 1| ≤ |μ j| * (c₁ * |μ j|) := by gcongr; exact hg1 j
      _ = c₁ * μ j ^ 2 := by rw [← sq_abs (μ j)]; ring
  have b3 : |(∑ j, g j) - ∑ j, f j| ≤ c₂ * δ * (n / 10) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |g j - f j| ≤ ∑ _j : ι, c₂ * δ * (1 / 10) := Finset.sum_le_sum fun j _ => by
          rw [abs_sub_comm]
          calc |f j - g j| ≤ c₂ * |μ j| * δ := hfg j
            _ ≤ c₂ * (1 / 10) * δ := by gcongr; exact hμ j
            _ = c₂ * δ * (1 / 10) := by ring
      _ = c₂ * δ * (n / 10) := by simp [n]; ring
  have hF0 : 0 < ∑ j, f j := by linarith
  have hG0 : 0 < ∑ j, g j := by linarith
  have key : (∑ j, μ j * f j) / (∑ j, f j) - (∑ j, μ j * g j) / (∑ j, g j) =
      ((∑ j, μ j * (f j - g j)) * (∑ j, g j) + (∑ j, μ j * (g j - 1)) * ((∑ j, g j) - ∑ j, f j)) /
        ((∑ j, f j) * ∑ j, g j) := by
    rw [← e1]
    have : ∑ j, μ j * (f j - g j) = (∑ j, μ j * f j) - ∑ j, μ j * g j := by
      rw [← Finset.sum_sub_distrib]; congr 1; funext j; ring
    rw [this]
    field_simp
    ring
  rw [key, abs_div, abs_of_pos (mul_pos hF0 hG0), div_le_iff₀ (mul_pos hF0 hG0)]
  have hnum : |(∑ j, μ j * (f j - g j)) * (∑ j, g j) + (∑ j, μ j * (g j - 1)) *
      ((∑ j, g j) - ∑ j, f j)| ≤ c₂ * δ * Q * (4 / 3 * n) + c₁ * Q * (c₂ * δ * (n / 10)) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hG0]
    gcongr
  refine hnum.trans ?_
  have hden : (3 / 4 * n) * (3 / 4 * n) ≤ (∑ j, f j) * ∑ j, g j := by
    gcongr
  calc c₂ * δ * Q * (4 / 3 * n) + c₁ * Q * (c₂ * δ * (n / 10))
      = 16 / 9 * c₂ * (4 / 3 + c₁ / 10) * (n⁻¹ * Q) * δ * ((3 / 4 * n) * (3 / 4 * n)) := by
        field_simp; ring
    _ ≤ _ := by gcongr

end ShiftScalar2

section ShiftScalar3

variable {ι : Type*} [Fintype ι]

/-- `X = w (x - w)⁻¹`: `|X + 1| ≤ (5/4)|x|`, `7/8 ≤ |X| ≤ 9/8`, `|X|² ∈ [3/4, 4/3]`,
`||X|² - 1| ≤ (85/32)|x|`. -/
private lemma Sh_X_bd (x : ℝ) {w : ℂ} (hx : |x| ≤ 1 / 10) (hw : 9 / 10 ≤ ‖w‖) :
    ‖w * ((x : ℂ) - w)⁻¹ + 1‖ ≤ 5 / 4 * |x| ∧ 7 / 8 ≤ ‖w * ((x : ℂ) - w)⁻¹‖ ∧
      ‖w * ((x : ℂ) - w)⁻¹‖ ≤ 9 / 8 ∧ 3 / 4 ≤ ‖w * ((x : ℂ) - w)⁻¹‖ ^ 2 ∧
      ‖w * ((x : ℂ) - w)⁻¹‖ ^ 2 ≤ 4 / 3 ∧ |‖w * ((x : ℂ) - w)⁻¹‖ ^ 2 - 1| ≤ 85 / 32 * |x| ∧
      (x : ℂ) - w ≠ 0 := by
  obtain ⟨hne, -, -⟩ := Sh_res_bd x hx hw
  obtain ⟨h1, h2, -⟩ := Sh_nua_bd x hx hw
  rw [Sh_X_eq x hne]
  set v := (x : ℂ) * ((x : ℂ) - w)⁻¹
  have e1 : -1 + v + 1 = v := by ring
  have hlo : 7 / 8 ≤ ‖-1 + v‖ := by
    have := norm_sub_norm_le (-1 : ℂ) (-v)
    rw [norm_neg, norm_neg, norm_one, sub_neg_eq_add] at this
    linarith
  have hhi : ‖-1 + v‖ ≤ 9 / 8 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_one]; linarith
  refine ⟨by rw [e1]; exact h1, hlo, hhi, by nlinarith, by nlinarith, ?_, hne⟩
  have := Sh_sq_sub (-1 + v) (-1)
  rw [norm_neg, norm_one, one_pow, sub_neg_eq_add, e1] at this
  refine this.trans ?_
  calc ‖v‖ * (‖-1 + v‖ + 1) ≤ 5 / 4 * |x| * (9 / 8 + 1) := by gcongr
    _ = 85 / 32 * |x| := by ring

variable [DecidableEq ι]

/-- `⟨M_t Λ M_t^*⟩ / ⟨M_t M_t^*⟩` in spectral form, at `w = z + m_t(z)`. -/
private def Sh_R (μ : ι → ℝ) (t : ℝ) (w : ℂ) : ℝ :=
  (∑ j, μ j * ‖(((t * μ j : ℝ) : ℂ) - w)⁻¹‖ ^ 2) / ∑ j, ‖(((t * μ j : ℝ) : ℂ) - w)⁻¹‖ ^ 2

/-- `⟨Λ M_t²⟩ / ⟨M_t²⟩` in spectral form. -/
private def Sh_S (μ : ι → ℝ) (t : ℝ) (w : ℂ) : ℂ :=
  (∑ j, (μ j : ℂ) * (((t * μ j : ℝ) : ℂ) - w)⁻¹ ^ 2) / ∑ j, (((t * μ j : ℝ) : ℂ) - w)⁻¹ ^ 2

private lemma Sh_R_X (μ : ι → ℝ) (t : ℝ) {w : ℂ} (hw : w ≠ 0) :
    Sh_R μ t w = (∑ j, μ j * ‖w * (((t * μ j : ℝ) : ℂ) - w)⁻¹‖ ^ 2) /
      ∑ j, ‖w * (((t * μ j : ℝ) : ℂ) - w)⁻¹‖ ^ 2 := by
  have hw' : 0 < ‖w‖ ^ 2 := by positivity
  simp only [norm_mul, mul_pow, Sh_R]
  rw [← Finset.mul_sum]
  have : ∑ j, μ j * (‖w‖ ^ 2 * ‖(((t * μ j : ℝ) : ℂ) - w)⁻¹‖ ^ 2) =
      ‖w‖ ^ 2 * ∑ j, μ j * ‖(((t * μ j : ℝ) : ℂ) - w)⁻¹‖ ^ 2 := by
    rw [Finset.mul_sum]; congr 1; funext j; ring
  rw [this, mul_div_mul_left _ _ hw'.ne']

private lemma Sh_abs_tmu {μ : ι → ℝ} {t : ℝ} (hμ : ∀ j, |μ j| ≤ 1 / 10) (ht : |t| ≤ 1) (j : ι) :
    |t * μ j| ≤ |μ j| ∧ |t * μ j| ≤ 1 / 10 := by
  rw [abs_mul]
  constructor
  · calc |t| * |μ j| ≤ 1 * |μ j| := by gcongr
      _ = |μ j| := one_mul _
  · calc |t| * |μ j| ≤ 1 * (1 / 10) := by gcongr; exact hμ j
      _ = 1 / 10 := by ring

/-- `|⟨M Λ M^*⟩/⟨M M^*⟩| ≤ 4 ⟨Λ²⟩` when `⟨Λ⟩ = 0`. -/
private lemma Sh_R_bd [Nonempty ι] (μ : ι → ℝ) (t : ℝ) {w : ℂ} (hμ0 : ∑ j, μ j = 0)
    (hμ : ∀ j, |μ j| ≤ 1 / 10) (ht : |t| ≤ 1) (hw : 9 / 10 ≤ ‖w‖) :
    |Sh_R μ t w| ≤ 4 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) := by
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
  rw [Sh_R_X μ t hw0]
  have := Sh_wavg_bd μ (fun j => ‖w * (((t * μ j : ℝ) : ℂ) - w)⁻¹‖ ^ 2) (85 / 32) (by norm_num)
    hμ0 (fun j => (Sh_X_bd _ (Sh_abs_tmu hμ ht j).2 hw).2.2.2.1)
    (fun j => (Sh_X_bd _ (Sh_abs_tmu hμ ht j).2 hw).2.2.2.2.2.1.trans
      (mul_le_mul_of_nonneg_left (Sh_abs_tmu hμ ht j).1 (by norm_num)))
  refine this.trans ?_
  have : 0 ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 := by positivity
  nlinarith

/-- `|⟨MΛM^*⟩/⟨MM^*⟩(w₁) - ⟨MΛM^*⟩/⟨MM^*⟩(w₂)| ≤ 10 ⟨Λ²⟩ |w₁ - w₂|` when `⟨Λ⟩ = 0`. -/
private lemma Sh_R_lip [Nonempty ι] (μ : ι → ℝ) (t : ℝ) {w₁ w₂ : ℂ} (hμ0 : ∑ j, μ j = 0)
    (hμ : ∀ j, |μ j| ≤ 1 / 10) (ht : |t| ≤ 1) (hw₁ : 9 / 10 ≤ ‖w₁‖) (hw₂ : 9 / 10 ≤ ‖w₂‖) :
    |Sh_R μ t w₁ - Sh_R μ t w₂| ≤
      10 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) * ‖w₁ - w₂‖ := by
  have hw0₁ : w₁ ≠ 0 := fun h => by rw [h, norm_zero] at hw₁; linarith
  have hw0₂ : w₂ ≠ 0 := fun h => by rw [h, norm_zero] at hw₂; linarith
  rw [Sh_R_X μ t hw0₁, Sh_R_X μ t hw0₂]
  have hx := fun j => (Sh_abs_tmu hμ ht j)
  have hfg : ∀ j, |‖w₁ * (((t * μ j : ℝ) : ℂ) - w₁)⁻¹‖ ^ 2 -
      ‖w₂ * (((t * μ j : ℝ) : ℂ) - w₂)⁻¹‖ ^ 2| ≤ 225 / 64 * |μ j| * ‖w₁ - w₂‖ := by
    intro j
    obtain ⟨hn₁, ha₁, -⟩ := Sh_res_bd _ (hx j).2 hw₁
    obtain ⟨hn₂, ha₂, -⟩ := Sh_res_bd _ (hx j).2 hw₂
    have X₁ := Sh_X_bd _ (hx j).2 hw₁
    have X₂ := Sh_X_bd _ (hx j).2 hw₂
    refine (Sh_sq_sub _ _).trans ?_
    rw [Sh_X_eq _ hn₁, Sh_X_eq _ hn₂]
    have e : -1 + ((t * μ j : ℝ) : ℂ) * (((t * μ j : ℝ) : ℂ) - w₁)⁻¹ -
        (-1 + ((t * μ j : ℝ) : ℂ) * (((t * μ j : ℝ) : ℂ) - w₂)⁻¹) =
        ((t * μ j : ℝ) : ℂ) * ((w₁ - w₂) * ((((t * μ j : ℝ) : ℂ) - w₁)⁻¹ *
          (((t * μ j : ℝ) : ℂ) - w₂)⁻¹)) := by
      field_simp; ring
    rw [e, ← Sh_X_eq _ hn₁, ← Sh_X_eq _ hn₂]
    have hA : ‖((t * μ j : ℝ) : ℂ) * ((w₁ - w₂) * ((((t * μ j : ℝ) : ℂ) - w₁)⁻¹ *
        (((t * μ j : ℝ) : ℂ) - w₂)⁻¹))‖ ≤ |μ j| * (‖w₁ - w₂‖ * (5 / 4 * (5 / 4))) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul (hx j).1 ?_ (by positivity) (abs_nonneg _)
      gcongr
    calc _ ≤ |μ j| * (‖w₁ - w₂‖ * (5 / 4 * (5 / 4))) * (9 / 8 + 9 / 8) := by
          refine mul_le_mul hA ?_ (by positivity) (by positivity)
          linarith [X₁.2.2.1, X₂.2.2.1]
      _ = 225 / 64 * |μ j| * ‖w₁ - w₂‖ := by ring
  have := Sh_wavg_lip μ (fun j => ‖w₁ * (((t * μ j : ℝ) : ℂ) - w₁)⁻¹‖ ^ 2)
    (fun j => ‖w₂ * (((t * μ j : ℝ) : ℂ) - w₂)⁻¹‖ ^ 2) (85 / 32) (225 / 64) ‖w₁ - w₂‖
    (by norm_num) (by norm_num) (norm_nonneg _) hμ0 hμ
    (fun j => (Sh_X_bd _ (hx j).2 hw₁).2.2.2.1) (fun j => (Sh_X_bd _ (hx j).2 hw₂).2.2.2.1)
    (fun j => (Sh_X_bd _ (hx j).2 hw₂).2.2.2.2.1)
    (fun j => (Sh_X_bd _ (hx j).2 hw₂).2.2.2.2.2.1.trans
      (mul_le_mul_of_nonneg_left (hx j).1 (by norm_num))) hfg
  refine this.trans ?_
  have : 0 ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 := by positivity
  have h2 : 0 ≤ ‖w₁ - w₂‖ := norm_nonneg _
  have : 16 / 9 * (225 / 64 : ℝ) * (4 / 3 + 85 / 32 / 10) ≤ 10 := by norm_num
  nlinarith [mul_nonneg ‹0 ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2› h2]

end ShiftScalar3

section ShiftScalar4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma Sh_im_inv (x : ℝ) (w : ℂ) :
    (((x : ℂ) - w)⁻¹).im = w.im * ‖((x : ℂ) - w)⁻¹‖ ^ 2 := by
  rw [norm_inv, inv_pow, Complex.sq_norm, Complex.inv_im]
  simp [div_eq_mul_inv]

/-- `|⟨ΛM²⟩/⟨M²⟩ - ⟨MΛM^*⟩/⟨MM^*⟩| ≤ 8 ⟨Λ²⟩ |Im w|` when `⟨Λ⟩ = 0`. -/
private lemma Sh_RS [Nonempty ι] (μ : ι → ℝ) (t : ℝ) {w : ℂ} (hμ0 : ∑ j, μ j = 0)
    (hμ : ∀ j, |μ j| ≤ 1 / 10) (ht : |t| ≤ 1) (hw : 9 / 10 ≤ ‖w‖) :
    ‖Sh_S μ t w - (Sh_R μ t w : ℂ)‖ ≤
      8 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) * |w.im| := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
  have hx := fun j => Sh_abs_tmu hμ ht j
  set X : ι → ℂ := fun j => w * (((t * μ j : ℝ) : ℂ) - w)⁻¹ with hX
  set R := Sh_R μ t w with hRdef
  have hR : R = (∑ j, μ j * ‖X j‖ ^ 2) / ∑ j, ‖X j‖ ^ 2 := Sh_R_X μ t hw0
  have hRb : |R| ≤ 4 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) := Sh_R_bd μ t hμ0 hμ ht hw
  have hXb := fun j => Sh_X_bd _ (hx j).2 hw
  have hpos : 0 < ∑ j, ‖X j‖ ^ 2 := Finset.sum_pos (fun j _ => by
    have := (hXb j).2.2.2.1; simp only [hX]; linarith) Finset.univ_nonempty
  have hzero : ∑ j, (μ j - R) * ‖X j‖ ^ 2 = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hR, div_mul_cancel₀ _ hpos.ne']
    exact sub_self _
  -- the real part of `Σ X²` is at least `0.7 n`
  have hre : ∀ j, 7 / 10 ≤ ((X j) ^ 2).re := by
    intro j
    obtain ⟨hne, -, -⟩ := Sh_res_bd _ (hx j).2 hw
    obtain ⟨-, h2, -⟩ := Sh_nua_bd _ (hx j).2 hw
    have e : X j = -1 + ((t * μ j : ℝ) : ℂ) * (((t * μ j : ℝ) : ℂ) - w)⁻¹ := Sh_X_eq _ hne
    set v := ((t * μ j : ℝ) : ℂ) * (((t * μ j : ℝ) : ℂ) - w)⁻¹
    rw [e]
    have : ((-1 + v) ^ 2).re = 1 - 2 * v.re + (v ^ 2).re := by
      simp [sq]; ring
    rw [this]
    have h3 := Complex.re_le_norm v
    have h4 : |(v ^ 2).re| ≤ ‖v‖ ^ 2 := by rw [← norm_pow]; exact Complex.abs_re_le_norm _
    nlinarith [abs_le.1 h4, norm_nonneg v]
  have hsumre : 7 / 10 * (Fintype.card ι : ℝ) ≤ (∑ j, X j ^ 2).re := by
    rw [Complex.re_sum]
    calc 7 / 10 * (Fintype.card ι : ℝ) = ∑ _j : ι, (7 / 10 : ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j _ => hre j
  have hsum0 : 7 / 10 * (Fintype.card ι : ℝ) ≤ ‖∑ j, X j ^ 2‖ :=
    hsumre.trans (Complex.re_le_norm _)
  have hsumne : ∑ j, X j ^ 2 ≠ 0 := fun h => by rw [h, norm_zero] at hsum0; linarith
  have hS : Sh_S μ t w = (∑ j, (μ j : ℂ) * X j ^ 2) / ∑ j, X j ^ 2 := by
    have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
    simp only [Sh_S, hX, mul_pow]
    rw [← Finset.mul_sum]
    have : ∑ j, (μ j : ℂ) * (w ^ 2 * (((t * μ j : ℝ) : ℂ) - w)⁻¹ ^ 2) =
        w ^ 2 * ∑ j, (μ j : ℂ) * (((t * μ j : ℝ) : ℂ) - w)⁻¹ ^ 2 := by
      rw [Finset.mul_sum]; congr 1; funext j; ring
    rw [this, mul_div_mul_left _ _ hw2]
  have key : Sh_S μ t w - (R : ℂ) =
      (∑ j, ((μ j - R : ℝ) : ℂ) * (X j ^ 2 - ((‖X j‖ ^ 2 : ℝ) : ℂ))) / ∑ j, X j ^ 2 := by
    rw [hS, eq_div_iff hsumne, sub_mul, div_mul_cancel₀ _ hsumne]
    have h0 : ∑ j, ((μ j - R : ℝ) : ℂ) * ((‖X j‖ ^ 2 : ℝ) : ℂ) = 0 := by
      have := congrArg (fun r : ℝ => (r : ℂ)) hzero
      simpa [Complex.ofReal_sum] using this
    simp only [mul_sub, Finset.sum_sub_distrib, h0, sub_zero]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1; funext j; push_cast; ring
  rw [key, norm_div]
  have hterm : ∀ j, ‖((μ j - R : ℝ) : ℂ) * (X j ^ 2 - ((‖X j‖ ^ 2 : ℝ) : ℂ))‖ ≤
      225 / 64 * |w.im| * (μ j ^ 2 + |R| * (1 / 10)) := by
    intro j
    have hn2 : (‖X j‖ ^ 2 : ℝ) = (X j).re ^ 2 + (X j).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have e1 : X j ^ 2 - ((‖X j‖ ^ 2 : ℝ) : ℂ) = X j * (2 * Complex.I * ((X j).im : ℂ)) := by
      rw [hn2]
      apply Complex.ext <;> simp [sq] <;> ring
    obtain ⟨hne, ha, -⟩ := Sh_res_bd _ (hx j).2 hw
    have him : (X j).im = (t * μ j) * (w.im * ‖(((t * μ j : ℝ) : ℂ) - w)⁻¹‖ ^ 2) := by
      have e : X j = -1 + ((t * μ j : ℝ) : ℂ) * (((t * μ j : ℝ) : ℂ) - w)⁻¹ := Sh_X_eq _ hne
      rw [e, Complex.add_im, Complex.im_ofReal_mul, Sh_im_inv]; simp
    have him' : |(X j).im| ≤ |μ j| * (|w.im| * (25 / 16)) := by
      rw [him, abs_mul (t * μ j), abs_mul w.im, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖(((t * μ j : ℝ) : ℂ) - w)⁻¹‖ ^ 2)]
      refine mul_le_mul (hx j).1 ?_ (by positivity) (abs_nonneg _)
      gcongr
      nlinarith [norm_nonneg ((((t * μ j : ℝ) : ℂ) - w)⁻¹)]
    have hnorm : ‖((μ j - R : ℝ) : ℂ) * (X j * (2 * Complex.I * ((X j).im : ℂ)))‖ =
        |μ j - R| * (‖X j‖ * (2 * 1 * |(X j).im|)) := by
      rw [norm_mul (((μ j - R : ℝ) : ℂ)), norm_mul (X j), norm_mul (2 * Complex.I),
        norm_mul (2 : ℂ), Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, Complex.norm_two]
    rw [e1, hnorm]
    have h1 : |μ j - R| * |μ j| ≤ μ j ^ 2 + |R| * (1 / 10) := by
      have := abs_sub (μ j) R
      have hm := hμ j
      calc |μ j - R| * |μ j| ≤ (|μ j| + |R|) * |μ j| := by gcongr
        _ = |μ j| ^ 2 + |R| * |μ j| := by ring
        _ ≤ μ j ^ 2 + |R| * (1 / 10) := by rw [sq_abs]; gcongr
    have h2 : ‖X j‖ ≤ 9 / 8 := (hXb j).2.2.1
    calc |μ j - R| * (‖X j‖ * (2 * 1 * |(X j).im|))
        ≤ |μ j - R| * (9 / 8 * (2 * 1 * (|μ j| * (|w.im| * (25 / 16))))) := by gcongr
      _ = 225 / 64 * |w.im| * (|μ j - R| * |μ j|) := by ring
      _ ≤ 225 / 64 * |w.im| * (μ j ^ 2 + |R| * (1 / 10)) := by gcongr
  have hnum : ‖∑ j, ((μ j - R : ℝ) : ℂ) * (X j ^ 2 - ((‖X j‖ ^ 2 : ℝ) : ℂ))‖ ≤
      225 / 64 * |w.im| * ((∑ j, μ j ^ 2) + (Fintype.card ι : ℝ) * (|R| * (1 / 10))) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => hterm j).trans ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp
  rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖∑ j, X j ^ 2‖)]
  refine hnum.trans ?_
  set σ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hQ : ∑ j, μ j ^ 2 = (Fintype.card ι : ℝ) * σ := by rw [hσ]; field_simp
  rw [hQ]
  have hy := abs_nonneg w.im
  calc 225 / 64 * |w.im| * ((Fintype.card ι : ℝ) * σ + (Fintype.card ι : ℝ) * (|R| * (1 / 10)))
      ≤ 225 / 64 * |w.im| * ((Fintype.card ι : ℝ) * σ +
          (Fintype.card ι : ℝ) * (4 * σ * (1 / 10))) := by gcongr
    _ ≤ 8 * σ * |w.im| * (7 / 10 * (Fintype.card ι : ℝ)) := by
        have : 0 ≤ |w.im| * ((Fintype.card ι : ℝ) * σ) := by positivity
        nlinarith
    _ ≤ 8 * σ * |w.im| * ‖∑ j, X j ^ 2‖ := by gcongr

end ShiftScalar4

section ShiftScalar5

variable {ι : Type*} [Fintype ι]

/-- With `m = n⁻¹ Σ_j (tμ_j - w)⁻¹`, `Σ μ = 0`: `|w m + 1| ≤ (5/4)⟨Λ²⟩/|w|`, `|w m| ≥ 7/8`,
`|w + 1/m| ≤ (10/7)⟨Λ²⟩` and `|m² - n⁻¹ Σ_j (tμ_j - w)⁻²| ≤ 4⟨Λ²⟩`. -/
private lemma Sh_m_bd [Nonempty ι] (μ : ι → ℝ) (t : ℝ) {w : ℂ} (hμ0 : ∑ j, μ j = 0)
    (hμ : ∀ j, |μ j| ≤ 1 / 10) (ht : |t| ≤ 1) (hw : 9 / 10 ≤ ‖w‖) :
    ‖w * (((Fintype.card ι : ℂ))⁻¹ * ∑ j, (((t * μ j : ℝ) : ℂ) - w)⁻¹) + 1‖ ≤
        5 / 4 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) / ‖w‖ ∧
      7 / 8 ≤ ‖w * (((Fintype.card ι : ℂ))⁻¹ * ∑ j, (((t * μ j : ℝ) : ℂ) - w)⁻¹)‖ ∧
      ‖w + (((Fintype.card ι : ℂ))⁻¹ * ∑ j, (((t * μ j : ℝ) : ℂ) - w)⁻¹)⁻¹‖ ≤
        10 / 7 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) ∧
      ‖(((Fintype.card ι : ℂ))⁻¹ * ∑ j, (((t * μ j : ℝ) : ℂ) - w)⁻¹) ^ 2 -
          ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (((t * μ j : ℝ) : ℂ) - w)⁻¹ ^ 2‖ ≤
        4 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) ∧
      ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (((t * μ j : ℝ) : ℂ) - w)⁻¹ ≠ 0 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
  have hwpos : 0 < ‖w‖ := by linarith
  have hx := fun j => Sh_abs_tmu hμ ht j
  set c : ℂ := ((Fintype.card ι : ℂ))⁻¹ with hc
  have hcn : ‖c‖ = ((Fintype.card ι : ℝ))⁻¹ := by
    rw [hc, norm_inv, Complex.norm_natCast]
  set σ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 with hσ
  have hσ0 : 0 ≤ σ := by positivity
  set a : ι → ℂ := fun j => (((t * μ j : ℝ) : ℂ) - w)⁻¹ with ha
  set b : ι → ℂ := fun j => ((t * μ j : ℝ) : ℂ) * a j / w with hb
  have hab : ∀ j, a j = -w⁻¹ + b j := by
    intro j
    obtain ⟨hne, -, -⟩ := Sh_res_bd _ (hx j).2 hw
    simp only [ha, hb]
    field_simp
    ring
  have hbb : ∀ j, ‖b j‖ ≤ 25 / 18 * |μ j| := by
    intro j
    obtain ⟨-, ha', -⟩ := Sh_res_bd _ (hx j).2 hw
    rw [hb]; dsimp only
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_iff₀ hwpos]
    calc |t * μ j| * ‖a j‖ ≤ |μ j| * (5 / 4) := mul_le_mul (hx j).1 ha' (norm_nonneg _)
          (abs_nonneg _)
      _ ≤ 25 / 18 * |μ j| * ‖w‖ := by nlinarith [abs_nonneg (μ j)]
  have hsumb2 : c * ∑ j, ‖b j‖ ^ 2 = ((((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖b j‖ ^ 2 : ℝ) : ℂ) := by
    rw [hc]; push_cast; rfl
  have hb2 : ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖b j‖ ^ 2 ≤ (25 / 18) ^ 2 * σ := by
    calc ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖b j‖ ^ 2
        ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, (25 / 18) ^ 2 * μ j ^ 2 := by
          gcongr with j
          calc ‖b j‖ ^ 2 ≤ (25 / 18 * |μ j|) ^ 2 := by gcongr; exact hbb j
            _ = (25 / 18) ^ 2 * μ j ^ 2 := by rw [mul_pow, sq_abs]
      _ = (25 / 18) ^ 2 * σ := by rw [← Finset.mul_sum, hσ]; ring
  -- `w m + 1 = n⁻¹ Σ_j tμ_j a_j`, and `Σ_j tμ_j a_j = Σ_j tμ_j b_j`
  have hwm : w * (c * ∑ j, a j) + 1 = c * ∑ j, ((t * μ j : ℝ) : ℂ) * b j := by
    have hsum : ∑ j, ((t * μ j : ℝ) : ℂ) = 0 := by
      simp only [Complex.ofReal_mul, ← Finset.mul_sum]
      rw [← Complex.ofReal_sum, hμ0]; simp
    have e : ∀ j, w * a j = -1 + ((t * μ j : ℝ) : ℂ) * a j := fun j =>
      Sh_X_eq _ (Sh_res_bd _ (hx j).2 hw).1
    have e2 : ∀ j, ((t * μ j : ℝ) : ℂ) * a j = ((t * μ j : ℝ) : ℂ) * (-w⁻¹) +
        ((t * μ j : ℝ) : ℂ) * b j := fun j => by rw [hab j]; ring
    have h1 : w * (c * ∑ j, a j) = c * ∑ j, w * a j := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1]
    simp only [e, Finset.sum_add_distrib, e2, ← Finset.sum_mul, hsum, zero_mul, zero_add]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
    field_simp
    ring
  have hnb : ‖c * ∑ j, ((t * μ j : ℝ) : ℂ) * b j‖ ≤ 5 / 4 * σ / ‖w‖ := by
    rw [norm_mul, hcn]
    have : ‖∑ j, ((t * μ j : ℝ) : ℂ) * b j‖ ≤ ∑ j, μ j ^ 2 * (5 / 4) / ‖w‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      obtain ⟨-, ha', -⟩ := Sh_res_bd _ (hx j).2 hw
      rw [hb]; dsimp only
      rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hwpos]
      calc |t * μ j| * (|t * μ j| * ‖a j‖) ≤ |μ j| * (|μ j| * (5 / 4)) := by
            refine mul_le_mul (hx j).1 (mul_le_mul (hx j).1 ha' (norm_nonneg _) (abs_nonneg _))
              (by positivity) (abs_nonneg _)
        _ = μ j ^ 2 * (5 / 4) := by rw [← sq_abs (μ j)]; ring
    calc ((Fintype.card ι : ℝ))⁻¹ * ‖∑ j, ((t * μ j : ℝ) : ℂ) * b j‖
        ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 * (5 / 4) / ‖w‖ := by gcongr
      _ = 5 / 4 * σ / ‖w‖ := by rw [← Finset.sum_div, ← Finset.sum_mul, hσ]; ring
  have hσsmall : σ ≤ 1 / 100 := by
    rw [hσ]
    calc ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ _j : ι, (1 / 100 : ℝ) := by
          gcongr with j
          have := hμ j
          nlinarith [abs_nonneg (μ j), sq_abs (μ j)]
      _ = 1 / 100 := by simp
  have h1 : ‖w * (c * ∑ j, a j) + 1‖ ≤ 5 / 4 * σ / ‖w‖ := by rw [hwm]; exact hnb
  have h2 : 7 / 8 ≤ ‖w * (c * ∑ j, a j)‖ := by
    have := norm_sub_norm_le (-1 : ℂ) (-(w * (c * ∑ j, a j) + 1))
    rw [norm_neg, norm_neg, norm_one, show (-1 : ℂ) - -(w * (c * ∑ j, a j) + 1) =
      w * (c * ∑ j, a j) by ring] at this
    have : 5 / 4 * σ / ‖w‖ ≤ 1 / 8 := by
      rw [div_le_iff₀ hwpos]; nlinarith
    linarith
  have hm0 : c * ∑ j, a j ≠ 0 := fun h => by rw [h, mul_zero, norm_zero] at h2; linarith
  refine ⟨h1, h2, ?_, ?_, hm0⟩
  · have e : w + (c * ∑ j, a j)⁻¹ = (w * (c * ∑ j, a j) + 1) / (c * ∑ j, a j) := by
      rw [add_div, mul_div_assoc, div_self hm0, mul_one, one_div]
    rw [e, norm_div]
    have hmpos : 7 / (8 * ‖w‖) ≤ ‖c * ∑ j, a j‖ := by
      rw [norm_mul] at h2
      rw [div_le_iff₀ (by positivity)]; linarith
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hmpos)]
    calc ‖w * (c * ∑ j, a j) + 1‖ ≤ 5 / 4 * σ / ‖w‖ := h1
      _ = 10 / 7 * σ * (7 / (8 * ‖w‖)) := by field_simp; ring
      _ ≤ 10 / 7 * σ * ‖c * ∑ j, a j‖ := by gcongr
  · -- `m² - avg a² = (avg b)² - avg b²`
    have e : (c * ∑ j, a j) ^ 2 - c * ∑ j, a j ^ 2 = (c * ∑ j, b j) ^ 2 - c * ∑ j, b j ^ 2 := by
      have s1 : c * ∑ j, a j = -w⁻¹ + c * ∑ j, b j := by
        simp only [hab, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hc]
        field_simp
      have s2 : c * ∑ j, a j ^ 2 = w⁻¹ ^ 2 - 2 * w⁻¹ * (c * ∑ j, b j) + c * ∑ j, b j ^ 2 := by
        simp only [hab, add_sq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hc, ← Finset.mul_sum, ← Finset.sum_mul]
        field_simp
        ring
      rw [s1, s2]; ring
    rw [e]
    have hb1 : ‖c * ∑ j, b j‖ ^ 2 ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖b j‖ ^ 2 := by
      rw [norm_mul, hcn]
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖b j‖)
      rw [Finset.card_univ] at this
      calc (((Fintype.card ι : ℝ))⁻¹ * ‖∑ j, b j‖) ^ 2
          ≤ (((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖b j‖) ^ 2 := by gcongr; exact norm_sum_le _ _
        _ = ((Fintype.card ι : ℝ))⁻¹ ^ 2 * (∑ j, ‖b j‖) ^ 2 := by ring
        _ ≤ ((Fintype.card ι : ℝ))⁻¹ ^ 2 * ((Fintype.card ι : ℝ) * ∑ j, ‖b j‖ ^ 2) := by gcongr
        _ = _ := by field_simp
    have hb2' : ‖c * ∑ j, b j ^ 2‖ ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖b j‖ ^ 2 := by
      rw [norm_mul, hcn]
      gcongr
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp [norm_pow]
    calc ‖(c * ∑ j, b j) ^ 2 - c * ∑ j, b j ^ 2‖ ≤ ‖c * ∑ j, b j‖ ^ 2 + ‖c * ∑ j, b j ^ 2‖ := by
          refine (norm_sub_le _ _).trans (le_of_eq ?_); rw [norm_pow]
      _ ≤ 2 * ((25 / 18) ^ 2 * σ) := by linarith
      _ ≤ 4 * σ := by nlinarith

end ShiftScalar5

/-! ### The family `Λ_t = tΛ`: `m_t`, its primitive and its derivatives -/

section ShiftFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `m_t(z)` for `Λ_t = t U diag(μ) U^*`. -/
private def Sh_m (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  mSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z

/-- `(tμ_j - z - m_t(z))⁻¹`, the eigenvalues of `M_t(z)`. -/
private def Sh_a (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (t : ℝ) (z : ℂ) (j : ι) : ℂ :=
  (((t * μ j : ℝ) : ℂ) - (z + Sh_m U μ t z))⁻¹

/-- `u_t(z) = ⟨Λ M_t(z)⟩`. -/
private def Sh_u (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (μ j : ℂ) * Sh_a U μ t z j

/-- The primitive `P_t(z) = -n⁻¹ Σ_j log(z + m_t(z) - tμ_j) - m_t(z)²/2` of `m_t` in `z`;
its `t`-derivative is `-⟨Λ M_t(z)⟩`. -/
private def Sh_P (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  -(((Fintype.card ι : ℂ))⁻¹ * ∑ j, Complex.log (z + Sh_m U μ t z - ((t * μ j : ℝ) : ℂ))) -
    Sh_m U μ t z ^ 2 / 2

/-- The hypotheses on `Λ = U diag(μ) U^*` used below: `‖Λ‖ ≤ 1/10`, `|μ_j| ≤ 1/10`, `Σ μ = 0`. -/
private structure Sh_Hyp (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) : Prop where
  norm_le : opNorm (Sh_cd U (fun j => (μ j : ℂ))) ≤ 1 / 10
  eig_le : ∀ j, |μ j| ≤ 1 / 10
  sum_zero : ∑ j, μ j = 0

/-- Basic facts at `|t| ≤ 1`, `Im z > 0`: `Im m > 0`, `m = n⁻¹ Σ a_j`, `|w| > 9/10`, `|m| < 1`,
`Im m = Im w · n⁻¹ Σ |a_j|²`, `n⁻¹ Σ |a_j|² < 1`, and `M_t = U diag(a) U^*`. -/
private lemma Sh_basic {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) {z : ℂ} (hz : 0 < z.im) :
    0 < (Sh_m U μ t z).im ∧
      Sh_m U μ t z = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ∧
      9 / 10 < ‖z + Sh_m U μ t z‖ ∧ ‖Sh_m U μ t z‖ < 1 ∧
      (Sh_m U μ t z).im = (z + Sh_m U μ t z).im *
        (((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Sh_a U μ t z j‖ ^ 2) ∧
      ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Sh_a U μ t z j‖ ^ 2 < 1 ∧
      MSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z = Sh_cd U (Sh_a U μ t z) := by
  obtain ⟨h1, h2, h3⟩ := Sh_bridge U μ t hz
  have hH : ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))).IsHermitian := by
    have hΛ : (Sh_cd U (fun j => (μ j : ℂ))).IsHermitian := by
      have : (Sh_cd U (fun j => (μ j : ℂ))) =
          Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (diagonal (fun j => (μ j : ℂ))) := rfl
      rw [this, Unitary.conjStarAlgAut_apply]
      refine (isHermitian_diagonal_of_self_adjoint _ ?_).isSelfAdjoint.conjugate _ |>.isHermitian
      ext j; simp
    exact Sh_herm_smul hΛ t
  have hn : opNorm ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) ≤ 1 / 10 := by
    rw [Sh_opNorm_smul]
    calc |t| * opNorm (Sh_cd U (fun j => (μ j : ℂ))) ≤ 1 * (1 / 10) :=
          mul_le_mul ht H.norm_le (norm_nonneg _) zero_le_one
      _ = 1 / 10 := by ring
  obtain ⟨a1, a2, -⟩ := mSol_apriori _ hH hn z hz
  have hn0 : 0 ≤ opNorm ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) := norm_nonneg _
  have hm : Sh_m U μ t z = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j := h2
  have hw : 0 < (z + Sh_m U μ t z).im := by simp only [Complex.add_im]; unfold Sh_m; linarith
  have him : (Sh_m U μ t z).im = (z + Sh_m U μ t z).im *
      (((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Sh_a U μ t z j‖ ^ 2) := by
    conv_lhs => rw [hm]
    have e : (((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j) =
        ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) * ∑ j, Sh_a U μ t z j := by push_cast; rfl
    rw [e, Complex.im_ofReal_mul, Complex.im_sum]
    simp only [Sh_a, Sh_im_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (z + Sh_m U μ t z).im = (z + Sh_m U μ t z).im from rfl]
    ring
  refine ⟨h1, hm, by unfold Sh_m; linarith, a2, him, ?_, h3⟩
  have hm1 : 0 < (Sh_m U μ t z).im := h1
  have : (Sh_m U μ t z).im < (z + Sh_m U μ t z).im := by
    simp only [Complex.add_im]; linarith
  by_contra hcon
  push_neg at hcon
  nlinarith

end ShiftFamily

section ShiftFamily2

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Sh_cd_herm (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) :
    (Sh_cd U (fun j => (μ j : ℂ))).IsHermitian := by
  have : (Sh_cd U (fun j => (μ j : ℂ))) =
      Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (diagonal (fun j => (μ j : ℂ))) := rfl
  rw [this, Unitary.conjStarAlgAut_apply]
  refine (isHermitian_diagonal_of_self_adjoint _ ?_).isSelfAdjoint.conjugate _ |>.isHermitian
  ext j; simp

/-- Joint continuity of `(t, z) ↦ m_t(z)` on `|t| ≤ 1`, `Im z > 0` (Definition 2.10
[def_moving_Lambda]). -/
private lemma Sh_joint {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) :
    ContinuousOn (fun q : ℝ × ℂ => Sh_m U μ q.1 q.2) {q | |q.1| ≤ 1 ∧ 0 < q.2.im} := by
  set Λ := Sh_cd U (fun j => (μ j : ℂ))
  have hΛ : Λ.IsHermitian := Sh_cd_herm U μ
  set cl : ℝ → ℝ := fun t => max (-1) (min 1 t) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hcl1 : ∀ t, |cl t| ≤ 1 := fun t => by
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  have hmc := moving_continuous (fun t => ((cl t : ℝ) : ℂ) • Λ)
    ((Complex.continuous_ofReal.comp hclc).smul continuous_const)
    (fun t => Sh_herm_smul hΛ _)
    (fun t => by
      rw [Sh_opNorm_smul]
      calc |cl t| * opNorm Λ ≤ 1 * (1 / 10) := mul_le_mul (hcl1 t) H.norm_le (norm_nonneg _)
            zero_le_one
        _ = 1 / 10 := by ring)
  refine (hmc.2.2.2.mono (fun q (hq : q ∈ {q : ℝ × ℂ | |q.1| ≤ 1 ∧ 0 < q.2.im}) => hq.2)).congr
    fun q hq => ?_
  have : cl q.1 = q.1 := by
    obtain ⟨h1, -⟩ := hq
    rw [abs_le] at h1
    simp only [hcl]
    rw [min_eq_right h1.2, max_eq_right h1.1]
  simp only [Sh_m, this, Λ]

private lemma Sh_joint_at {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    {z : ℂ} (ht : |t| < 1) (hz : 0 < z.im) :
    ContinuousAt (fun q : ℝ × ℂ => Sh_m U μ q.1 q.2) (t, z) := by
  refine (Sh_joint H).continuousAt ?_
  have ho : IsOpen ({q : ℝ × ℂ | |q.1| < 1} ∩ {q : ℝ × ℂ | 0 < q.2.im}) :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_snd))
  exact Filter.mem_of_superset (ho.mem_nhds ⟨ht, hz⟩) fun q hq => ⟨hq.1.le, hq.2⟩

/-- (A.43) [derivative_m_t_z_with_t_and_z], `z`-derivative, spectral form:
`∂_z m_t = A/(1 - A)` with `A = n⁻¹ Σ_j a_j²`. -/
private lemma Sh_dm_z {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (Sh_m U μ t)
      ((((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2)) z := by
  have hH := Sh_herm_smul (Sh_cd_herm U μ) t
  have h := (derivative_m_t_z _ hH z hz 0).1
  have hM := (Sh_basic H ht hz).2.2.2.2.2.2
  rw [hM, Sh_cd_pow, Sh_ntr_cd] at h
  exact h

/-- `t ↦ m_t(z)` is differentiable (A.43) [derivative_m_t_z_with_t_and_z]. -/
private lemma Sh_dm_t_ex (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (t : ℝ) {z : ℂ}
    (hz : 0 < z.im) : ∃ d, HasDerivAt (fun s => Sh_m U μ s z) d t :=
  ⟨_, (derivative_m_t_z _ (Sh_cd_herm U μ) z hz t).2⟩

private lemma Sh_slit {w : ℂ} (x : ℝ) (hw : 0 < w.im) : w - (x : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right; simp; linarith

/-- `m_t` along a path: the primitive `P_t` satisfies `d/ds P_t(p(s)) = m_t(p(s)) p'(s)`. -/
private lemma Sh_P_path {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) {p : ℝ → ℂ} {p' : ℂ} {s₀ : ℝ} (hp : HasDerivAt p p' s₀)
    (hz : 0 < (p s₀).im) :
    HasDerivAt (fun s => Sh_P U μ t (p s)) (Sh_m U μ t (p s₀) * p') s₀ := by
  obtain ⟨b1, b2, -⟩ := Sh_basic H ht hz
  have hφ := (Sh_dm_z H ht hz).comp s₀ hp
  set φ' := ((((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t (p s₀) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t (p s₀) j ^ 2)) * p'
  have hw : 0 < (p s₀ + Sh_m U μ t (p s₀)).im := by simp only [Complex.add_im]; linarith
  have hlog : ∀ j ∈ Finset.univ, HasDerivAt
      (fun s => Complex.log (p s + Sh_m U μ t (p s) - ((t * μ j : ℝ) : ℂ)))
      ((p' + φ') / (p s₀ + Sh_m U μ t (p s₀) - ((t * μ j : ℝ) : ℂ))) s₀ := fun j _ =>
    ((hp.add hφ).sub_const _).clog_real (Sh_slit _ hw)
  have hsum := (HasDerivAt.fun_sum hlog).const_mul (((Fintype.card ι : ℂ))⁻¹)
  have hfin := hsum.neg.sub ((hφ.pow 2).div_const 2)
  have e : ∀ j, (p' + φ') / (p s₀ + Sh_m U μ t (p s₀) - ((t * μ j : ℝ) : ℂ)) =
      -(p' + φ') * Sh_a U μ t (p s₀) j := fun j => by
    have hne := Sh_ne_of_im (t * μ j) hw
    simp only [Sh_a]
    rw [show p s₀ + Sh_m U μ t (p s₀) - ((t * μ j : ℝ) : ℂ) =
      -(((t * μ j : ℝ) : ℂ) - (p s₀ + Sh_m U μ t (p s₀))) by ring]
    field_simp
  convert hfin using 1
  · funext s
    simp only [Sh_P, Pi.sub_apply, Pi.neg_apply, Function.comp_apply, Pi.pow_apply]
  · simp only [e, ← Finset.mul_sum, Function.comp_apply]
    rw [b2]
    push_cast
    ring

/-- `d/dt P_t(z) = -⟨Λ M_t(z)⟩`. -/
private lemma Sh_P_t {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun s => Sh_P U μ s z) (-Sh_u U μ t z) t := by
  obtain ⟨b1, b2, -⟩ := Sh_basic H ht hz
  obtain ⟨d, hd⟩ := Sh_dm_t_ex U μ t hz
  have hw : 0 < (z + Sh_m U μ t z).im := by simp only [Complex.add_im]; linarith
  have hlog : ∀ j ∈ Finset.univ, HasDerivAt
      (fun s => Complex.log (z + Sh_m U μ s z - ((s * μ j : ℝ) : ℂ)))
      ((d - (μ j : ℂ)) / (z + Sh_m U μ t z - ((t * μ j : ℝ) : ℂ))) t := fun j _ => by
    have h1 : HasDerivAt (fun s : ℝ => ((s * μ j : ℝ) : ℂ)) ((1 * μ j : ℝ) : ℂ) t :=
      ((hasDerivAt_id t).mul_const (μ j)).ofReal_comp
    have h2 := (hd.const_add z).sub h1
    rw [one_mul] at h2
    exact h2.clog_real (Sh_slit _ hw)
  have hsum := (HasDerivAt.fun_sum hlog).const_mul (((Fintype.card ι : ℂ))⁻¹)
  have hfin := hsum.neg.sub ((hd.pow 2).div_const 2)
  have e : ∀ j, (d - (μ j : ℂ)) / (z + Sh_m U μ t z - ((t * μ j : ℝ) : ℂ)) =
      -d * Sh_a U μ t z j + (μ j : ℂ) * Sh_a U μ t z j := fun j => by
    have hne := Sh_ne_of_im (t * μ j) hw
    simp only [Sh_a]
    rw [show z + Sh_m U μ t z - ((t * μ j : ℝ) : ℂ) =
      -(((t * μ j : ℝ) : ℂ) - (z + Sh_m U μ t z)) by ring]
    field_simp
    ring
  convert hfin using 1
  · funext s
    simp only [Sh_P, Pi.sub_apply, Pi.neg_apply, Function.comp_apply, Pi.pow_apply]
  · simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Sh_u]
    rw [b2]
    push_cast
    ring

end ShiftFamily2

section ShiftFamily3

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Continuity of `s ↦ m_s(p(s))` and of `a_j` along a continuous path. -/
private lemma Sh_path_cont {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ)
    {p : ℝ → ℂ} {s₀ : ℝ} (hs : |s₀| < 1) (hp : ContinuousAt p s₀) (hz : 0 < (p s₀).im) :
    Tendsto (fun s => Sh_m U μ s (p s)) (𝓝 s₀) (𝓝 (Sh_m U μ s₀ (p s₀))) ∧
      ∀ j, Tendsto (fun s => Sh_a U μ s (p s) j) (𝓝 s₀) (𝓝 (Sh_a U μ s₀ (p s₀) j)) := by
  have hq : ContinuousAt (fun s : ℝ => ((s, p s) : ℝ × ℂ)) s₀ :=
    continuousAt_id.prodMk hp
  have hm : Tendsto (fun s => Sh_m U μ s (p s)) (𝓝 s₀) (𝓝 (Sh_m U μ s₀ (p s₀))) := by
    have h := (Sh_joint_at H hs hz).tendsto.comp hq.tendsto
    exact h
  refine ⟨hm, fun j => ?_⟩
  obtain ⟨b1, -⟩ := Sh_basic H hs.le hz
  have hw : 0 < (p s₀ + Sh_m U μ s₀ (p s₀)).im := by simp only [Complex.add_im]; linarith
  have h1 : Tendsto (fun s : ℝ => ((s * μ j : ℝ) : ℂ)) (𝓝 s₀) (𝓝 ((s₀ * μ j : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).tendsto s₀
  have h2 := (h1.sub (hp.tendsto.add hm)).inv₀ (Sh_ne_of_im _ hw)
  unfold Sh_a
  exact h2

/-- `d/ds m_s(p(s)) = (p' A - B)/(1 - A)` with `A = ⟨M²⟩`, `B = ⟨Λ M²⟩`: the derivative of
`m_t(z_t)` used in the proof of (A.34) [modification_shift_eigenvector]. -/
private lemma Sh_dm_path {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ)
    {p : ℝ → ℂ} {p' : ℂ} {s₀ : ℝ} (hs : |s₀| < 1) (hp : HasDerivAt p p' s₀)
    (hz : 0 < (p s₀).im) :
    HasDerivAt (fun s => Sh_m U μ s (p s))
      ((p' * (((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ s₀ (p s₀) j ^ 2) -
          ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (μ j : ℂ) * Sh_a U μ s₀ (p s₀) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ s₀ (p s₀) j ^ 2)) s₀ := by
  obtain ⟨hm, ha⟩ := Sh_path_cont H hs hp.continuousAt hz
  obtain ⟨b1, b2, -, -, -, b6, -⟩ := Sh_basic H hs.le hz
  set c : ℂ := ((Fintype.card ι : ℂ))⁻¹
  set a : ℝ → ι → ℂ := fun s j => Sh_a U μ s (p s) j with hadef
  set A := c * ∑ j, a s₀ j ^ 2
  set B := c * ∑ j, (μ j : ℂ) * a s₀ j ^ 2
  set G : ℝ → ℂ := fun s => c * ∑ j, a s j * a s₀ j
  set Bm : ℝ → ℂ := fun s => c * ∑ j, (μ j : ℂ) * (a s j * a s₀ j)
  have hG : Tendsto G (𝓝 s₀) (𝓝 A) := by
    have : Tendsto G (𝓝 s₀) (𝓝 (c * ∑ j, a s₀ j * a s₀ j)) :=
      Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => (ha j).mul tendsto_const_nhds)
    have e : c * ∑ j, a s₀ j * a s₀ j = A := by simp only [A, sq]
    rwa [e] at this
  have hB : Tendsto Bm (𝓝 s₀) (𝓝 B) := by
    have : Tendsto Bm (𝓝 s₀) (𝓝 (c * ∑ j, (μ j : ℂ) * (a s₀ j * a s₀ j))) :=
      Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ =>
        Tendsto.const_mul _ ((ha j).mul tendsto_const_nhds))
    have e : c * ∑ j, (μ j : ℂ) * (a s₀ j * a s₀ j) = B := by simp only [B, sq]
    rwa [e] at this
  have hA1 : 1 - A ≠ 0 := by
    intro h
    have hA : A = 1 := by linear_combination -h
    have : ‖A‖ ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Sh_a U μ s₀ (p s₀) j‖ ^ 2 := by
      simp only [A, c, norm_mul, norm_inv, Complex.norm_natCast]
      gcongr
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp [a, norm_pow]
    rw [hA, norm_one] at this
    linarith
  -- eventually `|s| ≤ 1` and `Im p(s) > 0`
  have hev : ∀ᶠ s in 𝓝 s₀, |s| < 1 ∧ 0 < (p s).im :=
    (continuous_abs.continuousAt.eventually_lt continuousAt_const hs).and
      (continuousAt_const.eventually_lt
        (Complex.continuous_im.continuousAt.comp hp.continuousAt) hz)
  have hkey : ∀ᶠ s in 𝓝 s₀, (Sh_m U μ s (p s) - Sh_m U μ s₀ (p s₀)) * (1 - G s) =
      (s₀ - s) * Bm s + (p s - p s₀) * G s := by
    filter_upwards [hev] with s hs'
    obtain ⟨c1, c2, -⟩ := Sh_basic H hs'.1.le hs'.2
    have hw : 0 < (p s + Sh_m U μ s (p s)).im := by simp only [Complex.add_im]; linarith
    have hw0 : 0 < (p s₀ + Sh_m U μ s₀ (p s₀)).im := by simp only [Complex.add_im]; linarith
    have e : ∀ j, a s j - a s₀ j = (((s₀ - s) * μ j : ℝ) : ℂ) * (a s j * a s₀ j) +
        ((p s - p s₀) + (Sh_m U μ s (p s) - Sh_m U μ s₀ (p s₀))) * (a s j * a s₀ j) := by
      intro j
      have n1 := Sh_ne_of_im (s * μ j) hw
      have n2 := Sh_ne_of_im (s₀ * μ j) hw0
      simp only [a, Sh_a]
      rw [inv_sub_inv n1 n2, div_eq_mul_inv, mul_inv, ← add_mul]
      congr 1
      push_cast
      ring
    have hsum : Sh_m U μ s (p s) - Sh_m U μ s₀ (p s₀) = c * ∑ j, (a s j - a s₀ j) := by
      rw [c2, b2, Finset.sum_sub_distrib, mul_sub]
    simp only [e, Finset.sum_add_distrib] at hsum
    simp only [G, Bm]
    have e2 : ∀ j, (((s₀ - s) * μ j : ℝ) : ℂ) * (a s j * a s₀ j) =
        ((s₀ - s : ℝ) : ℂ) * ((μ j : ℂ) * (a s j * a s₀ j)) := fun j => by push_cast; ring
    simp only [e2, ← Finset.mul_sum] at hsum
    push_cast at hsum
    linear_combination hsum
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun s => (-Bm s + slope p s₀ s * G s) / (1 - G s)) (𝓝[≠] s₀)
      (𝓝 ((p' * A - B) / (1 - A))) := by
    have h1 := (hasDerivAt_iff_tendsto_slope.1 hp)
    have := ((hB.mono_left nhdsWithin_le_nhds).neg.add (h1.mul (hG.mono_left nhdsWithin_le_nhds))).div
      (tendsto_const_nhds.sub (hG.mono_left nhdsWithin_le_nhds)) hA1
    convert this using 2
    ring
  refine hlim.congr' ?_
  have hG1 : ∀ᶠ s in 𝓝 s₀, 1 - G s ≠ 0 :=
    (tendsto_const_nhds.sub hG).eventually_ne hA1
  filter_upwards [self_mem_nhdsWithin, hkey.filter_mono nhdsWithin_le_nhds,
    hG1.filter_mono nhdsWithin_le_nhds] with s hs1 hk hg
  have hs0 : ((s : ℂ) - (s₀ : ℂ)) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hs1
  rw [slope_def_module, slope_def_module, Complex.real_smul, Complex.real_smul]
  have : (Sh_m U μ s (p s) - Sh_m U μ s₀ (p s₀)) = ((s₀ - s) * Bm s + (p s - p s₀) * G s) /
      (1 - G s) := by rw [← hk]; field_simp
  rw [this]
  push_cast
  field_simp
  ring

end ShiftFamily3

/-! ### Real-variable tools: roots of decreasing functions and an implicit derivative -/

section ShiftReal

/-- `s = sup {x | c ≤ f x}` is a root of a continuous `f` with `c ≤ f a` and `f < c` on `[b, ∞)`. -/
private lemma Sh_sSup_root {f : ℝ → ℝ} (hf : Continuous f) {c a b : ℝ} (ha : c ≤ f a)
    (hb : ∀ x, b ≤ x → f x < c) :
    f (sSup {x | c ≤ f x}) = c ∧ a ≤ sSup {x | c ≤ f x} ∧ sSup {x | c ≤ f x} < b := by
  set S := {x | c ≤ f x}
  have hne : S.Nonempty := ⟨a, ha⟩
  have hbdd : BddAbove S := ⟨b, fun x hx => by
    by_contra h; push_neg at h; exact absurd hx (not_le.2 (hb x h.le))⟩
  have hcl : IsClosed S := isClosed_le continuous_const hf
  have hmem : sSup S ∈ S := hcl.csSup_mem hne hbdd
  have hlt : sSup S < b := by
    by_contra h; push_neg at h; exact absurd hmem (not_le.2 (hb _ h))
  refine ⟨le_antisymm ?_ hmem, le_csSup hbdd ha, hlt⟩
  by_contra h
  push_neg at h
  have hev : ∀ᶠ x in 𝓝 (sSup S), c < f x := continuousAt_const.eventually_lt hf.continuousAt h
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have : sSup S + δ / 2 ∈ S := (hball (by
    rw [Real.dist_eq, show sSup S + δ / 2 - sSup S = δ / 2 by ring, abs_of_pos (by linarith)]
    linarith)).le
  have := le_csSup hbdd this
  linarith

/-- Roots of two close antitone functions are close. -/
private lemma Sh_root_close {f g : ℝ → ℝ} (hg : Antitone g) {c s s' δ ε : ℝ} (hs' : g s' = c)
    (h1 : c + ε < f (s - δ)) (h2 : f (s + δ) < c - ε) (h3 : |f (s - δ) - g (s - δ)| ≤ ε)
    (h4 : |f (s + δ) - g (s + δ)| ≤ ε) : |s' - s| < δ := by
  rw [abs_lt]
  have a1 := (abs_le.1 h3).2
  have a2 := (abs_le.1 h4).1
  constructor
  · by_contra h; push_neg at h
    have := hg (show s' ≤ s - δ by linarith)
    linarith
  · by_contra h; push_neg at h
    have := hg (show s + δ ≤ s' by linarith)
    linarith

/-- The mean value theorem in either orientation. -/
private lemma Sh_mvt {f f' : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x) :
    ∃ ξ ∈ Set.uIcc a b, f b - f a = f' ξ * (b - a) := by
  rcases lt_trichotomy a b with h | h | h
  · have hc : ContinuousOn f (Set.Icc a b) := fun x hx =>
      (hf x (by rw [Set.uIcc_of_le h.le]; exact hx)).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope f f' h hc fun x hx =>
      hf x (by rw [Set.uIcc_of_le h.le]; exact Set.Ioo_subset_Icc_self hx)
    refine ⟨ξ, by rw [Set.uIcc_of_le h.le]; exact Set.Ioo_subset_Icc_self hξ, ?_⟩
    rw [e]; field_simp [sub_ne_zero.2 h.ne']
  · exact ⟨a, Set.left_mem_uIcc, by rw [h]; ring⟩
  · have hc : ContinuousOn f (Set.Icc b a) := fun x hx =>
      (hf x (by rw [Set.uIcc_of_ge h.le]; exact hx)).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope f f' h hc fun x hx =>
      hf x (by rw [Set.uIcc_of_ge h.le]; exact Set.Ioo_subset_Icc_self hx)
    refine ⟨ξ, by rw [Set.uIcc_of_ge h.le]; exact Set.Ioo_subset_Icc_self hξ, ?_⟩
    rw [e]; field_simp [sub_ne_zero.2 h.ne']; ring

/-- The implicit function `F(t, g(t)) = c` has the derivative `-∂_t F / ∂_x F`, given continuity
of `g` and of the partial derivatives. -/
private lemma Sh_ift {F Ft Fx : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {c t₀ a b : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    (h1 : ∀ t ∈ Set.Ioo a b, F t (g t) = c)
    (h2 : ∀ t ∈ Set.Ioo a b, ∀ x, HasDerivAt (fun s => F s x) (Ft t x) t)
    (h3 : ∀ x, HasDerivAt (F t₀) (Fx t₀ x) x)
    (h4 : ContinuousAt (fun q : ℝ × ℝ => Ft q.1 q.2) (t₀, g t₀))
    (h5 : ContinuousAt (Fx t₀) (g t₀)) (h6 : Fx t₀ (g t₀) ≠ 0) (h7 : ContinuousAt g t₀) :
    HasDerivAt g (-Ft t₀ (g t₀) / Fx t₀ (g t₀)) t₀ := by
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- continuity of `(s, x, y) ↦ -Ft s x / Fx t₀ y`
  have hΦ : ContinuousAt (fun q : ℝ × ℝ × ℝ => -Ft q.1 q.2.1 / Fx t₀ q.2.2) (t₀, g t₀, g t₀) := by
    have f1 : ContinuousAt (fun q : ℝ × ℝ × ℝ => ((q.1, q.2.1) : ℝ × ℝ)) (t₀, g t₀, g t₀) := by
      fun_prop
    have f2 : ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.2) (t₀, g t₀, g t₀) := by fun_prop
    have e1 : ContinuousAt (fun q : ℝ × ℝ × ℝ => Ft q.1 q.2.1) (t₀, g t₀, g t₀) :=
      ContinuousAt.comp (x := (t₀, g t₀, g t₀)) (g := fun q : ℝ × ℝ => Ft q.1 q.2) h4 f1
    have e2 : ContinuousAt (fun q : ℝ × ℝ × ℝ => Fx t₀ q.2.2) (t₀, g t₀, g t₀) :=
      ContinuousAt.comp (x := (t₀, g t₀, g t₀)) (g := Fx t₀) h5 f2
    exact e1.neg.div e2 h6
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.continuousAt_iff.1 hΦ ε hε
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.eventually_nhds_iff.1 (h5.eventually_ne h6)
  set δ₀ := min δ₁ δ₂
  have hδ₀ : 0 < δ₀ := lt_min hδ₁ hδ₂
  obtain ⟨δ₃, hδ₃, hb₃⟩ := Metric.continuousAt_iff.1 h7 δ₀ hδ₀
  obtain ⟨δ₄, hδ₄, hb₄⟩ := Metric.isOpen_iff.1 isOpen_Ioo t₀ ht₀
  refine ⟨min δ₀ (min δ₃ δ₄), lt_min hδ₀ (lt_min hδ₃ hδ₄), fun t ht hdist => ?_⟩
  have hd₀ : dist t t₀ < δ₀ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd₃ : dist t t₀ < δ₃ := lt_of_lt_of_le hdist ((min_le_right _ _).trans (min_le_left _ _))
  have hd₄ : dist t t₀ < δ₄ := lt_of_lt_of_le hdist ((min_le_right _ _).trans (min_le_right _ _))
  have htI : t ∈ Set.Ioo a b := hb₄ (by rw [Metric.mem_ball]; exact hd₄)
  have hg₃ : dist (g t) (g t₀) < δ₀ := hb₃ hd₃
  -- the segment between `t₀` and `t` lies in `(a, b)`
  have hseg : ∀ s ∈ Set.uIcc t₀ t, s ∈ Set.Ioo a b := fun s hs =>
    (Set.ordConnected_Ioo.uIcc_subset ht₀ htI) hs
  obtain ⟨ξ, hξ, eξ⟩ := Sh_mvt (f := fun s => F s (g t)) (f' := fun s => Ft s (g t))
    (a := t₀) (b := t) fun s hs => h2 s (hseg s hs) (g t)
  obtain ⟨ζ, hζ, eζ⟩ := Sh_mvt (f := F t₀) (f' := Fx t₀) (a := g t₀) (b := g t)
    fun x _ => h3 x
  have hsum : Ft ξ (g t) * (t - t₀) + Fx t₀ ζ * (g t - g t₀) = 0 := by
    have := h1 t htI; have := h1 t₀ ht₀
    linarith
  have hζd : dist ζ (g t₀) ≤ dist (g t) (g t₀) := by
    rw [Real.dist_eq, Real.dist_eq]
    rcases Set.mem_uIcc.1 hζ with h | h
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  have hξd : dist ξ t₀ ≤ dist t t₀ := by
    rw [Real.dist_eq, Real.dist_eq]
    rcases Set.mem_uIcc.1 hξ with h | h
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  have hFx : Fx t₀ ζ ≠ 0 := hb₂ (lt_of_le_of_lt hζd (lt_of_lt_of_le hg₃ (min_le_right _ _)))
  have hne : t - t₀ ≠ 0 := sub_ne_zero.2 ht
  have hslope : slope g t₀ t = -Ft ξ (g t) / Fx t₀ ζ := by
    rw [slope_def_field, eq_div_iff hFx, div_mul_eq_mul_div, div_eq_iff hne]
    linarith
  rw [hslope]
  have hdq : dist ((ξ, g t, ζ) : ℝ × ℝ × ℝ) (t₀, g t₀, g t₀) < δ₁ := by
    rw [Prod.dist_eq, Prod.dist_eq]
    exact max_lt (lt_of_le_of_lt hξd (lt_of_lt_of_le hd₀ (min_le_left _ _)))
      (max_lt (lt_of_lt_of_le hg₃ (min_le_left _ _))
      (lt_of_le_of_lt hζd (lt_of_lt_of_le hg₃ (min_le_left _ _))))
  exact hb₁ hdq

end ShiftReal

/-! ### The counting function `N_t(E) = ∫_E^∞ ρ_t` and its regularization at height `h` -/

section ShiftCount

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Sh_hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).im) f'.im x := by
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf

/-- `F_h(t, E) = π⁻¹ (Im P_t(3 + ih) - Im P_t(E + ih)) = π⁻¹ ∫_E^3 Im m_t(x + ih) dx`, the counting
function of `ρ_t` regularized at height `h`. -/
private def Sh_F (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (h t x : ℝ) : ℝ :=
  ((Sh_P U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im -
    (Sh_P U μ t ((x : ℂ) + (h : ℂ) * Complex.I)).im) / Real.pi

private lemma Sh_hpath (h x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) + (h : ℂ) * Complex.I) 1 x := by
  simpa using (hasDerivAt_id x).ofReal_comp.add_const ((h : ℂ) * Complex.I)

private lemma Sh_vpath (x s : ℝ) :
    HasDerivAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) Complex.I s := by
  simpa using ((hasDerivAt_id s).ofReal_comp.mul_const Complex.I).const_add (x : ℂ)

private lemma Sh_im_hpath {h : ℝ} (hh : 0 < h) (x : ℝ) : 0 < ((x : ℂ) + (h : ℂ) * Complex.I).im := by
  simpa using hh

/-- `∂_E F_h(t, E) = -π⁻¹ Im m_t(E + ih)`. -/
private lemma Sh_F_dx {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {h t : ℝ}
    (hh : 0 < h) (ht : |t| ≤ 1) (x : ℝ) :
    HasDerivAt (Sh_F U μ h t)
      (-(Sh_m U μ t ((x : ℂ) + (h : ℂ) * Complex.I)).im / Real.pi) x := by
  have h1 := Sh_hasDerivAt_im (Sh_P_path H ht (Sh_hpath h x) (Sh_im_hpath hh x))
  rw [mul_one] at h1
  have h2 := (h1.const_sub ((Sh_P U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im)).div_const Real.pi
  exact h2.congr_deriv (by ring)

/-- `∂_t F_h(t, E) = π⁻¹ (Im u_t(E + ih) - Im u_t(3 + ih))`, `u_t = ⟨Λ M_t⟩`. -/
private lemma Sh_F_dt {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {h t : ℝ}
    (hh : 0 < h) (ht : |t| ≤ 1) (x : ℝ) :
    HasDerivAt (fun s => Sh_F U μ h s x)
      (((Sh_u U μ t ((x : ℂ) + (h : ℂ) * Complex.I)).im -
        (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) / Real.pi) t := by
  have h3 := Sh_hasDerivAt_im (Sh_P_t H ht (Sh_im_hpath hh 3))
  have hx := Sh_hasDerivAt_im (Sh_P_t H ht (Sh_im_hpath hh x))
  have := (h3.sub hx).div_const Real.pi
  exact this.congr_deriv (by simp only [Complex.neg_im]; ring)

/-- Continuity of `x ↦ m_t(x + ih)`. -/
private lemma Sh_m_hcont {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {h t : ℝ}
    (hh : 0 < h) (ht : |t| ≤ 1) :
    Continuous fun x : ℝ => Sh_m U μ t ((x : ℂ) + (h : ℂ) * Complex.I) :=
  continuous_iff_continuousAt.2 fun x =>
    ((Sh_dm_z H ht (Sh_im_hpath hh x)).comp x (Sh_hpath h x)).continuousAt

/-- `F_h(t, E) = π⁻¹ ∫_E^3 Im m_t(x + ih) dx`. -/
private lemma Sh_F_int {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {h t : ℝ}
    (hh : 0 < h) (ht : |t| ≤ 1) (x : ℝ) :
    Sh_F U μ h t x =
      (∫ y in x..3, (Sh_m U μ t ((y : ℂ) + (h : ℂ) * Complex.I)).im) / Real.pi := by
  have hd : ∀ y ∈ Set.uIcc x 3, HasDerivAt
      (fun y : ℝ => (Sh_P U μ t ((y : ℂ) + (h : ℂ) * Complex.I)).im)
      ((Sh_m U μ t ((y : ℂ) + (h : ℂ) * Complex.I)).im) y := fun y _ => by
    have := Sh_hasDerivAt_im (Sh_P_path H ht (Sh_hpath h y) (Sh_im_hpath hh y))
    rwa [mul_one] at this
  have hint : IntervalIntegrable (fun y : ℝ => (Sh_m U μ t ((y : ℂ) + (h : ℂ) * Complex.I)).im)
      MeasureTheory.volume x 3 :=
    (Complex.continuous_im.comp (Sh_m_hcont H hh ht)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, Sh_F]

/-- `|F_h - F_{h'}| ≤ 2|h - h'|/π`: `∂_h Im P_t(E + ih) = Re m_t` and `|m_t| < 1`. -/
private lemma Sh_F_vert {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {h h' t : ℝ}
    (hh : 0 < h) (hh' : 0 < h') (ht : |t| ≤ 1) (x : ℝ) :
    |Sh_F U μ h t x - Sh_F U μ h' t x| ≤ 2 * |h - h'| / Real.pi := by
  have key : ∀ y : ℝ, |(Sh_P U μ t ((y : ℂ) + (h : ℂ) * Complex.I)).im -
      (Sh_P U μ t ((y : ℂ) + (h' : ℂ) * Complex.I)).im| ≤ |h - h'| := by
    intro y
    have hseg : ∀ s ∈ Set.uIcc h' h, 0 < s := fun s hs => by
      rcases Set.mem_uIcc.1 hs with hs | hs <;> linarith [hs.1]
    obtain ⟨ξ, hξ, e⟩ := Sh_mvt (f := fun s : ℝ => (Sh_P U μ t ((y : ℂ) + (s : ℂ) * Complex.I)).im)
      (f' := fun s => (Sh_m U μ t ((y : ℂ) + (s : ℂ) * Complex.I) * Complex.I).im)
      (a := h') (b := h) fun s hs =>
        Sh_hasDerivAt_im (Sh_P_path H ht (Sh_vpath y s) (by simpa using hseg s hs))
    rw [e, abs_mul]
    have hb : |(Sh_m U μ t ((y : ℂ) + (ξ : ℂ) * Complex.I) * Complex.I).im| ≤ 1 := by
      rw [Complex.mul_I_im]
      exact (Complex.abs_re_le_norm _).trans
        (Sh_basic H ht (by simpa using hseg ξ hξ)).2.2.2.1.le
    calc |(Sh_m U μ t ((y : ℂ) + (ξ : ℂ) * Complex.I) * Complex.I).im| * |h - h'|
        ≤ 1 * |h - h'| := by gcongr
      _ = |h - h'| := one_mul _
  have k3 := key 3
  have kx := key x
  push_cast at k3
  unfold Sh_F
  rw [← sub_div, abs_div, abs_of_pos Real.pi_pos]
  gcongr
  calc |(Sh_P U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im - (Sh_P U μ t ((x : ℂ) + (h : ℂ) * Complex.I)).im -
        ((Sh_P U μ t ((3 : ℝ) + (h' : ℂ) * Complex.I)).im -
          (Sh_P U μ t ((x : ℂ) + (h' : ℂ) * Complex.I)).im)|
      ≤ |(Sh_P U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im -
          (Sh_P U μ t ((3 : ℝ) + (h' : ℂ) * Complex.I)).im| +
        |(Sh_P U μ t ((x : ℂ) + (h : ℂ) * Complex.I)).im -
          (Sh_P U μ t ((x : ℂ) + (h' : ℂ) * Complex.I)).im| := by
        rw [show ∀ a b c d : ℝ, a - b - (c - d) = (a - c) - (b - d) by intros; ring]
        exact abs_sub _ _
    _ ≤ 2 * |h - h'| := by push_cast; linarith

end ShiftCount

section ShiftCount2

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Sh_tΛ {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) :
    ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))).IsHermitian ∧
      opNorm ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) ≤ 1 / 10 := by
  refine ⟨Sh_herm_smul (Sh_cd_herm U μ) t, ?_⟩
  rw [Sh_opNorm_smul]
  calc |t| * opNorm (Sh_cd U (fun j => (μ j : ℂ))) ≤ 1 * (1 / 10) :=
        mul_le_mul ht H.norm_le (norm_nonneg _) zero_le_one
    _ = 1 / 10 := by ring

/-- The boundary value: `Im m_t(x + ih) → Im m_t(x)` as `h ↓ 0`, and `ρ_t(x) = π⁻¹ Im m_t(x)`
((2.19) [eq:density_rhoN]). -/
private lemma Sh_rho_eq {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) (x : ℝ) :
    Tendsto (fun h : ℝ => (Sh_m U μ t ((x : ℂ) + (h : ℂ) * Complex.I)).im) (𝓝[>] 0)
        (𝓝 ((mExt ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) x).im)) ∧
      rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) x =
        (mExt ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) x).im / Real.pi := by
  obtain ⟨hH, hn⟩ := Sh_tΛ H ht
  set Λ := (t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))
  have hc := (mExt_boundary Λ hH hn).1 (x : ℂ) (by simp)
  have hφ : Tendsto (fun h : ℝ => (x : ℂ) + (h : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.im}] (x : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Continuous fun h : ℝ => (x : ℂ) + (h : ℂ) * Complex.I := by fun_prop
      have h0 := this.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      show 0 ≤ ((x : ℂ) + (h : ℂ) * Complex.I).im
      simpa using (le_of_lt hh)
  have h1 := hc.tendsto.comp hφ
  have h2 : Tendsto (fun h : ℝ => Sh_m U μ t ((x : ℂ) + (h : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝 (mExt Λ x)) := by
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have : 0 < ((x : ℂ) + (h : ℂ) * Complex.I).im := by simpa using hh
    show mExt Λ ((x : ℂ) + (h : ℂ) * Complex.I) = _
    rw [mExt, if_pos this]
    rfl
  have h3 := (Complex.continuous_im.tendsto _).comp h2
  have h3' : Tendsto (fun η : ℝ => (mSol Λ ((x : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] 0)
      (𝓝 (mExt Λ x).im) := h3
  refine ⟨h3, ?_⟩
  unfold rho
  rw [h3'.limUnder_eq]

/-- `F_h(t, E) → ∫_E^3 ρ_t` as `h ↓ 0`. -/
private lemma Sh_F_lim {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) (x : ℝ) :
    Tendsto (fun h => Sh_F U μ h t x) (𝓝[>] 0)
      (𝓝 (∫ y in x..3, rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) y)) := by
  have hrho : ∀ y, rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) y =
      (mExt ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) y).im / Real.pi := fun y =>
    (Sh_rho_eq H ht y).2
  simp only [hrho]
  rw [intervalIntegral.integral_div]
  have hDCT : Tendsto (fun h : ℝ => ∫ y in x..3, (Sh_m U μ t ((y : ℂ) + (h : ℂ) * Complex.I)).im)
      (𝓝[>] 0) (𝓝 (∫ y in x..3, (mExt ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) y).im)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact ((Complex.continuous_im.comp (Sh_m_hcont H hh ht)).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with h hh
      refine Eventually.of_forall fun y _ => ?_
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (Sh_basic H ht (Sh_im_hpath hh y)).2.2.2.1.le
    · exact Eventually.of_forall fun y _ => (Sh_rho_eq H ht y).1
  refine (hDCT.div_const Real.pi).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (Sh_F_int H hh ht x).symm

/-- `|F_h(t, E) - ∫_E^3 ρ_t| ≤ 2h/π`. -/
private lemma Sh_F_N {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {h t : ℝ}
    (hh : 0 < h) (ht : |t| ≤ 1) (x : ℝ) :
    |Sh_F U μ h t x - ∫ y in x..3, rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) y| ≤
      2 * h / Real.pi := by
  have hl := ((tendsto_const_nhds (x := Sh_F U μ h t x)).sub (Sh_F_lim H ht x)).abs
  have hb : Tendsto (fun h' : ℝ => 2 * |h - h'| / Real.pi) (𝓝[>] 0) (𝓝 (2 * |h - 0| / Real.pi)) :=
    (((continuous_const.sub continuous_id).abs.const_mul 2).div_const _).tendsto 0 |>.mono_left
      nhdsWithin_le_nhds
  rw [sub_zero, abs_of_pos hh] at hb
  refine le_of_tendsto_of_tendsto hl hb ?_
  filter_upwards [self_mem_nhdsWithin] with h' hh'
  exact Sh_F_vert H hh hh' ht x

/-- `F_h(t, ·)` is strictly decreasing. -/
private lemma Sh_F_anti {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {h t : ℝ}
    (hh : 0 < h) (ht : |t| ≤ 1) : StrictAnti (Sh_F U μ h t) := by
  refine strictAnti_of_deriv_neg fun x => ?_
  rw [(Sh_F_dx H hh ht x).deriv]
  have := (Sh_basic H ht (Sh_im_hpath hh x)).1
  have := Real.pi_pos
  rw [neg_div]
  exact neg_neg_of_pos (div_pos (by assumption) Real.pi_pos)

/-- The counting function `∫_E^∞ ρ_t = ∫_E^3 ρ_t`, `∫_{-3}^3 ρ_t = 1`, its continuity, and the
quantile `γ_k(t)` of (2.20) [eq:gammak] is its root at level `(k - 1/2)/Mc`. -/
private lemma Sh_quant {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1)
    (hE : -3 < Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) ∧
      Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) < 3) {Mc k : ℕ} (hk : 1 ≤ k)
    (hkM : k ≤ Mc) :
    (∀ x, ∫ y in Set.Ioi x, rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) y =
      ∫ y in x..3, rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) y) ∧
    (∫ y in (-3 : ℝ)..3, rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) y) = 1 ∧
    Continuous (fun x => ∫ y in x..3, rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) y) ∧
    (∫ y in (quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k)..3,
        rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) y) = ((k : ℝ) - 1 / 2) / Mc := by
  obtain ⟨hH, hn⟩ := Sh_tΛ H ht
  set Λ := (t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))
  obtain ⟨r0, rc, ri, r1, -⟩ := rho_stieltjes Λ hH hn
  obtain ⟨-, hsupp⟩ := rho_support Λ hH hn
  have hzero : ∀ y, (y ≤ -3 ∨ 3 ≤ y) → rho Λ y = 0 := by
    intro y hy
    by_contra h
    have : y ∈ Function.support (rho Λ) := h
    rw [hsupp] at this
    rcases hy with hy | hy <;> [linarith [this.1]; linarith [this.2]]
  have hIoi : ∀ x, ∫ y in Set.Ioi x, rho Λ y = ∫ y in x..3, rho Λ y := by
    intro x
    have e := intervalIntegral.integral_interval_add_Ioi (f := rho Λ) (a := x) (b := 3)
      ri.integrableOn ri.integrableOn
    have z : ∫ y in Set.Ioi (3 : ℝ), rho Λ y = 0 :=
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun y hy =>
        hzero y (Or.inr (le_of_lt hy))
    rw [z, add_zero] at e
    exact e.symm
  have h3 : ∫ y in (-3 : ℝ)..3, rho Λ y = 1 := by
    rw [← hIoi]
    have e := intervalIntegral.integral_Iic_add_Ioi (f := rho Λ) (b := -3) ri.integrableOn
      ri.integrableOn
    have z : ∫ y in Set.Iic (-3 : ℝ), rho Λ y = 0 :=
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun y hy => hzero y (Or.inl hy)
    rw [z, zero_add, r1] at e
    exact e
  have hcont : Continuous (fun x => ∫ y in x..3, rho Λ y) := by
    have : (fun x => ∫ y in x..3, rho Λ y) = fun x => -∫ y in (3 : ℝ)..x, rho Λ y := by
      funext x; rw [intervalIntegral.integral_symm]
    rw [this]
    exact (intervalIntegral.continuous_primitive (fun a b => rc.intervalIntegrable a b) 3).neg
  refine ⟨hIoi, h3, hcont, ?_⟩
  have hc1 : ((k : ℝ) - 1 / 2) / Mc < 1 := by
    have hM : (0 : ℝ) < Mc := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hk.trans hkM))
    rw [div_lt_one hM]
    have : (k : ℝ) ≤ Mc := by exact_mod_cast hkM
    linarith
  have hc0 : 0 < ((k : ℝ) - 1 / 2) / Mc := by
    have hM : (0 : ℝ) < Mc := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hk.trans hkM))
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_pos (by linarith) hM
  have hS : {x | ((k : ℝ) - 1 / 2) / Mc ≤ ∫ E in Set.Ioi x, rho Λ E} =
      {x | ((k : ℝ) - 1 / 2) / Mc ≤ ∫ y in x..3, rho Λ y} := by
    ext x; simp only [Set.mem_setOf_eq, hIoi]
  have hroot := Sh_sSup_root hcont (c := ((k : ℝ) - 1 / 2) / Mc) (a := -3) (b := 3)
    (by rw [h3]; exact hc1.le) (fun x hx => by
      have : ∫ y in x..3, rho Λ y = 0 := by
        rw [intervalIntegral.integral_symm]
        have : ∫ y in (3 : ℝ)..x, rho Λ y = 0 :=
          intervalIntegral.integral_zero_ae (Eventually.of_forall fun y hy => by
            rw [Set.uIoc_of_le hx] at hy
            exact hzero y (Or.inr (le_of_lt hy.1)))
        rw [this, neg_zero]
      rw [this]; exact hc0)
  unfold quant
  rw [hS]
  exact hroot.1

end ShiftCount2

/-! ### The regularized quantile `γ_k^h(t)` and its derivative -/

section ShiftGh

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Joint continuity of `(t, z) ↦ a_j(t, z)` on `|t| ≤ 1`, `Im z > 0`. -/
private lemma Sh_a_cont {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) (j : ι) :
    ContinuousOn (fun q : ℝ × ℂ => Sh_a U μ q.1 q.2 j) {q | |q.1| ≤ 1 ∧ 0 < q.2.im} := by
  intro q hq
  have hm := Sh_joint H q hq
  obtain ⟨b1, -⟩ := Sh_basic H hq.1 hq.2
  have hw : 0 < (q.2 + Sh_m U μ q.1 q.2).im := by simp only [Complex.add_im]; linarith [hq.2]
  have h1 : ContinuousWithinAt (fun q : ℝ × ℂ => ((q.1 * μ j : ℝ) : ℂ))
      {q | |q.1| ≤ 1 ∧ 0 < q.2.im} q :=
    (Complex.continuous_ofReal.comp (continuous_fst.mul continuous_const)).continuousWithinAt
  exact (h1.sub (continuous_snd.continuousWithinAt.add hm)).inv₀ (Sh_ne_of_im _ hw)

private lemma Sh_u_cont {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) :
    ContinuousOn (fun q : ℝ × ℂ => Sh_u U μ q.1 q.2) {q | |q.1| ≤ 1 ∧ 0 < q.2.im} := by
  unfold Sh_u
  exact continuousOn_const.mul (continuousOn_finsetSum _ fun j _ =>
    continuousOn_const.mul (Sh_a_cont H j))

/-- `|u_t(z)| ≤ 1/8` and `Im m_t(x + ih) ≥ h/27` for `|x| ≤ 3`, `0 < h ≤ 1`. -/
private lemma Sh_u_bd {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) {z : ℂ} (hz : 0 < z.im) : ‖Sh_u U μ t z‖ ≤ 1 / 8 := by
  obtain ⟨-, -, hw, -⟩ := Sh_basic H ht hz
  unfold Sh_u
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc ((Fintype.card ι : ℝ))⁻¹ * ‖∑ j, (μ j : ℂ) * Sh_a U μ t z j‖
      ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ _j : ι, (1 / 8 : ℝ) := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have ha := (Sh_res_bd _ (Sh_abs_tmu H.eig_le ht j).2 hw.le).2.1
        calc |μ j| * ‖Sh_a U μ t z j‖ ≤ 1 / 10 * (5 / 4) :=
              mul_le_mul (H.eig_le j) ha (norm_nonneg _) (by norm_num)
          _ ≤ 1 / 8 := by norm_num
    _ = 1 / 8 := by simp

private lemma Sh_im_m_lower {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) {x h : ℝ} (hx : |x| ≤ 3) (hh : 0 < h) (hh1 : h ≤ 1) :
    h / 27 ≤ (Sh_m U μ t ((x : ℂ) + (h : ℂ) * Complex.I)).im := by
  set z : ℂ := (x : ℂ) + (h : ℂ) * Complex.I
  have hz : 0 < z.im := Sh_im_hpath hh x
  obtain ⟨b1, -, -, b4, b5, -⟩ := Sh_basic H ht hz
  have hzn : ‖z‖ ≤ 4 := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    rw [abs_of_pos hh]; linarith
  have hwn : ‖z + Sh_m U μ t z‖ ≤ 5 := by
    refine (norm_add_le _ _).trans ?_; linarith
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hA : 1 / 27 ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Sh_a U μ t z j‖ ^ 2 := by
    calc (1 / 27 : ℝ) = ((Fintype.card ι : ℝ))⁻¹ * ∑ _j : ι, (1 / 27 : ℝ) := by simp
      _ ≤ _ := by
        gcongr with j
        have hj : ‖((t * μ j : ℝ) : ℂ) - (z + Sh_m U μ t z)‖ ≤ 51 / 10 := by
          refine (norm_sub_le _ _).trans ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
          linarith [(Sh_abs_tmu H.eig_le ht j).2]
        have hpos : 0 < ‖((t * μ j : ℝ) : ℂ) - (z + Sh_m U μ t z)‖ := norm_pos_iff.2
          (Sh_ne_of_im _ (by simp only [Complex.add_im]; linarith))
        simp only [Sh_a, norm_inv, inv_pow]
        rw [le_inv_comm₀ (by norm_num) (by positivity)]
        nlinarith
  have hzim : z.im = h := by simp [z]
  rw [b5, Complex.add_im, hzim]
  have : 0 < (Sh_m U μ t z).im := b1
  nlinarith

/-- The regularized quantile: the root of `F_h(t, ·) = c`. -/
private def Sh_gh (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (c h t : ℝ) : ℝ :=
  sSup {x | c ≤ Sh_F U μ h t x}

private lemma Sh_gh_root {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {c h t : ℝ}
    (hc : 0 < c) (hh : 0 < h) (ht : |t| ≤ 1) (h3 : c ≤ Sh_F U μ h t (-3)) :
    Sh_F U μ h t (Sh_gh U μ c h t) = c ∧ -3 ≤ Sh_gh U μ c h t ∧ Sh_gh U μ c h t < 3 := by
  have hcont : Continuous (Sh_F U μ h t) :=
    continuous_iff_continuousAt.2 fun x => (Sh_F_dx H hh ht x).continuousAt
  have hanti := Sh_F_anti H hh ht
  have h30 : Sh_F U μ h t 3 = 0 := by simp [Sh_F]
  exact Sh_sSup_root hcont h3 fun x hx => by
    calc Sh_F U μ h t x ≤ Sh_F U μ h t 3 := hanti.antitone hx
      _ < c := by rw [h30]; exact hc

/-- Lipschitz bound `|γ^h(t) - γ^h(t')| ≤ (7/h)|t - t'|` on `[0, 1]`. -/
private lemma Sh_gh_lip {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {c h : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hh1 : h ≤ 1)
    (h3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ Sh_F U μ h t (-3)) {t t' : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht' : t' ∈ Set.Icc (0 : ℝ) 1) :
    |Sh_gh U μ c h t - Sh_gh U μ c h t'| ≤ 7 / h * |t - t'| := by
  have habs : ∀ s ∈ Set.Icc (0 : ℝ) 1, |s| ≤ 1 := fun s hs => by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  obtain ⟨r1, r2, r3⟩ := Sh_gh_root H hc hh (habs t ht) (h3 t ht)
  obtain ⟨r1', r2', r3'⟩ := Sh_gh_root H hc hh (habs t' ht') (h3 t' ht')
  set g := Sh_gh U μ c h t
  set g' := Sh_gh U μ c h t'
  have hseg : ∀ s ∈ Set.uIcc t' t, |s| ≤ 1 := fun s hs =>
    habs s ((Set.uIcc_subset_Icc ht' ht) hs)
  obtain ⟨ξ, hξ, eξ⟩ := Sh_mvt (f := fun s => Sh_F U μ h s g)
    (f' := fun s => ((Sh_u U μ s ((g : ℂ) + (h : ℂ) * Complex.I)).im -
        (Sh_u U μ s ((3 : ℝ) + (h : ℂ) * Complex.I)).im) / Real.pi)
    (a := t') (b := t) fun s hs => Sh_F_dt H hh (hseg s hs) g
  obtain ⟨ζ, hζ, eζ⟩ := Sh_mvt (f := Sh_F U μ h t') (a := g') (b := g)
    fun x _ => Sh_F_dx H hh (habs t' ht') x
  have hζ3 : |ζ| ≤ 3 := by
    rw [abs_le]; rcases Set.mem_uIcc.1 hζ with h' | h' <;> constructor <;> linarith [h'.1, h'.2]
  have hlow := Sh_im_m_lower H (habs t' ht') hζ3 hh hh1
  have hξ1 := hseg ξ hξ
  have hu1 := Sh_u_bd H hξ1 (Sh_im_hpath hh g)
  have hu2 := Sh_u_bd H hξ1 (Sh_im_hpath hh 3)
  have hsum : ((Sh_u U μ ξ ((g : ℂ) + (h : ℂ) * Complex.I)).im -
        (Sh_u U μ ξ ((3 : ℝ) + (h : ℂ) * Complex.I)).im) * (t - t') =
      (Sh_m U μ t' ((ζ : ℂ) + (h : ℂ) * Complex.I)).im * (g - g') := by
    have hπ := Real.pi_pos
    have e1 : Sh_F U μ h t g - Sh_F U μ h t' g = _ := eξ
    have e2 : Sh_F U μ h t' g - Sh_F U μ h t' g' = _ := eζ
    rw [r1] at e1
    rw [r1'] at e2
    field_simp at e1 e2
    linarith
  have hB : |(Sh_u U μ ξ ((g : ℂ) + (h : ℂ) * Complex.I)).im -
      (Sh_u U μ ξ ((3 : ℝ) + (h : ℂ) * Complex.I)).im| ≤ 1 / 4 := by
    have a1 := (Complex.abs_im_le_norm (Sh_u U μ ξ ((g : ℂ) + (h : ℂ) * Complex.I))).trans hu1
    have a2 := (Complex.abs_im_le_norm (Sh_u U μ ξ ((3 : ℝ) + (h : ℂ) * Complex.I))).trans hu2
    calc _ ≤ _ + _ := abs_sub _ _
      _ ≤ 1 / 8 + 1 / 8 := add_le_add a1 a2
      _ = 1 / 4 := by norm_num
  have h27' : 0 < h / 27 := by positivity
  have hpos : 0 < (Sh_m U μ t' ((ζ : ℂ) + (h : ℂ) * Complex.I)).im := by linarith
  have : |g - g'| * (h / 27) ≤ 1 / 4 * |t - t'| := by
    calc |g - g'| * (h / 27) ≤ |g - g'| * (Sh_m U μ t' ((ζ : ℂ) + (h : ℂ) * Complex.I)).im := by
          gcongr
      _ = |(Sh_m U μ t' ((ζ : ℂ) + (h : ℂ) * Complex.I)).im * (g - g')| := by
          rw [abs_mul, abs_of_pos hpos, mul_comm]
      _ = |((Sh_u U μ ξ ((g : ℂ) + (h : ℂ) * Complex.I)).im -
          (Sh_u U μ ξ ((3 : ℝ) + (h : ℂ) * Complex.I)).im) * (t - t')| := by rw [hsum]
      _ ≤ 1 / 4 * |t - t'| := by rw [abs_mul]; gcongr
  have h27 : 0 < h / 27 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hh]
  nlinarith [abs_nonneg (g - g'), abs_nonneg (t - t')]

end ShiftGh

section ShiftGh2

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Sh_gh_contOn {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {c h : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hh1 : h ≤ 1)
    (h3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ Sh_F U μ h t (-3)) :
    ContinuousOn (Sh_gh U μ c h) (Set.Icc 0 1) := by
  have : LipschitzOnWith (Real.toNNReal (7 / h)) (Sh_gh U μ c h) (Set.Icc 0 1) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
      exact Sh_gh_lip H hc hh hh1 h3 hx hy
  exact this.continuousOn

/-- `d/dt γ^h(t) = (Im u_t(z) - Im u_t(3 + ih)) / Im m_t(z)` at `z = γ^h(t) + ih`: the
regularized form of (A.46) [equation_derivative_gamma_k_t]. -/
private lemma Sh_gh_deriv {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {c h : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hh1 : h ≤ 1)
    (h3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ Sh_F U μ h t (-3)) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (Sh_gh U μ c h)
      (((Sh_u U μ t₀ ((Sh_gh U μ c h t₀ : ℂ) + (h : ℂ) * Complex.I)).im -
          (Sh_u U μ t₀ ((3 : ℝ) + (h : ℂ) * Complex.I)).im) /
        (Sh_m U μ t₀ ((Sh_gh U μ c h t₀ : ℂ) + (h : ℂ) * Complex.I)).im) t₀ := by
  have habs : ∀ s ∈ Set.Ioo (0 : ℝ) 1, |s| ≤ 1 := fun s hs => by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have habs' : |t₀| < 1 := by rw [abs_lt]; constructor <;> linarith [ht₀.1, ht₀.2]
  set g := Sh_gh U μ c h
  have hcont := Sh_gh_contOn H hc hh hh1 h3
  have h7 : ContinuousAt g t₀ :=
    hcont.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hFt : ContinuousAt (fun q : ℝ × ℝ => ((Sh_u U μ q.1 ((q.2 : ℂ) + (h : ℂ) * Complex.I)).im -
      (Sh_u U μ q.1 ((3 : ℝ) + (h : ℂ) * Complex.I)).im) / Real.pi) (t₀, g t₀) := by
    have hset : {q : ℝ × ℂ | |q.1| ≤ 1 ∧ 0 < q.2.im} ∈ 𝓝 ((t₀, (g t₀ : ℂ) + (h : ℂ) * Complex.I)) := by
      have ho : IsOpen ({q : ℝ × ℂ | |q.1| < 1} ∩ {q : ℝ × ℂ | 0 < q.2.im}) :=
        (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
          (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_snd))
      exact Filter.mem_of_superset (ho.mem_nhds ⟨habs', Sh_im_hpath hh (g t₀)⟩)
        fun q hq => ⟨hq.1.le, hq.2⟩
    have hset3 : {q : ℝ × ℂ | |q.1| ≤ 1 ∧ 0 < q.2.im} ∈
        𝓝 ((t₀, ((3 : ℝ) : ℂ) + (h : ℂ) * Complex.I)) := by
      have ho : IsOpen ({q : ℝ × ℂ | |q.1| < 1} ∩ {q : ℝ × ℂ | 0 < q.2.im}) :=
        (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
          (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_snd))
      exact Filter.mem_of_superset (ho.mem_nhds ⟨habs', Sh_im_hpath hh 3⟩)
        fun q hq => ⟨hq.1.le, hq.2⟩
    have c1 := (Sh_u_cont H).continuousAt hset
    have c2 := (Sh_u_cont H).continuousAt hset3
    have p1 : ContinuousAt (fun q : ℝ × ℝ => ((q.1, (q.2 : ℂ) + (h : ℂ) * Complex.I) : ℝ × ℂ))
        (t₀, g t₀) := by fun_prop
    have p2 : ContinuousAt (fun q : ℝ × ℝ => ((q.1, ((3 : ℝ) : ℂ) + (h : ℂ) * Complex.I) : ℝ × ℂ))
        (t₀, g t₀) := by fun_prop
    have d1 := ContinuousAt.comp_of_eq c1 p1 rfl
    have d2 := ContinuousAt.comp_of_eq c2 p2 rfl
    exact ((Complex.continuous_im.continuousAt.comp d1).sub
      (Complex.continuous_im.continuousAt.comp d2)).div_const _
  have h5 : ContinuousAt (fun x : ℝ => -(Sh_m U μ t₀ ((x : ℂ) + (h : ℂ) * Complex.I)).im /
      Real.pi) (g t₀) :=
    ((Complex.continuous_im.comp (Sh_m_hcont H hh habs'.le)).neg.div_const _).continuousAt
  have hpos := (Sh_basic H habs'.le (Sh_im_hpath hh (g t₀))).1
  have h6 : -(Sh_m U μ t₀ ((g t₀ : ℂ) + (h : ℂ) * Complex.I)).im / Real.pi ≠ 0 := by
    have := Real.pi_pos
    exact div_ne_zero (by linarith) this.ne'
  have key := Sh_ift (F := Sh_F U μ h)
    (Ft := fun s x => ((Sh_u U μ s ((x : ℂ) + (h : ℂ) * Complex.I)).im -
      (Sh_u U μ s ((3 : ℝ) + (h : ℂ) * Complex.I)).im) / Real.pi)
    (Fx := fun s x => -(Sh_m U μ s ((x : ℂ) + (h : ℂ) * Complex.I)).im / Real.pi)
    (g := g) (c := c) ht₀
    (fun t ht => (Sh_gh_root H hc hh (habs t ht) (h3 t ⟨ht.1.le, ht.2.le⟩)).1)
    (fun t ht x => Sh_F_dt H hh (habs t ht) x) (fun x => Sh_F_dx H hh habs'.le x) hFt h5 h6 h7
  refine key.congr_deriv ?_
  have := Real.pi_pos
  field_simp

/-- The regularized quantile is uniformly close to `γ_k(t)` once `2h/π < ρ₀ δ`, where `ρ_t ≥ ρ₀`
on `[γ_k(t) - δ, γ_k(t) + δ]`. -/
private lemma Sh_gh_close {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {h t : ℝ}
    (hh : 0 < h) (ht : |t| ≤ 1)
    (hE : -3 < Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) ∧
      Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) < 3) {Mc k : ℕ} (hk : 1 ≤ k)
    (hkM : k ≤ Mc) {δ ρ₀ : ℝ} (hδ : 0 < δ)
    (hρ : ∀ y ∈ Set.Icc (quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k - δ)
      (quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k + δ),
        ρ₀ ≤ rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) y)
    (hsmall : 2 * h / Real.pi < ρ₀ * δ)
    (hroot : Sh_F U μ h t (Sh_gh U μ (((k : ℝ) - 1 / 2) / Mc) h t) = ((k : ℝ) - 1 / 2) / Mc) :
    |Sh_gh U μ (((k : ℝ) - 1 / 2) / Mc) h t -
      quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k| < δ := by
  obtain ⟨-, -, hcont, hN⟩ := Sh_quant H ht hE hk hkM
  obtain ⟨hH, hn⟩ := Sh_tΛ H ht
  set Λ := (t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))
  set γ := quant (rho Λ) Mc k
  set c := ((k : ℝ) - 1 / 2) / Mc
  obtain ⟨-, rc, ri, -⟩ := rho_stieltjes Λ hH hn
  have hii : ∀ a b, IntervalIntegrable (rho Λ) MeasureTheory.volume a b := fun a b =>
    rc.intervalIntegrable a b
  have hlow : ∀ a b, a ≤ b → Set.Icc a b ⊆ Set.Icc (γ - δ) (γ + δ) →
      ρ₀ * (b - a) ≤ ∫ y in a..b, rho Λ y := by
    intro a b hab hsub
    have := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := ρ₀))
      (hii a b) fun y hy => hρ y (hsub hy)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have e1 : ∫ y in (γ - δ)..3, rho Λ y = (∫ y in (γ - δ)..γ, rho Λ y) + ∫ y in γ..3, rho Λ y :=
    (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
  have e2 : ∫ y in γ..3, rho Λ y = (∫ y in γ..(γ + δ), rho Λ y) + ∫ y in (γ + δ)..3, rho Λ y :=
    (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
  have l1 := hlow (γ - δ) γ (by linarith) (Set.Icc_subset_Icc le_rfl (by linarith))
  have l2 := hlow γ (γ + δ) (by linarith) (Set.Icc_subset_Icc (by linarith) le_rfl)
  have f1 := Sh_F_N H hh ht (γ - δ)
  have f2 := Sh_F_N H hh ht (γ + δ)
  refine Sh_root_close (f := fun x => ∫ y in x..3, rho Λ y) (g := Sh_F U μ h t)
    (Sh_F_anti H hh ht).antitone (c := c) (ε := 2 * h / Real.pi) hroot ?_ ?_ ?_ ?_
  · show c + 2 * h / Real.pi < ∫ y in (γ - δ)..3, rho Λ y
    rw [e1, hN]; linarith
  · show ∫ y in (γ + δ)..3, rho Λ y < c - 2 * h / Real.pi
    rw [e2] at hN; linarith
  · rw [abs_sub_comm]; exact f1
  · rw [abs_sub_comm]; exact f2

end ShiftGh2

/-! ### Bounds of Lemma A.1 [lemma_usual_properties_of_m_and_mu] along the family -/

section ShiftEst

/-- (A.1) [square_root_density] and (A.12) [de_ir_0] along `tΛ`, in spectral form, for `|z| ≤ 4`
and `Re z ∈ [E_t⁻, E_t⁺]`: `Im m ∼ √(κ + η)`, `|1 - ⟨M²⟩| ≳ √(κ + η)`,
`|1 - m²| ≲ √(κ + η) + ⟨Λ²⟩`. -/
private lemma Sh_edge_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ), Sh_Hyp U μ → ∀ t : ℝ, |t| ≤ 1 →
      ∀ z : ℂ, ‖z‖ ≤ 4 → 0 < z.im →
      z.re ∈ Set.Icc (Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))))
        (Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) →
      C⁻¹ * Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) ≤
          (Sh_m U μ t z).im ∧
        (Sh_m U μ t z).im ≤
          C * Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) ∧
        C⁻¹ * Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) ≤
          ‖1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2‖ ∧
        ‖1 - Sh_m U μ t z ^ 2‖ ≤
          C * (Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) +
            ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) := by
  obtain ⟨C₀, hC₀, h0⟩ := de_ir_0 (1 / 4) (by norm_num)
  obtain ⟨C₁, hC₁, h1⟩ := square_root_density (1 / 4) (by norm_num)
  refine ⟨C₀ * C₁ + C₀ + C₁ + 1, by nlinarith [mul_pos hC₀ hC₁], ?_⟩
  intro ι _ _ _ U μ H t ht z hz hzim hre
  obtain ⟨hH, hn⟩ := Sh_tΛ H ht
  set Λ := (t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))
  have hz4 : ‖z‖ ≤ (1 / 4 : ℝ)⁻¹ := by norm_num; exact hz
  have htr : ntr Λ = 0 := by
    simp only [Λ, Sh_cd_real_smul, Sh_ntr_cd]
    rw [show ∑ j, (((t * μ j : ℝ)) : ℂ) = ((t * ∑ j, μ j : ℝ) : ℂ) by
      push_cast; rw [Finset.mul_sum], H.sum_zero]
    simp
  obtain ⟨d1, d2, d3, d4⟩ := h0 ι Λ hH hn htr z hz4 hzim hre
  obtain ⟨-, s2⟩ := h1 ι Λ hH hn
  obtain ⟨s3, s4⟩ := (s2 z hz4 hzim).1 hre
  obtain ⟨-, -, -, -, -, -, hM⟩ := Sh_basic H ht hzim
  have hA : ntr (MSol Λ z ^ 2) = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2 := by
    rw [hM, Sh_cd_pow, Sh_ntr_cd]
  rw [hA] at d1 d2
  have hsq : avgSq Λ ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 := by
    have e : avgSq Λ = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, (t * μ j) ^ 2 := by
      simp only [avgSq, Λ, Sh_cd_real_smul, Sh_cd_mul, Sh_ntr_cd]
      rw [show ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (((t * μ j : ℝ)) : ℂ) * (((t * μ j : ℝ)) : ℂ) =
        (((((Fintype.card ι : ℝ))⁻¹ * ∑ j, (t * μ j) ^ 2 : ℝ)) : ℂ) by push_cast; simp [sq]]
      rw [Complex.ofReal_re]
    rw [e]
    have : t ^ 2 ≤ 1 := by nlinarith [abs_le.1 ht, sq_abs t]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
    rw [mul_pow]
    nlinarith [sq_nonneg (μ j)]
  set S := Real.sqrt (kappa Λ z.re + z.im)
  set m := Sh_m U μ t z
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hσ0 : 0 ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 := by positivity
  have hm0 : 0 ≤ m.im := (Sh_basic H ht hzim).1.le
  have hCC : 0 < C₀ * C₁ + C₀ + C₁ + 1 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ s3
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hC₁ (by nlinarith [mul_pos hC₀ hC₁])) hS0
  · refine s4.trans ?_
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_pos hC₀ hC₁]) hS0
  · calc (C₀ * C₁ + C₀ + C₁ + 1)⁻¹ * S ≤ (C₀ * C₁)⁻¹ * S :=
          mul_le_mul_of_nonneg_right (inv_anti₀ (mul_pos hC₀ hC₁) (by linarith)) hS0
      _ = C₀⁻¹ * (C₁⁻¹ * S) := by rw [mul_inv]; ring
      _ ≤ C₀⁻¹ * m.im := mul_le_mul_of_nonneg_left s3 (inv_nonneg.2 hC₀.le)
      _ ≤ _ := d1
  · calc ‖1 - m ^ 2‖ ≤ C₀ * (m.im + avgSq Λ) := d4
      _ ≤ C₀ * (C₁ * S + ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add s4 hsq) hC₀.le
      _ ≤ (C₀ * C₁ + C₀ + C₁ + 1) * (S + ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) := by
          nlinarith [mul_nonneg (mul_nonneg hC₀.le hC₁.le) hS0, mul_nonneg hC₀.le hσ0,
            mul_nonneg hC₁.le hS0, mul_nonneg (mul_nonneg hC₀.le hC₁.le) hσ0,
            mul_nonneg hC₁.le hσ0]

end ShiftEst

section ShiftVert

/-- Integration of `|f'(s)| ≤ L (κ + s)^{-1/2}` over `[h, η]`: `|f(η) - f(h)| ≤ 2L √(κ + η)`. -/
private lemma Sh_vint {f f' : ℝ → ℂ} {h η κ L : ℝ} (hh : 0 < h) (hhη : h ≤ η) (hκ : 0 ≤ κ)
    (hL : 0 ≤ L) (hd : ∀ s ∈ Set.Icc h η, HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Set.Icc h η, ‖f' s‖ ≤ L / Real.sqrt (κ + s)) :
    ‖f η - f h‖ ≤ 2 * L * Real.sqrt (κ + η) := by
  have hpos : ∀ s ∈ Set.Icc h η, 0 < κ + s := fun s hs => by linarith [hs.1]
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun s => f s - f h) (f' := f') (a := h) (b := η)
    (B := fun s => 2 * L * Real.sqrt (κ + s) - 2 * L * Real.sqrt (κ + h))
    (B' := fun s => L / Real.sqrt (κ + s))
    (fun s hs => ((hd s hs).sub_const (f h)).continuousAt.continuousWithinAt)
    (fun s hs => ((hd s (Set.Ico_subset_Icc_self hs)).sub_const (f h)).hasDerivWithinAt)
    (by simp)
    (fun s hs => by
      have : ContinuousAt (fun s => 2 * L * Real.sqrt (κ + s) - 2 * L * Real.sqrt (κ + h)) s := by
        fun_prop
      exact this.continuousWithinAt)
    (fun s hs => by
      have h1 := ((hasDerivAt_id s).const_add κ).sqrt (hpos s (Set.Ico_subset_Icc_self hs)).ne'
      have h2 := (h1.const_mul (2 * L)).sub_const (2 * L * Real.sqrt (κ + h))
      refine (h2.congr_deriv ?_).hasDerivWithinAt
      have := Real.sqrt_pos.2 (hpos s (Set.Ico_subset_Icc_self hs))
      simp only [id]
      field_simp)
    (fun s hs => hb s (Set.Ico_subset_Icc_self hs))
    (Set.right_mem_Icc.2 hhη)
  refine key.trans ?_
  have := Real.sqrt_nonneg (κ + h)
  nlinarith [mul_nonneg (mul_nonneg zero_le_two hL) this]

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `Δ̃_t(z) = z + m_t(z) + 1/m_t(z)`, so that `Δ_ev = Re Δ̃_1(z₁)` in (5.2)
[definition_shift_eigenvector]. -/
private def Sh_D (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  z + Sh_m U μ t z + (Sh_m U μ t z)⁻¹

end ShiftVert

set_option maxHeartbeats 800000 in -- elaboration of large sums over the spectrum
/-- Vertical moves at `Re z = x ∈ [E_t⁻, E_t⁺]` between heights `h ≤ η ≤ 1`:
`|m(x + iη) - m(x + ih)| ≲ √(κ + η)` and `|Δ̃(x + iη) - Δ̃(x + ih)| ≲ ⟨Λ²⟩ √(κ + η)`. -/
private lemma Sh_vert :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ), Sh_Hyp U μ → ∀ t : ℝ, |t| ≤ 1 →
      ∀ x : ℝ, |x| ≤ 3 →
      x ∈ Set.Icc (Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))))
        (Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) →
      ∀ h η : ℝ, 0 < h → h ≤ η → η ≤ 1 →
      ‖Sh_m U μ t ((x : ℂ) + (η : ℂ) * Complex.I) - Sh_m U μ t ((x : ℂ) + (h : ℂ) * Complex.I)‖ ≤
          K * Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) x + η) ∧
        ‖Sh_D U μ t ((x : ℂ) + (η : ℂ) * Complex.I) - Sh_D U μ t ((x : ℂ) + (h : ℂ) * Complex.I)‖ ≤
          K * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) *
            Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) x + η) := by
  obtain ⟨C, hC, hEB⟩ := Sh_edge_bounds
  refine ⟨2 * C * (1600 / 49 * 4) + 2 * C, by nlinarith, ?_⟩
  intro ι _ _ _ U μ H t ht x hx hxE h η hh hhη hη1
  set κ := kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) x
  have hκ : 0 ≤ κ := le_min (abs_nonneg _) (abs_nonneg _)
  set σ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2
  have hσ : 0 ≤ σ := by positivity
  have hC0 : 0 < C := by linarith
  -- facts on the vertical segment
  have hz : ∀ s ∈ Set.Icc h η, 0 < ((x : ℂ) + (s : ℂ) * Complex.I).im ∧
      ‖(x : ℂ) + (s : ℂ) * Complex.I‖ ≤ 4 ∧ ((x : ℂ) + (s : ℂ) * Complex.I).re = x := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    refine ⟨by simpa using hs0, ?_, by simp⟩
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    rw [abs_of_pos hs0]; linarith [hs.2]
  have hA : ∀ s ∈ Set.Icc h η,
      ‖1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((x : ℂ) + (s : ℂ) * Complex.I) j ^ 2‖ ≥
        C⁻¹ * Real.sqrt (κ + s) ∧
      ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((x : ℂ) + (s : ℂ) * Complex.I) j ^ 2‖ ≤ 1 := by
    intro s hs
    obtain ⟨z1, z2, z3⟩ := hz s hs
    have e := (hEB ι U μ H t ht _ z2 z1 (by rw [z3]; exact hxE)).2.2.1
    rw [z3, show ((x : ℂ) + (s : ℂ) * Complex.I).im = s by simp] at e
    refine ⟨e, ?_⟩
    obtain ⟨-, -, -, -, -, b6, -⟩ := Sh_basic H ht z1
    refine le_trans ?_ b6.le
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    gcongr
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_pow]
  -- derivative of `m` along the segment
  have hdm : ∀ s ∈ Set.Icc h η, HasDerivAt (fun s : ℝ => Sh_m U μ t ((x : ℂ) + (s : ℂ) * Complex.I))
      ((((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((x : ℂ) + (s : ℂ) * Complex.I) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((x : ℂ) + (s : ℂ) * Complex.I) j ^ 2) *
          Complex.I) s := fun s hs =>
    (Sh_dm_z H ht (hz s hs).1).comp s (Sh_vpath x s)
  have hsq : ∀ s ∈ Set.Icc h η, 0 < Real.sqrt (κ + s) := fun s hs =>
    Real.sqrt_pos.2 (by linarith [hs.1])
  have hmd : ∀ s ∈ Set.Icc h η,
      ‖(((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((x : ℂ) + (s : ℂ) * Complex.I) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((x : ℂ) + (s : ℂ) * Complex.I) j ^ 2) *
          Complex.I‖ ≤ C / Real.sqrt (κ + s) := by
    intro s hs
    obtain ⟨a1, a2⟩ := hA s hs
    have hp : 0 < C⁻¹ * Real.sqrt (κ + s) := mul_pos (inv_pos.2 hC0) (hsq s hs)
    rw [norm_mul, Complex.norm_I, mul_one, norm_div, div_le_div_iff₀ (lt_of_lt_of_le hp a1)
      (hsq s hs)]
    calc _ ≤ 1 * Real.sqrt (κ + s) := by gcongr
      _ = C * (C⁻¹ * Real.sqrt (κ + s)) := by field_simp
      _ ≤ _ := by gcongr
  have V1 := Sh_vint (f := fun s : ℝ => Sh_m U μ t ((x : ℂ) + (s : ℂ) * Complex.I)) hh hhη hκ
    hC0.le hdm hmd
  refine ⟨V1.trans ?_, ?_⟩
  · gcongr; nlinarith
  -- `Δ̃' = (m² - A)/(m² (1 - A))`
  have hD : ∀ s ∈ Set.Icc h η, ∃ d : ℂ, HasDerivAt
      (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I + Sh_m U μ t ((x : ℂ) + (s : ℂ) * Complex.I) +
        (Sh_m U μ t ((x : ℂ) + (s : ℂ) * Complex.I))⁻¹) d s ∧
      ‖d‖ ≤ C * (1600 / 49 * 4) * σ / Real.sqrt (κ + s) := by
    intro s hs
    obtain ⟨z1, z2, -⟩ := hz s hs
    set z := (x : ℂ) + (s : ℂ) * Complex.I
    obtain ⟨b1, b2, b3, b4, -⟩ := Sh_basic H ht z1
    set m := Sh_m U μ t z
    set A := ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2
    obtain ⟨-, m2, -, m4, -⟩ := Sh_m_bd μ t H.sum_zero H.eig_le ht b3.le
    have hmA : m = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (((t * μ j : ℝ) : ℂ) - (z + m))⁻¹ := b2
    rw [← hmA] at m2 m4
    have hm0 : m ≠ 0 := fun h0 => by rw [h0, mul_zero, norm_zero] at m2; linarith
    have hwn : ‖z + m‖ ≤ 5 := (norm_add_le _ _).trans (by linarith)
    have hmlow : 7 / 40 ≤ ‖m‖ := by
      rw [norm_mul] at m2
      by_contra hc; push_neg at hc
      nlinarith [norm_nonneg (z + m)]
    obtain ⟨a1, a2⟩ := hA s hs
    have hA1 : 1 - A ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at a1
      linarith [mul_pos (inv_pos.2 hC0) (hsq s hs)]
    have hderiv := ((Sh_vpath x s).add (hdm s hs)).add ((hdm s hs).inv hm0)
    have e : Complex.I + A / (1 - A) * Complex.I + -(A / (1 - A) * Complex.I) / m ^ 2 =
        Complex.I * ((m ^ 2 - A) / (m ^ 2 * (1 - A))) := by
      field_simp; ring
    refine ⟨Complex.I * ((m ^ 2 - A) / (m ^ 2 * (1 - A))), hderiv.congr_deriv e, ?_⟩
    rw [norm_mul, Complex.norm_I, one_mul, norm_div, norm_mul, norm_pow]
    have hp : 0 < C⁻¹ * Real.sqrt (κ + s) := mul_pos (inv_pos.2 hC0) (hsq s hs)
    have hm2 : (7 / 40 : ℝ) ^ 2 ≤ ‖m‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hmlow 2
    have h1 : (49 / 1600 : ℝ) * (C⁻¹ * Real.sqrt (κ + s)) ≤ ‖m‖ ^ 2 * ‖1 - A‖ := by
      rw [show (49 / 1600 : ℝ) = (7 / 40) ^ 2 by norm_num]
      exact mul_le_mul hm2 a1 hp.le (sq_nonneg _)
    have hpos2 : 0 < ‖m‖ ^ 2 * ‖1 - A‖ := lt_of_lt_of_le (mul_pos (by norm_num) hp) h1
    rw [div_le_div_iff₀ hpos2 (hsq s hs)]
    have hS := (hsq s hs).le
    calc ‖m ^ 2 - A‖ * Real.sqrt (κ + s) ≤ 4 * σ * Real.sqrt (κ + s) :=
          mul_le_mul_of_nonneg_right m4 hS
      _ = C * (1600 / 49 * 4) * σ * ((49 / 1600) * (C⁻¹ * Real.sqrt (κ + s))) := by
          have hCi : C * C⁻¹ = 1 := mul_inv_cancel₀ hC0.ne'
          linear_combination (-4 * σ * Real.sqrt (κ + s)) * hCi
      _ ≤ C * (1600 / 49 * 4) * σ * (‖m‖ ^ 2 * ‖1 - A‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  choose d hd1 hd2 using hD
  have V4 := Sh_vint (f := fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I +
      Sh_m U μ t ((x : ℂ) + (s : ℂ) * Complex.I) + (Sh_m U μ t ((x : ℂ) + (s : ℂ) * Complex.I))⁻¹)
    (f' := fun s => if hs : s ∈ Set.Icc h η then d s hs else 0) hh hhη hκ
    (L := C * (1600 / 49 * 4) * σ) (by positivity)
    (fun s hs => by simp only [hs, dif_pos]; exact hd1 s hs)
    (fun s hs => by simp only [hs, dif_pos]; exact (hd2 s hs).trans (le_of_eq (by ring)))
  simp only [Sh_D]
  refine V4.trans ?_
  have := Real.sqrt_nonneg (κ + η)
  nlinarith [mul_nonneg hσ this, mul_nonneg (mul_nonneg hC0.le hσ) this]

section ShiftAux3

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- At height `η`: `|∂_z m_t| ≤ 1/η` (from (A.3) [equation_z_im_m]), and
`|∂_z Δ̃_t| ≤ 1 + 34/η` when `|z| ≤ 4`. -/
private lemma Sh_dz_bd {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) {z : ℂ} (hz : 0 < z.im) (hz4 : ‖z‖ ≤ 4) :
    ‖(((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2)‖ ≤ 1 / z.im ∧
      7 / 40 ≤ ‖Sh_m U μ t z‖ := by
  obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := Sh_basic H ht hz
  set B := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Sh_a U μ t z j‖ ^ 2
  set A := ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2
  have hAB : ‖A‖ ≤ B := by
    simp only [A, B, norm_mul, norm_inv, Complex.norm_natCast]
    gcongr
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_pow]
  have hw : (z + Sh_m U μ t z).im = z.im + (Sh_m U μ t z).im := Complex.add_im _ _
  have hB : B * (z.im + (Sh_m U μ t z).im) = (Sh_m U μ t z).im := by
    have := b5; rw [hw] at this; linear_combination -this
  have hmim : (Sh_m U μ t z).im ≤ 1 := (Complex.im_le_norm _).trans b4.le
  constructor
  · have h1 : 1 - B ≤ ‖1 - A‖ := by
      have := norm_sub_norm_le (1 : ℂ) A
      rw [norm_one] at this; linarith
    have h1B : 0 < 1 - B := by linarith
    rw [norm_div, div_le_div_iff₀ (lt_of_lt_of_le h1B h1) hz]
    calc ‖A‖ * z.im ≤ B * z.im := by gcongr
      _ = (Sh_m U μ t z).im * (1 - B) := by nlinarith
      _ ≤ 1 * ‖1 - A‖ := by
          apply mul_le_mul hmim h1 h1B.le zero_le_one
  · obtain ⟨-, m2, -, -, -⟩ := Sh_m_bd μ t H.sum_zero H.eig_le ht b3.le
    have hmA : Sh_m U μ t z = ((Fintype.card ι : ℂ))⁻¹ *
        ∑ j, (((t * μ j : ℝ) : ℂ) - (z + Sh_m U μ t z))⁻¹ := b2
    rw [← hmA, norm_mul] at m2
    have hwn : ‖z + Sh_m U μ t z‖ ≤ 5 := (norm_add_le _ _).trans (by linarith)
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg (z + Sh_m U μ t z), norm_nonneg (Sh_m U μ t z)]

set_option maxHeartbeats 800000 in -- elaboration of large sums over the spectrum
/-- Horizontal Lipschitz bounds at height `η ∈ (0, 1]` for `|x|, |x'| ≤ 3`. -/
private lemma Sh_horiz {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {x x' : ℝ} (hx : |x| ≤ 3) (hx' : |x'| ≤ 3) :
    ‖Sh_m U μ t ((x : ℂ) + (η : ℂ) * Complex.I) - Sh_m U μ t ((x' : ℂ) + (η : ℂ) * Complex.I)‖ ≤
        |x - x'| / η ∧
      ‖Sh_D U μ t ((x : ℂ) + (η : ℂ) * Complex.I) - Sh_D U μ t ((x' : ℂ) + (η : ℂ) * Complex.I)‖ ≤
        (1 + 34 / η) * |x - x'| := by
  have hz : ∀ y : ℝ, |y| ≤ 3 → 0 < ((y : ℂ) + (η : ℂ) * Complex.I).im ∧
      ‖(y : ℂ) + (η : ℂ) * Complex.I‖ ≤ 4 := fun y hy => by
    refine ⟨by simpa using hη, (norm_add_le _ _).trans ?_⟩
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    rw [abs_of_pos hη]; linarith
  have him : ∀ y : ℝ, ((y : ℂ) + (η : ℂ) * Complex.I).im = η := fun y => by simp
  -- the segment between `x'` and `x`
  wlog hle : x' ≤ x generalizing x x'
  · obtain ⟨a1, a2⟩ := this hx' hx (by linarith)
    exact ⟨by rw [norm_sub_rev, abs_sub_comm]; exact a1,
      by rw [norm_sub_rev, abs_sub_comm]; exact a2⟩
  have hseg : ∀ y ∈ Set.Icc x' x, |y| ≤ 3 := fun y hy => by
    rw [abs_le] at hx hx' ⊢; constructor <;> linarith [hy.1, hy.2]
  have hdm : ∀ y ∈ Set.Icc x' x, HasDerivAt (fun y : ℝ => Sh_m U μ t ((y : ℂ) + (η : ℂ) * Complex.I))
      ((((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) * 1)
        y := fun y hy => (Sh_dm_z H ht (hz y (hseg y hy)).1).comp y (Sh_hpath η y)
  have hb : ∀ y ∈ Set.Icc x' x, ‖(((Fintype.card ι : ℂ))⁻¹ *
      ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) * 1‖
        ≤ 1 / η := fun y hy => by
    have := (Sh_dz_bd H ht (hz y (hseg y hy)).1 (hz y (hseg y hy)).2).1
    rw [him y] at this
    rwa [mul_one]
  have e1 := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun y : ℝ =>
      Sh_m U μ t ((y : ℂ) + (η : ℂ) * Complex.I)) (C := 1 / η)
    (fun y hy => (hdm y hy).hasDerivWithinAt) (fun y hy => hb y (Set.Ico_subset_Icc_self hy))
    x (Set.right_mem_Icc.2 hle)
  rw [abs_of_nonneg (by linarith)]
  refine ⟨e1.trans (le_of_eq (by ring)), ?_⟩
  have hdD : ∀ y ∈ Set.Icc x' x, HasDerivAt (fun y : ℝ =>
      (y : ℂ) + (η : ℂ) * Complex.I + Sh_m U μ t ((y : ℂ) + (η : ℂ) * Complex.I) +
        (Sh_m U μ t ((y : ℂ) + (η : ℂ) * Complex.I))⁻¹)
      (1 + (((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) * 1 +
        -((((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) * 1) /
          Sh_m U μ t ((y : ℂ) + (η : ℂ) * Complex.I) ^ 2) y := fun y hy => by
    have hm0 : Sh_m U μ t ((y : ℂ) + (η : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have := (Sh_dz_bd H ht (hz y (hseg y hy)).1 (hz y (hseg y hy)).2).2
      rw [h0, norm_zero] at this; linarith
    exact ((Sh_hpath η y).add (hdm y hy)).add ((hdm y hy).inv hm0)
  have hbD : ∀ y ∈ Set.Icc x' x, ‖1 + (((Fintype.card ι : ℂ))⁻¹ *
        ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) * 1 +
        -((((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) * 1) /
          Sh_m U μ t ((y : ℂ) + (η : ℂ) * Complex.I) ^ 2‖ ≤ 1 + 34 / η := fun y hy => by
    obtain ⟨d1, d2⟩ := Sh_dz_bd H ht (hz y (hseg y hy)).1 (hz y (hseg y hy)).2
    rw [him] at d1
    set q := (((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((y : ℂ) + (η : ℂ) * Complex.I) j ^ 2) * 1
    have hq : ‖q‖ ≤ 1 / η := by simp only [q, mul_one]; exact d1
    set mm := Sh_m U μ t ((y : ℂ) + (η : ℂ) * Complex.I)
    have hmm : (7 / 40 : ℝ) ^ 2 ≤ ‖mm‖ ^ 2 := pow_le_pow_left₀ (by norm_num) d2 2
    have hmm0 : 0 < ‖mm‖ ^ 2 := lt_of_lt_of_le (by norm_num) hmm
    calc ‖1 + q + -q / mm ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖q‖ + ‖q‖ / ‖mm‖ ^ 2 := by
          refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_of_eq ?_))
          rw [norm_div, norm_neg, norm_pow]
      _ ≤ 1 + 1 / η + (1 / η) / (7 / 40) ^ 2 := by
          rw [norm_one]
          gcongr
      _ ≤ 1 + 34 / η := by
          rw [div_div]
          have : 1 / η + 1 / (η * (7 / 40) ^ 2) = (1 + 1600 / 49) / η := by field_simp; ring
          rw [add_assoc, this]
          gcongr
          norm_num
  have e2 := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun y : ℝ =>
      (y : ℂ) + (η : ℂ) * Complex.I + Sh_m U μ t ((y : ℂ) + (η : ℂ) * Complex.I) +
        (Sh_m U μ t ((y : ℂ) + (η : ℂ) * Complex.I))⁻¹) (C := 1 + 34 / η)
    (fun y hy => (hdD y hy).hasDerivWithinAt) (fun y hy => hbD y (Set.Ico_subset_Icc_self hy))
    x (Set.right_mem_Icc.2 hle)
  simp only [Sh_D]
  exact e2

/-- `Im u_t(3 + ih) ≤ h/15` and `Im u_t(z) / Im m_t(z) = ⟨M Λ M^*⟩/⟨M M^*⟩`. -/
private lemma Sh_u3 {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) {h : ℝ} (hh : 0 < h) :
    |(Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im| ≤ h / 15 := by
  set z : ℂ := ((3 : ℝ) : ℂ) + (h : ℂ) * Complex.I
  have hz : 0 < z.im := Sh_im_hpath hh 3
  obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := Sh_basic H ht hz
  set w := z + Sh_m U μ t z
  have hre : 2 ≤ w.re := by
    have := Complex.abs_re_le_norm (Sh_m U μ t z)
    simp only [w, z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [abs_le] at this; linarith
  have ha : ∀ j, ‖Sh_a U μ t z j‖ ≤ 10 / 19 := by
    intro j
    have hx := (Sh_abs_tmu H.eig_le ht j).2
    have h1 : 19 / 10 ≤ ‖((t * μ j : ℝ) : ℂ) - w‖ := by
      have := Complex.abs_re_le_norm (((t * μ j : ℝ) : ℂ) - w)
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      rw [abs_le] at hx
      rw [abs_le] at this
      have : |t * μ j - w.re| ≥ 19 / 10 := by
        rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
      linarith [Complex.abs_re_le_norm (((t * μ j : ℝ) : ℂ) - w),
        show |(((t * μ j : ℝ) : ℂ) - w).re| = |t * μ j - w.re| by simp]
    simp only [Sh_a, norm_inv]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hB : ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Sh_a U μ t z j‖ ^ 2 ≤ 1 / 3 := by
    calc ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Sh_a U μ t z j‖ ^ 2
        ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ _j : ι, (10 / 19 : ℝ) ^ 2 := by
          gcongr with j; exact ha j
      _ ≤ 1 / 3 := by simp; norm_num
  have e : w.im = h + (Sh_m U μ t z).im := by simp [w, z]
  have hwim : w.im ≤ 2 * h := by
    have : (Sh_m U μ t z).im ≤ w.im / 3 := by
      rw [b5]
      have : 0 ≤ w.im := by rw [e]; linarith
      nlinarith
    linarith
  have hu : (Sh_u U μ t z).im = w.im * (((Fintype.card ι : ℝ))⁻¹ *
      ∑ j, μ j * ‖Sh_a U μ t z j‖ ^ 2) := by
    unfold Sh_u
    have e : ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (μ j : ℂ) * Sh_a U μ t z j =
        ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) * ∑ j, (μ j : ℂ) * Sh_a U μ t z j := by push_cast; rfl
    rw [e, Complex.im_ofReal_mul, Complex.im_sum]
    simp only [Complex.im_ofReal_mul, Sh_a, Sh_im_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hs : |((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j * ‖Sh_a U μ t z j‖ ^ 2| ≤ 1 / 30 := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hn)]
    calc ((Fintype.card ι : ℝ))⁻¹ * |∑ j, μ j * ‖Sh_a U μ t z j‖ ^ 2|
        ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ _j : ι, (1 / 30 : ℝ) := by
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (sq_nonneg ‖Sh_a U μ t z j‖)]
          have := ha j
          have h2 : ‖Sh_a U μ t z j‖ ^ 2 ≤ (10 / 19) ^ 2 := by gcongr
          calc |μ j| * ‖Sh_a U μ t z j‖ ^ 2 ≤ 1 / 10 * (10 / 19) ^ 2 :=
                mul_le_mul (H.eig_le j) h2 (sq_nonneg _) (by norm_num)
            _ ≤ 1 / 30 := by norm_num
      _ = 1 / 30 := by simp
  rw [hu, abs_mul]
  have hw0 : 0 ≤ w.im := by rw [e]; linarith
  rw [abs_of_nonneg hw0]
  nlinarith [abs_nonneg (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j * ‖Sh_a U μ t z j‖ ^ 2)]

private lemma Sh_R_ratio {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : |t| ≤ 1) {z : ℂ} (hz : 0 < z.im) :
    (Sh_u U μ t z).im / (Sh_m U μ t z).im = Sh_R μ t (z + Sh_m U μ t z) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := Sh_basic H ht hz
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hu : (Sh_u U μ t z).im = (z + Sh_m U μ t z).im * (((Fintype.card ι : ℝ))⁻¹ *
      ∑ j, μ j * ‖Sh_a U μ t z j‖ ^ 2) := by
    unfold Sh_u
    have e : ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (μ j : ℂ) * Sh_a U μ t z j =
        ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) * ∑ j, (μ j : ℂ) * Sh_a U μ t z j := by push_cast; rfl
    rw [e, Complex.im_ofReal_mul, Complex.im_sum]
    simp only [Complex.im_ofReal_mul, Sh_a, Sh_im_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hw : 0 < (z + Sh_m U μ t z).im := by simp only [Complex.add_im]; linarith
  have hS : 0 < ∑ j, ‖Sh_a U μ t z j‖ ^ 2 := by
    have : 0 < ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Sh_a U μ t z j‖ ^ 2 := by
      have := b5; nlinarith
    exact pos_of_mul_pos_right this (inv_pos.2 hn).le
  rw [hu, b5, mul_div_mul_left _ _ hw.ne', mul_div_mul_left _ _ (inv_ne_zero hn.ne')]
  rfl

/-- At `t = 0`, `Δ̃_0 = z + m_sc + 1/m_sc = 0`. -/
private lemma Sh_D0 (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) {z : ℂ} (hz : 0 < z.im) :
    Sh_D U μ 0 z = 0 := by
  obtain ⟨h1, -, -, -, -, -, h7⟩ := rho_zero (ι := ι)
  have e : Sh_m U μ 0 z = msc z := by
    rw [← h1 z]
    simp only [Sh_m, Complex.ofReal_zero, zero_smul, mExt, hz, ite_true]
  obtain ⟨q, hq⟩ := h7 z hz
  have hm0 : msc z ≠ 0 := fun h0 => by rw [h0] at hq; simp at hq
  simp only [Sh_D, e]
  field_simp
  linear_combination q

end ShiftAux3

section ShiftAux4

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `Σ_j (tμ_j - w)⁻² ≠ 0`. -/
private lemma Sh_suma2_ne (μ : ι → ℝ) (t : ℝ) {w : ℂ} (hμ : ∀ j, |μ j| ≤ 1 / 10) (ht : |t| ≤ 1)
    (hw : 9 / 10 ≤ ‖w‖) : ∑ j, (((t * μ j : ℝ) : ℂ) - w)⁻¹ ^ 2 ≠ 0 := by
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
  have hx := fun j => Sh_abs_tmu hμ ht j
  have hre : ∀ j, 7 / 10 ≤ ((w * (((t * μ j : ℝ) : ℂ) - w)⁻¹) ^ 2).re := by
    intro j
    obtain ⟨hne, -, -⟩ := Sh_res_bd _ (hx j).2 hw
    obtain ⟨-, h2, -⟩ := Sh_nua_bd _ (hx j).2 hw
    rw [Sh_X_eq _ hne]
    set v := ((t * μ j : ℝ) : ℂ) * (((t * μ j : ℝ) : ℂ) - w)⁻¹
    have : ((-1 + v) ^ 2).re = 1 - 2 * v.re + (v ^ 2).re := by simp [sq]; ring
    rw [this]
    have h3 := Complex.re_le_norm v
    have h4 : |(v ^ 2).re| ≤ ‖v‖ ^ 2 := by rw [← norm_pow]; exact Complex.abs_re_le_norm _
    nlinarith [abs_le.1 h4, norm_nonneg v]
  intro h0
  have : ∑ j, (w * (((t * μ j : ℝ) : ℂ) - w)⁻¹) ^ 2 = 0 := by
    simp only [mul_pow, ← Finset.mul_sum, h0, mul_zero]
  have h1 := congrArg Complex.re this
  rw [Complex.re_sum, Complex.zero_re] at h1
  have : (0 : ℝ) < ∑ j, ((w * (((t * μ j : ℝ) : ℂ) - w)⁻¹) ^ 2).re :=
    Finset.sum_pos (fun j _ => by linarith [hre j]) Finset.univ_nonempty
  linarith

/-- The pointwise flow error behind (A.42) [derivative_estimate_modification_shift_eigenvalue]
and (A.52) [derivative_f_t_minus_gamma_k_t]: with `A = ⟨M²⟩`, `B = ⟨ΛM²⟩`, any real `g'`,
`|(g'A - B)/(1 - A) · (1 - m⁻²)| ≤ C²(1600/49)(1 + ⟨Λ²⟩/S)(8⟨Λ²⟩ Im w + |g' - R|)`, where
`S = √(κ + η)` and `R = ⟨MΛM^*⟩/⟨MM^*⟩`. -/
private lemma Sh_flow_pt {C : ℝ} (hC : 1 ≤ C)
    (hEB : ∀ (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ), Sh_Hyp U μ → ∀ t : ℝ, |t| ≤ 1 →
      ∀ z : ℂ, ‖z‖ ≤ 4 → 0 < z.im →
      z.re ∈ Set.Icc (Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))))
        (Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) →
      C⁻¹ * Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) ≤
          (Sh_m U μ t z).im ∧
        (Sh_m U μ t z).im ≤
          C * Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) ∧
        C⁻¹ * Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) ≤
          ‖1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2‖ ∧
        ‖1 - Sh_m U μ t z ^ 2‖ ≤
          C * (Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) +
            ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2))
    {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ} (ht : |t| ≤ 1)
    {z : ℂ} (hz4 : ‖z‖ ≤ 4) (hz : 0 < z.im)
    (hre : z.re ∈ Set.Icc (Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))))
        (Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))))) (g' : ℝ) :
    ‖((g' : ℂ) * (((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2) -
          ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (μ j : ℂ) * Sh_a U μ t z j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2) *
        (1 - 1 / Sh_m U μ t z ^ 2)‖ ≤
      C ^ 2 * (1600 / 49) * (1 + (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) /
          Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im)) *
        (8 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) * (z + Sh_m U μ t z).im +
          |g' - Sh_R μ t (z + Sh_m U μ t z)|) := by
  obtain ⟨e1, e2, e3, e4⟩ := hEB U μ H t ht z hz4 hz hre
  obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := Sh_basic H ht hz
  have hC0 : 0 < C := by linarith
  set S := Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im)
  set σ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2
  have hσ : 0 ≤ σ := by positivity
  set w := z + Sh_m U μ t z
  set m := Sh_m U μ t z
  set A := ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2
  set B := ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (μ j : ℂ) * Sh_a U μ t z j ^ 2
  have hκ0 : 0 ≤ kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re :=
    le_min (abs_nonneg _) (abs_nonneg _)
  have hSpos : 0 < S := Real.sqrt_pos.2 (by linarith)
  have hmlow : 7 / 40 ≤ ‖m‖ := (Sh_dz_bd H ht hz hz4).2
  have hm0 : m ≠ 0 := fun h0 => by rw [h0, norm_zero] at hmlow; linarith
  have hA1 : 0 < ‖1 - A‖ := lt_of_lt_of_le (by positivity) e3
  have hAle : ‖A‖ ≤ 1 := by
    refine le_trans ?_ b6.le
    simp only [A, norm_mul, norm_inv, Complex.norm_natCast]
    gcongr
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_pow]
  have hsne := Sh_suma2_ne μ t H.eig_le ht b3.le
  have hsne' : ∑ j, Sh_a U μ t z j ^ 2 ≠ 0 := hsne
  have hBA : B = A * Sh_S μ t w := by
    have hS_eq : Sh_S μ t w = (∑ j, (μ j : ℂ) * Sh_a U μ t z j ^ 2) / ∑ j, Sh_a U μ t z j ^ 2 :=
      rfl
    rw [hS_eq]
    simp only [A, B]
    rw [mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hsne']
  have hRS := Sh_RS μ t H.sum_zero H.eig_le ht b3.le
  have hwim : 0 < w.im := by simp only [w, Complex.add_im]; linarith
  rw [abs_of_pos hwim] at hRS
  have hnum : ‖(g' : ℂ) * A - B‖ ≤ 8 * σ * w.im + |g' - Sh_R μ t w| := by
    rw [hBA, show (g' : ℂ) * A - A * Sh_S μ t w = A * ((g' : ℂ) - Sh_S μ t w) by ring, norm_mul]
    have : ‖(g' : ℂ) - Sh_S μ t w‖ ≤ |g' - Sh_R μ t w| + 8 * σ * w.im := by
      have e : (g' : ℂ) - Sh_S μ t w = ((g' - Sh_R μ t w : ℝ) : ℂ) - (Sh_S μ t w - Sh_R μ t w) := by
        push_cast; ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith
    calc ‖A‖ * ‖(g' : ℂ) - Sh_S μ t w‖ ≤ 1 * (|g' - Sh_R μ t w| + 8 * σ * w.im) :=
          mul_le_mul hAle this (norm_nonneg _) zero_le_one
      _ = _ := by ring
  have hfac : ‖1 - 1 / m ^ 2‖ ≤ C * (S + σ) / (7 / 40) ^ 2 := by
    have e : 1 - 1 / m ^ 2 = -(1 - m ^ 2) / m ^ 2 := by field_simp; ring
    rw [e, norm_div, norm_neg, norm_pow]
    have hm2 : (7 / 40 : ℝ) ^ 2 ≤ ‖m‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hmlow 2
    calc ‖1 - m ^ 2‖ / ‖m‖ ^ 2 ≤ C * (S + σ) / ‖m‖ ^ 2 := by gcongr
      _ ≤ C * (S + σ) / (7 / 40) ^ 2 := by gcongr
  rw [norm_mul, norm_div]
  have hX : 0 ≤ 8 * σ * w.im + |g' - Sh_R μ t w| := by positivity
  calc ‖(g' : ℂ) * A - B‖ / ‖1 - A‖ * ‖1 - 1 / m ^ 2‖
      ≤ (8 * σ * w.im + |g' - Sh_R μ t w|) / (C⁻¹ * S) * (C * (S + σ) / (7 / 40) ^ 2) := by
        gcongr
    _ = C ^ 2 * (1600 / 49) * (1 + σ / S) * (8 * σ * w.im + |g' - Sh_R μ t w|) := by
        field_simp
        ring

end ShiftAux4

/-! ### The flow `t ↦ γ_k(t)` and the two shifts (Lemma A.3 [lemma_modification_of_shift]) -/

/-- The constant of `Sh_edge_bounds`. -/
private def Sh_CE : ℝ := Sh_edge_bounds.choose

private lemma Sh_CE_spec : 1 ≤ Sh_CE ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ), Sh_Hyp U μ → ∀ t : ℝ, |t| ≤ 1 →
      ∀ z : ℂ, ‖z‖ ≤ 4 → 0 < z.im →
      z.re ∈ Set.Icc (Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))))
        (Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) →
      Sh_CE⁻¹ * Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) ≤
          (Sh_m U μ t z).im ∧
        (Sh_m U μ t z).im ≤
          Sh_CE * Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) ∧
        Sh_CE⁻¹ * Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) ≤
          ‖1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t z j ^ 2‖ ∧
        ‖1 - Sh_m U μ t z ^ 2‖ ≤
          Sh_CE * (Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z.re + z.im) +
            ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) :=
  Sh_edge_bounds.choose_spec

/-- The constant of `Sh_vert`. -/
private def Sh_KV : ℝ := Sh_vert.choose

private lemma Sh_KV_spec : 1 ≤ Sh_KV ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ), Sh_Hyp U μ → ∀ t : ℝ, |t| ≤ 1 →
      ∀ x : ℝ, |x| ≤ 3 →
      x ∈ Set.Icc (Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))))
        (Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) →
      ∀ h η : ℝ, 0 < h → h ≤ η → η ≤ 1 →
      ‖Sh_m U μ t ((x : ℂ) + (η : ℂ) * Complex.I) - Sh_m U μ t ((x : ℂ) + (h : ℂ) * Complex.I)‖ ≤
          Sh_KV * Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) x + η) ∧
        ‖Sh_D U μ t ((x : ℂ) + (η : ℂ) * Complex.I) - Sh_D U μ t ((x : ℂ) + (h : ℂ) * Complex.I)‖ ≤
          Sh_KV * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) *
            Real.sqrt (kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) x + η) :=
  Sh_vert.choose_spec

/-- The constant of (A.1) [square_root_density] at `τ = 1/4`. -/
private def Sh_CS : ℝ := (square_root_density (1 / 4) (by norm_num)).choose

private lemma Sh_CS_spec : 0 < Sh_CS ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (Λ : Matrix ι ι ℂ), Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      (∀ x ∈ Set.Icc (Eminus Λ) (Eplus Λ),
        Sh_CS⁻¹ * Real.sqrt ((Eplus Λ - x) * (x - Eminus Λ)) ≤ rho Λ x ∧
          rho Λ x ≤ Sh_CS * Real.sqrt ((Eplus Λ - x) * (x - Eminus Λ))) ∧
      ∀ z : ℂ, ‖z‖ ≤ (1 / 4 : ℝ)⁻¹ → 0 < z.im →
        (z.re ∈ Set.Icc (Eminus Λ) (Eplus Λ) →
          Sh_CS⁻¹ * Real.sqrt (kappa Λ z.re + z.im) ≤ (mSol Λ z).im ∧
            (mSol Λ z).im ≤ Sh_CS * Real.sqrt (kappa Λ z.re + z.im)) ∧
        (z.re ∉ Set.Icc (Eminus Λ) (Eplus Λ) →
          Sh_CS⁻¹ * (z.im / Real.sqrt (kappa Λ z.re + z.im)) ≤ (mSol Λ z).im ∧
            (mSol Λ z).im ≤ Sh_CS * (z.im / Real.sqrt (kappa Λ z.re + z.im))) :=
  (square_root_density (1 / 4) (by norm_num)).choose_spec

section ShiftMain

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The hypotheses on the flow used below: the edges of `ρ_t` lie in `(-3, 3)`, the quantile
`γ_k(t)` is at distance `≥ κ₀` from both edges, and `κ_t(γ_k(t)) ≤ K₁ κ₀`, for `t ∈ [0, 1]`. -/
private structure Sh_Q (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (Mc k : ℕ) (κ₀ K₁ : ℝ) : Prop where
  k1 : 1 ≤ k
  kM : k ≤ Mc
  κpos : 0 < κ₀
  edges : ∀ t ∈ Set.Icc (0 : ℝ) 1, -3 < Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) ∧
    Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) < 3
  bulk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) + κ₀ ≤
      quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k ∧
    quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k + κ₀ ≤
      Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))
  kup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))
      (quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k) ≤ K₁ * κ₀

private lemma Sh_abs01 {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : |t| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [ht.1, ht.2]

/-- Choice of the height `h`: the regularized quantile exists and is `δ`-close to `γ_k(t)` for
every `t ∈ [0, 1]`. -/
private lemma Sh_setup {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {Mc k : ℕ}
    {κ₀ K₁ : ℝ} (Q : Sh_Q U μ Mc k κ₀ K₁) {δ h : ℝ} (hδ : 0 < δ) (hδκ : δ ≤ κ₀ / 2)
    (hh : 0 < h) (hh1 : h ≤ 1 - ((k : ℝ) - 1 / 2) / Mc)
    (hsmall : 2 * h / Real.pi < Sh_CS⁻¹ * (κ₀ / 2) * δ) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ((k : ℝ) - 1 / 2) / Mc ≤ Sh_F U μ h t (-3)) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |Sh_gh U μ (((k : ℝ) - 1 / 2) / Mc) h t -
        quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k| < δ := by
  have hπ : 2 / Real.pi < 1 := by
    rw [div_lt_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have hc0 : 0 < ((k : ℝ) - 1 / 2) / Mc := by
    have hM : (0 : ℝ) < Mc := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (Q.k1.trans Q.kM))
    have : (1 : ℝ) ≤ k := by exact_mod_cast Q.k1
    exact div_pos (by linarith) hM
  have h3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((k : ℝ) - 1 / 2) / Mc ≤ Sh_F U μ h t (-3) := by
    intro t ht
    have hN := (Sh_quant H (Sh_abs01 ht) (Q.edges t ht) Q.k1 Q.kM).2.1
    have hF := Sh_F_N H hh (Sh_abs01 ht) (-3)
    rw [hN] at hF
    have : 2 * h / Real.pi ≤ h := by
      rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
    have := (abs_le.1 hF).1
    linarith
  refine ⟨h3, fun t ht => ?_⟩
  have hroot := (Sh_gh_root H hc0 hh (Sh_abs01 ht) (h3 t ht)).1
  obtain ⟨hb1, hb2⟩ := Q.bulk t ht
  obtain ⟨hH, hn⟩ := Sh_tΛ H (Sh_abs01 ht)
  obtain ⟨hCS, hCS'⟩ := Sh_CS_spec
  have hρ := (hCS' ι _ hH hn).1
  refine Sh_gh_close H hh (Sh_abs01 ht) (Q.edges t ht) Q.k1 Q.kM hδ (ρ₀ := Sh_CS⁻¹ * (κ₀ / 2))
    (fun y hy => ?_) hsmall hroot
  have hy1 : Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) + κ₀ / 2 ≤ y := by linarith [hy.1]
  have hy2 : y + κ₀ / 2 ≤ Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) := by linarith [hy.2]
  have hk := Q.κpos
  obtain ⟨r1, -⟩ := hρ y ⟨by linarith, by linarith⟩
  refine le_trans ?_ r1
  gcongr
  rw [Real.le_sqrt (by positivity) (by nlinarith)]
  nlinarith

end ShiftMain

section ShiftMain2

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `t ↦ γ_k(t)` is continuous on `[0, 1]` (Definition 2.10 [def_moving_Lambda]). -/
private lemma Sh_quant_cont {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ)
    {Mc k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ Mc) :
    ContinuousOn (fun t : ℝ => quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k)
      (Set.Icc 0 1) := by
  set Λ := Sh_cd U (fun j => (μ j : ℂ))
  have hΛ : Λ.IsHermitian := Sh_cd_herm U μ
  set cl : ℝ → ℝ := fun t => max (-1) (min 1 t) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hcl1 : ∀ t, |cl t| ≤ 1 := fun t => by
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  have hmc := moving_continuous (fun t => ((cl t : ℝ) : ℂ) • Λ)
    ((Complex.continuous_ofReal.comp hclc).smul continuous_const)
    (fun t => Sh_herm_smul hΛ _)
    (fun t => by
      rw [Sh_opNorm_smul]
      calc |cl t| * opNorm Λ ≤ 1 * (1 / 10) := mul_le_mul (hcl1 t) H.norm_le (norm_nonneg _)
            zero_le_one
        _ = 1 / 10 := by ring)
  refine (hmc.2.2.1 Mc k hk hkM).continuousOn.congr fun t ht => ?_
  have : cl t = t := by
    simp only [hcl]; rw [min_eq_right ht.2, max_eq_right (by linarith [ht.1])]
  simp only [this]

/-- Continuity of `t ↦ ⟨M_t Λ M_t^*⟩/⟨M_t M_t^*⟩` along a continuous path in the upper half
plane. -/
private lemma Sh_R_cont {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hfi : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (f t).im) :
    ContinuousOn (fun t => Sh_R μ t (f t + Sh_m U μ t (f t))) (Set.Icc 0 1) := by
  have hq : ContinuousOn (fun t : ℝ => ((t, f t) : ℝ × ℂ)) (Set.Icc 0 1) :=
    continuousOn_id.prodMk hf
  have hmaps : Set.MapsTo (fun t : ℝ => ((t, f t) : ℝ × ℂ)) (Set.Icc 0 1)
      {q | |q.1| ≤ 1 ∧ 0 < q.2.im} := fun t ht => ⟨Sh_abs01 ht, hfi t ht⟩
  have ha : ∀ j, ContinuousOn (fun t => Sh_a U μ t (f t) j) (Set.Icc 0 1) := fun j => by
    have := ContinuousOn.comp (g := fun q : ℝ × ℂ => Sh_a U μ q.1 q.2 j)
      (f := fun t : ℝ => ((t, f t) : ℝ × ℂ)) (Sh_a_cont H j) hq hmaps
    exact this
  have hnum : ContinuousOn (fun t => ∑ j, μ j * ‖Sh_a U μ t (f t) j‖ ^ 2) (Set.Icc 0 1) :=
    continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ((ha j).norm.pow 2)
  have hden : ContinuousOn (fun t => ∑ j, ‖Sh_a U μ t (f t) j‖ ^ 2) (Set.Icc 0 1) :=
    continuousOn_finsetSum _ fun j _ => (ha j).norm.pow 2
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∑ j, ‖Sh_a U μ t (f t) j‖ ^ 2 ≠ 0 := by
    intro t ht h0
    obtain ⟨b1, -, -, -, b5, -⟩ := Sh_basic H (Sh_abs01 ht) (hfi t ht)
    rw [h0, mul_zero, mul_zero] at b5
    linarith
  have key := hnum.div hden hne
  refine key.congr fun t _ => ?_
  rfl

/-- `γ^h(1) - γ^h(0) = ∫₀¹ (Im u_t(z_t) - Im u_t(3 + ih)) / Im m_t(z_t) dt`, `z_t = γ^h(t) + ih`. -/
private lemma Sh_gh_ftc {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {c h : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hh1 : h ≤ 1)
    (h3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ Sh_F U μ h t (-3)) :
    IntervalIntegrable (fun t => ((Sh_u U μ t ((Sh_gh U μ c h t : ℂ) + (h : ℂ) * Complex.I)).im -
          (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) /
        (Sh_m U μ t ((Sh_gh U μ c h t : ℂ) + (h : ℂ) * Complex.I)).im) MeasureTheory.volume 0 1 ∧
    Sh_gh U μ c h 1 - Sh_gh U μ c h 0 = ∫ t in (0 : ℝ)..1,
      ((Sh_u U μ t ((Sh_gh U μ c h t : ℂ) + (h : ℂ) * Complex.I)).im -
          (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) /
        (Sh_m U μ t ((Sh_gh U μ c h t : ℂ) + (h : ℂ) * Complex.I)).im := by
  have hg := Sh_gh_contOn H hc hh hh1 h3
  have hp : ContinuousOn (fun t : ℝ => (Sh_gh U μ c h t : ℂ) + (h : ℂ) * Complex.I)
      (Set.Icc 0 1) := (Complex.continuous_ofReal.comp_continuousOn hg).add continuousOn_const
  have hq : ContinuousOn (fun t : ℝ => ((t, (Sh_gh U μ c h t : ℂ) + (h : ℂ) * Complex.I) :
      ℝ × ℂ)) (Set.Icc 0 1) := continuousOn_id.prodMk hp
  have hmaps : Set.MapsTo (fun t : ℝ => ((t, (Sh_gh U μ c h t : ℂ) + (h : ℂ) * Complex.I) :
      ℝ × ℂ)) (Set.Icc 0 1) {q | |q.1| ≤ 1 ∧ 0 < q.2.im} := fun t ht =>
    ⟨Sh_abs01 ht, Sh_im_hpath hh _⟩
  have hmaps3 : Set.MapsTo (fun t : ℝ => ((t, ((3 : ℝ) : ℂ) + (h : ℂ) * Complex.I) : ℝ × ℂ))
      (Set.Icc 0 1) {q | |q.1| ≤ 1 ∧ 0 < q.2.im} := fun t ht =>
    ⟨Sh_abs01 ht, Sh_im_hpath hh _⟩
  have c1 := (Sh_u_cont H).comp hq hmaps
  have c2 := (Sh_u_cont H).comp (continuousOn_id.prodMk continuousOn_const) hmaps3
  have c3 := (Sh_joint H).comp hq hmaps
  have hcont : ContinuousOn (fun t => ((Sh_u U μ t ((Sh_gh U μ c h t : ℂ) + (h : ℂ) * Complex.I)).im -
          (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) /
        (Sh_m U μ t ((Sh_gh U μ c h t : ℂ) + (h : ℂ) * Complex.I)).im) (Set.Icc 0 1) := by
    refine ((Complex.continuous_im.comp_continuousOn c1).sub
      (Complex.continuous_im.comp_continuousOn c2)).div
      (Complex.continuous_im.comp_continuousOn c3) fun t ht => ?_
    exact (Sh_basic H (Sh_abs01 ht) (Sh_im_hpath hh _)).1.ne'
  refine ⟨hcont.intervalIntegrable_of_Icc zero_le_one, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hg
    (fun t ht => Sh_gh_deriv H hc hh hh1 h3 ht) (hcont.intervalIntegrable_of_Icc zero_le_one)]

end ShiftMain2

section ShiftMain3

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Location facts near the quantile: for `|x - γ| < δ ≤ κ₀/2` with `γ` at distance `≥ κ₀` from
both edges, `x ∈ [E⁻, E⁺]`, `|x| ≤ 3`, `κ₀/2 ≤ κ(x) ≤ κ(γ) + κ₀/2`. -/
private lemma Sh_near {Em Ep γ x δ κ₀ : ℝ} (hE : -3 < Em ∧ Ep < 3) (hγ : Em + κ₀ ≤ γ ∧ γ + κ₀ ≤ Ep)
    (hκ₀ : 0 < κ₀) (hx : |x - γ| < δ) (hδ : δ ≤ κ₀ / 2) :
    x ∈ Set.Icc Em Ep ∧ |x| ≤ 3 ∧ |γ| ≤ 3 ∧ κ₀ / 2 ≤ min |Ep - x| |x - Em| ∧
      min |Ep - x| |x - Em| ≤ min |Ep - γ| |γ - Em| + κ₀ / 2 := by
  rw [abs_lt] at hx
  refine ⟨⟨by linarith, by linarith⟩, by rw [abs_le]; constructor <;> linarith,
    by rw [abs_le]; constructor <;> linarith, ?_, ?_⟩
  · rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    exact le_min (by linarith) (by linarith)
  · rw [abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith),
      abs_of_pos (by linarith), ← min_add_add_right]
    exact min_le_min (by linarith) (by linarith)

private lemma Sh_sqrt_mono {a b : ℝ} (K : ℝ) (hK : 1 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {c : ℝ} (hc : c ≤ K * a) (hc0 : 0 ≤ c) :
    Real.sqrt (c + b) ≤ Real.sqrt K * Real.sqrt (a + b) := by
  rw [← Real.sqrt_mul (by linarith)]
  exact Real.sqrt_le_sqrt (by nlinarith)

private lemma Sh_eta_le_sqrt {κ η : ℝ} (hκ : 0 ≤ κ) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    η ≤ Real.sqrt (κ + η) := by
  rw [Real.le_sqrt hη (by linarith)]; nlinarith

/-- The pointwise comparison behind (A.36) [estimate_change_definition_of_shift_eigenvalue]:
`Δ(t)` against the derivative of the regularized quantile. -/
private lemma Sh_pt3 {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {γ x h η δ κ₀ K₁ : ℝ}
    (hE : -3 < Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) ∧
      Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) < 3)
    (hγ : Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) + κ₀ ≤ γ ∧
      γ + κ₀ ≤ Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))))
    (hκγ : kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) γ ≤ K₁ * κ₀) (hK₁ : 0 ≤ K₁)
    (hκ₀ : 0 < κ₀) (hx : |x - γ| < δ) (hδ : δ ≤ κ₀ / 2) (hh : 0 < h) (hhη : h ≤ η)
    (hη1 : η ≤ 1) :
    |Sh_R μ t ((γ : ℂ) + (η : ℂ) * Complex.I + Sh_m U μ t ((γ : ℂ) + (η : ℂ) * Complex.I)) -
        ((Sh_u U μ t ((x : ℂ) + (h : ℂ) * Complex.I)).im -
          (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) /
        (Sh_m U μ t ((x : ℂ) + (h : ℂ) * Complex.I)).im| ≤
      10 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) * (1 + 1 / η) * δ +
        10 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) *
          (1 + Sh_KV * Real.sqrt (K₁ + 1)) * Real.sqrt (κ₀ + η) +
        Sh_CE * h / (15 * Real.sqrt (κ₀ / 2)) := by
  have ht1 := Sh_abs01 ht
  have hη : 0 < η := lt_of_lt_of_le hh hhη
  obtain ⟨hxE, hx3, hγ3, hκlo, hκhi⟩ := Sh_near hE hγ hκ₀ hx hδ
  set Λt := (t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))
  have hκx : kappa Λt x = min |Eplus Λt - x| |x - Eminus Λt| := rfl
  have hκγ' : kappa Λt γ = min |Eplus Λt - γ| |γ - Eminus Λt| := rfl
  rw [← hκx] at hκlo hκhi
  rw [← hκγ'] at hκhi
  set σ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2
  have hσ : 0 ≤ σ := by positivity
  set zγ : ℂ := (γ : ℂ) + (η : ℂ) * Complex.I
  set zxη : ℂ := (x : ℂ) + (η : ℂ) * Complex.I
  set zx : ℂ := (x : ℂ) + (h : ℂ) * Complex.I
  have hzγ : 0 < zγ.im := Sh_im_hpath hη γ
  have hzxη : 0 < zxη.im := Sh_im_hpath hη x
  have hzx : 0 < zx.im := Sh_im_hpath hh x
  obtain ⟨-, -, wγ, -⟩ := Sh_basic H ht1 hzγ
  obtain ⟨-, -, wxη, -⟩ := Sh_basic H ht1 hzxη
  obtain ⟨mx1, -, wx, -⟩ := Sh_basic H ht1 hzx
  -- the derivative of the regularized quantile
  have hratio := Sh_R_ratio H ht1 hzx
  have hgd : ((Sh_u U μ t zx).im - (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) /
      (Sh_m U μ t zx).im = Sh_R μ t (zx + Sh_m U μ t zx) -
        (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im / (Sh_m U μ t zx).im := by
    rw [sub_div, hratio]
  rw [hgd]
  -- three terms
  have T1 : |Sh_R μ t (zγ + Sh_m U μ t zγ) - Sh_R μ t (zxη + Sh_m U μ t zxη)| ≤
      10 * σ * (1 + 1 / η) * δ := by
    refine (Sh_R_lip μ t H.sum_zero H.eig_le ht1 wγ.le wxη.le).trans ?_
    have hm := (Sh_horiz H ht1 hη hη1 hγ3 hx3).1
    have e : zγ + Sh_m U μ t zγ - (zxη + Sh_m U μ t zxη) =
        ((γ - x : ℝ) : ℂ) + (Sh_m U μ t zγ - Sh_m U μ t zxη) := by
      simp only [zγ, zxη]; push_cast; ring
    have : ‖zγ + Sh_m U μ t zγ - (zxη + Sh_m U μ t zxη)‖ ≤ δ + δ / η := by
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 : |γ - x| ≤ δ := by rw [abs_sub_comm]; exact hx.le
      have h2 : |γ - x| / η ≤ δ / η := by gcongr
      linarith
    calc 10 * σ * ‖zγ + Sh_m U μ t zγ - (zxη + Sh_m U μ t zxη)‖ ≤ 10 * σ * (δ + δ / η) := by
          gcongr
      _ = 10 * σ * (1 + 1 / η) * δ := by ring
  have T2 : |Sh_R μ t (zxη + Sh_m U μ t zxη) - Sh_R μ t (zx + Sh_m U μ t zx)| ≤
      10 * σ * (1 + Sh_KV * Real.sqrt (K₁ + 1)) * Real.sqrt (κ₀ + η) := by
    refine (Sh_R_lip μ t H.sum_zero H.eig_le ht1 wxη.le wx.le).trans ?_
    obtain ⟨hKV1, hKV⟩ := Sh_KV_spec
    have hv := (hKV ι U μ H t ht1 x hx3 hxE h η hh hhη hη1).1
    have e : zxη + Sh_m U μ t zxη - (zx + Sh_m U μ t zx) =
        ((η - h : ℝ) : ℂ) * Complex.I + (Sh_m U μ t zxη - Sh_m U μ t zx) := by
      simp only [zxη, zx]; push_cast; ring
    have hk0 : 0 ≤ kappa Λt x := le_min (abs_nonneg _) (abs_nonneg _)
    have hsq : Real.sqrt (kappa Λt x + η) ≤ Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η) :=
      Sh_sqrt_mono (K₁ + 1) (by linarith) hκ₀.le hη.le (by nlinarith) hk0
    have heta := Sh_eta_le_sqrt hκ₀.le hη.le hη1
    have : ‖zxη + Sh_m U μ t zxη - (zx + Sh_m U μ t zx)‖ ≤
        (1 + Sh_KV * Real.sqrt (K₁ + 1)) * Real.sqrt (κ₀ + η) := by
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
        abs_of_nonneg (by linarith)]
      have : Sh_KV * Real.sqrt (kappa Λt x + η) ≤
          Sh_KV * (Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η)) := by gcongr
      nlinarith
    calc 10 * σ * ‖zxη + Sh_m U μ t zxη - (zx + Sh_m U μ t zx)‖
        ≤ 10 * σ * ((1 + Sh_KV * Real.sqrt (K₁ + 1)) * Real.sqrt (κ₀ + η)) := by gcongr
      _ = _ := by ring
  have T3 : |(Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im / (Sh_m U μ t zx).im| ≤
      Sh_CE * h / (15 * Real.sqrt (κ₀ / 2)) := by
    obtain ⟨hCE1, hCE⟩ := Sh_CE_spec
    have hzx4 : ‖zx‖ ≤ 4 := by
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      rw [abs_of_pos hh]; linarith [hhη, hη1]
    have hre : zx.re = x := by simp [zx]
    have him : zx.im = h := by simp [zx]
    have e1 := (hCE ι U μ H t ht1 zx hzx4 hzx (by rw [hre]; exact hxE)).1
    rw [hre, him] at e1
    have hu := Sh_u3 H ht1 hh
    have hs1 : Real.sqrt (κ₀ / 2) ≤ Real.sqrt (kappa Λt x + h) :=
      Real.sqrt_le_sqrt (by linarith)
    have hs0 : 0 < Real.sqrt (κ₀ / 2) := Real.sqrt_pos.2 (by linarith)
    have hlow : Sh_CE⁻¹ * Real.sqrt (κ₀ / 2) ≤ (Sh_m U μ t zx).im :=
      le_trans (mul_le_mul_of_nonneg_left hs1 (inv_nonneg.2 (by linarith))) e1
    have hpos : 0 < Sh_CE⁻¹ * Real.sqrt (κ₀ / 2) := mul_pos (inv_pos.2 (by linarith)) hs0
    rw [abs_div, abs_of_pos (lt_of_lt_of_le hpos hlow), div_le_iff₀ (lt_of_lt_of_le hpos hlow)]
    calc |(Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im| ≤ h / 15 := hu
      _ = Sh_CE * h / (15 * Real.sqrt (κ₀ / 2)) * (Sh_CE⁻¹ * Real.sqrt (κ₀ / 2)) := by
          field_simp
      _ ≤ _ := by gcongr
  calc |Sh_R μ t (zγ + Sh_m U μ t zγ) - (Sh_R μ t (zx + Sh_m U μ t zx) -
        (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im / (Sh_m U μ t zx).im)|
      ≤ |Sh_R μ t (zγ + Sh_m U μ t zγ) - Sh_R μ t (zxη + Sh_m U μ t zxη)| +
        |Sh_R μ t (zxη + Sh_m U μ t zxη) - Sh_R μ t (zx + Sh_m U μ t zx)| +
        |(Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im / (Sh_m U μ t zx).im| := by
        have := abs_add_three (Sh_R μ t (zγ + Sh_m U μ t zγ) - Sh_R μ t (zxη + Sh_m U μ t zxη))
          (Sh_R μ t (zxη + Sh_m U μ t zxη) - Sh_R μ t (zx + Sh_m U μ t zx))
          ((Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im / (Sh_m U μ t zx).im)
        convert this using 2; ring
    _ ≤ _ := by linarith

end ShiftMain3

section ShiftMain4

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Sh_c_bounds {Mc k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ Mc) :
    0 < ((k : ℝ) - 1 / 2) / Mc ∧ ((k : ℝ) - 1 / 2) / Mc < 1 := by
  have hM : (0 : ℝ) < Mc := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hk.trans hkM))
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (k : ℝ) ≤ Mc := by exact_mod_cast hkM
  exact ⟨div_pos (by linarith) hM, by rw [div_lt_one hM]; linarith⟩

/-- (A.35) [modification_shift_eigenvalue] in general form: `|∫₀¹ Δ(t) dt - (γ_k(1) - γ_k(0))|
≤ 10 ⟨Λ²⟩ (1 + K √(K₁ + 1)) √(κ₀ + η)`, for `0 < η ≤ 1`. -/
private lemma Sh_T3 {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {Mc k : ℕ}
    {κ₀ K₁ : ℝ} (Q : Sh_Q U μ Mc k κ₀ K₁) (hK₁ : 0 ≤ K₁) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    |(∫ t in (0 : ℝ)..1, Sh_R μ t
        ((quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k : ℂ) + (η : ℂ) * Complex.I +
          Sh_m U μ t ((quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k : ℂ) +
            (η : ℂ) * Complex.I))) -
      (quant (rho (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k -
        quant (rho (((0 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k)| ≤
      10 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) * (1 + Sh_KV * Real.sqrt (K₁ + 1)) *
        Real.sqrt (κ₀ + η) := by
  set γ : ℝ → ℝ := fun t => quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k with hγdef
  set σ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2
  have hσ : 0 ≤ σ := by positivity
  obtain ⟨hc0, hc1⟩ := Sh_c_bounds Q.k1 Q.kM
  set c := ((k : ℝ) - 1 / 2) / Mc
  have hκ₀ := Q.κpos
  obtain ⟨hCS, -⟩ := Sh_CS_spec
  obtain ⟨hCE, -⟩ := Sh_CE_spec
  apply le_of_forall_pos_le_add
  intro ε hε
  set L := 10 * σ * (1 + 1 / η) + 2
  have hL : 0 < L := by positivity
  set δ := min (κ₀ / 2) (ε / (2 * L))
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  have hδκ : δ ≤ κ₀ / 2 := min_le_left _ _
  have hδε : L * δ ≤ ε / 2 := by
    have := min_le_right (κ₀ / 2) (ε / (2 * L))
    calc L * δ ≤ L * (ε / (2 * L)) := by gcongr
      _ = ε / 2 := by field_simp
  set a := Sh_CE / (15 * Real.sqrt (κ₀ / 2))
  have ha : 0 ≤ a := by positivity
  set ρ₀ := Sh_CS⁻¹ * (κ₀ / 2)
  have hρ₀ : 0 < ρ₀ := by positivity
  set h := min (min ((1 - c) / 2) η) (min (Real.pi * ρ₀ * δ / 4) (ε / (2 * (a + 1))))
  have hh : 0 < h := lt_min (lt_min (by linarith) hη) (lt_min (by positivity) (by positivity))
  have hh1c : h ≤ 1 - c := by
    have : h ≤ (1 - c) / 2 := (min_le_left (min ((1 - c) / 2) η) _).trans (min_le_left _ _)
    linarith
  have hhη : h ≤ η := (min_le_left _ _).trans (min_le_right _ _)
  have hh1 : h ≤ 1 := hhη.trans hη1
  have hsmall : 2 * h / Real.pi < ρ₀ * δ := by
    have : h ≤ Real.pi * ρ₀ * δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [Real.pi_pos, mul_pos hρ₀ hδ]
  have hah : a * h ≤ ε / 2 := by
    have : h ≤ ε / (2 * (a + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    calc a * h ≤ (a + 1) * h := by nlinarith
      _ ≤ (a + 1) * (ε / (2 * (a + 1))) := by gcongr
      _ = ε / 2 := by field_simp
  obtain ⟨h3, hclose⟩ := Sh_setup H Q hδ hδκ hh hh1c hsmall
  obtain ⟨hgint, hftc⟩ := Sh_gh_ftc H hc0 hh hh1 h3
  -- integrability of `Δ`
  have hγc := Sh_quant_cont H (Mc := Mc) (k := k) Q.k1 Q.kM
  have hpath : ContinuousOn (fun t : ℝ => (γ t : ℂ) + (η : ℂ) * Complex.I) (Set.Icc 0 1) :=
    (Complex.continuous_ofReal.comp_continuousOn hγc).add continuousOn_const
  have hΔint : IntervalIntegrable (fun t => Sh_R μ t ((γ t : ℂ) + (η : ℂ) * Complex.I +
      Sh_m U μ t ((γ t : ℂ) + (η : ℂ) * Complex.I))) MeasureTheory.volume 0 1 :=
    (Sh_R_cont H hpath fun t _ => Sh_im_hpath hη (γ t)).intervalIntegrable_of_Icc zero_le_one
  -- pointwise bound
  have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖Sh_R μ t ((γ t : ℂ) + (η : ℂ) * Complex.I + Sh_m U μ t ((γ t : ℂ) + (η : ℂ) * Complex.I)) -
        ((Sh_u U μ t ((Sh_gh U μ c h t : ℂ) + (h : ℂ) * Complex.I)).im -
          (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) /
        (Sh_m U μ t ((Sh_gh U μ c h t : ℂ) + (h : ℂ) * Complex.I)).im‖ ≤
      10 * σ * (1 + 1 / η) * δ + 10 * σ * (1 + Sh_KV * Real.sqrt (K₁ + 1)) * Real.sqrt (κ₀ + η) +
        a * h := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs]
    have := Sh_pt3 H ht' (Q.edges t ht') (Q.bulk t ht') (Q.kup t ht') hK₁ hκ₀
      (hclose t ht') hδκ hh hhη hη1
    refine this.trans (le_of_eq ?_)
    simp only [a]
    ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [intervalIntegral.integral_sub hΔint hgint, ← hftc] at hint
  rw [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at hint
  have c1 := hclose 1 ⟨zero_le_one, le_refl _⟩
  have c0 := hclose 0 ⟨le_refl _, zero_le_one⟩
  have e1 : (γ 1) = quant (rho (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k := rfl
  have e0 : (γ 0) = quant (rho (((0 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k := rfl
  rw [← e1, ← e0]
  have hLδ : 10 * σ * (1 + 1 / η) * δ + 2 * δ = L * δ := by simp only [L]; ring
  calc |(∫ t in (0 : ℝ)..1, Sh_R μ t ((γ t : ℂ) + (η : ℂ) * Complex.I +
        Sh_m U μ t ((γ t : ℂ) + (η : ℂ) * Complex.I))) - (γ 1 - γ 0)|
      ≤ |(∫ t in (0 : ℝ)..1, Sh_R μ t ((γ t : ℂ) + (η : ℂ) * Complex.I +
          Sh_m U μ t ((γ t : ℂ) + (η : ℂ) * Complex.I))) -
          (Sh_gh U μ c h 1 - Sh_gh U μ c h 0)| +
        |Sh_gh U μ c h 1 - γ 1| + |Sh_gh U μ c h 0 - γ 0| := by
        have := abs_add_three ((∫ t in (0 : ℝ)..1, Sh_R μ t ((γ t : ℂ) + (η : ℂ) * Complex.I +
          Sh_m U μ t ((γ t : ℂ) + (η : ℂ) * Complex.I))) - (Sh_gh U μ c h 1 - Sh_gh U μ c h 0))
          (Sh_gh U μ c h 1 - γ 1) (-(Sh_gh U μ c h 0 - γ 0))
        rw [abs_neg] at this
        convert this using 2; ring
    _ ≤ (10 * σ * (1 + 1 / η) * δ + 10 * σ * (1 + Sh_KV * Real.sqrt (K₁ + 1)) *
          Real.sqrt (κ₀ + η) + a * h) + δ + δ := by
        gcongr
    _ ≤ 10 * σ * (1 + Sh_KV * Real.sqrt (K₁ + 1)) * Real.sqrt (κ₀ + η) + ε := by
        linarith

end ShiftMain4

section ShiftMain5

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `d/dt Δ̃_t(p(t)) = p' + m'(1 - m⁻²)` with `m' = (p'A - B)/(1 - A)`, the computation (A.52)
[derivative_f_t_minus_gamma_k_t]. -/
private lemma Sh_D_path {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ)
    {p : ℝ → ℂ} {p' : ℂ} {s₀ : ℝ} (hs : |s₀| < 1) (hp : HasDerivAt p p' s₀)
    (hz : 0 < (p s₀).im) :
    HasDerivAt (fun s => Sh_D U μ s (p s))
      (p' + (p' * (((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ s₀ (p s₀) j ^ 2) -
          ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (μ j : ℂ) * Sh_a U μ s₀ (p s₀) j ^ 2) /
        (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ s₀ (p s₀) j ^ 2) *
        (1 - 1 / Sh_m U μ s₀ (p s₀) ^ 2)) s₀ := by
  have hm := Sh_dm_path H hs hp hz
  have hm0 : Sh_m U μ s₀ (p s₀) ≠ 0 := fun h0 => by
    have := (Sh_basic H hs.le hz).1; rw [h0, Complex.zero_im] at this; linarith
  have := (hp.add hm).add (hm.inv hm0)
  refine this.congr_deriv ?_
  field_simp
  ring

/-- The pointwise bound on `d/dt (Re Δ̃_t(z_t) - γ^h(t))`. -/
private lemma Sh_pt2 {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {γ x h η δ κ₀ K₁ K₂ : ℝ}
    (hE : -3 < Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) ∧
      Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) < 3)
    (hγ : Eminus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) + κ₀ ≤ γ ∧
      γ + κ₀ ≤ Eplus ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))))
    (hκγ : kappa ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) γ ≤ K₁ * κ₀) (hK₁ : 0 ≤ K₁)
    (hK₂ : 0 ≤ K₂) (hσ : ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 ≤ K₂ * Real.sqrt κ₀)
    (hκ₀ : 0 < κ₀) (hx : |x - γ| < δ) (hδ : δ ≤ κ₀ / 2) (hh : 0 < h) (hhη : h ≤ η)
    (hη1 : η ≤ 1) :
    ‖(((((Sh_u U μ t ((x : ℂ) + (h : ℂ) * Complex.I)).im -
          (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) /
        (Sh_m U μ t ((x : ℂ) + (h : ℂ) * Complex.I)).im : ℝ) : ℂ) *
          (((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((x : ℂ) + (h : ℂ) * Complex.I) j ^ 2) -
        ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (μ j : ℂ) * Sh_a U μ t ((x : ℂ) + (h : ℂ) * Complex.I) j ^ 2) /
      (1 - ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Sh_a U μ t ((x : ℂ) + (h : ℂ) * Complex.I) j ^ 2) *
      (1 - 1 / Sh_m U μ t ((x : ℂ) + (h : ℂ) * Complex.I) ^ 2)‖ ≤
      Sh_CE ^ 2 * (1600 / 49) * (1 + Real.sqrt 2 * K₂) *
        (8 * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) *
          (h + Sh_CE * Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η)) +
          Sh_CE * h / (15 * Real.sqrt (κ₀ / 2))) := by
  have ht1 := Sh_abs01 ht
  have hη : 0 < η := lt_of_lt_of_le hh hhη
  obtain ⟨hxE, hx3, hγ3, hκlo, hκhi⟩ := Sh_near hE hγ hκ₀ hx hδ
  set Λt := (t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))
  have hκx : kappa Λt x = min |Eplus Λt - x| |x - Eminus Λt| := rfl
  have hκγ' : kappa Λt γ = min |Eplus Λt - γ| |γ - Eminus Λt| := rfl
  rw [← hκx] at hκlo hκhi
  rw [← hκγ'] at hκhi
  set σ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2
  have hσ0 : 0 ≤ σ := by positivity
  set zx : ℂ := (x : ℂ) + (h : ℂ) * Complex.I
  have hzx : 0 < zx.im := Sh_im_hpath hh x
  have hzx4 : ‖zx‖ ≤ 4 := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    rw [abs_of_pos hh]; linarith [hhη, hη1]
  have hre : zx.re = x := by simp [zx]
  have him : zx.im = h := by simp [zx]
  obtain ⟨hCE1, hCE⟩ := Sh_CE_spec
  have hfl := Sh_flow_pt hCE1 (hCE ι) H ht1 hzx4 hzx (by rw [hre]; exact hxE)
    (((Sh_u U μ t zx).im - (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) / (Sh_m U μ t zx).im)
  refine hfl.trans ?_
  rw [hre, him]
  obtain ⟨e1, e2, -⟩ := hCE ι U μ H t ht1 zx hzx4 hzx (by rw [hre]; exact hxE)
  rw [hre, him] at e1 e2
  have hk0 : 0 ≤ kappa Λt x := le_min (abs_nonneg _) (abs_nonneg _)
  set S := Real.sqrt (kappa Λt x + h)
  have hS2 : Real.sqrt (κ₀ / 2) ≤ S := Real.sqrt_le_sqrt (by linarith)
  have hs0 : 0 < Real.sqrt (κ₀ / 2) := Real.sqrt_pos.2 (by linarith)
  have hSpos : 0 < S := lt_of_lt_of_le hs0 hS2
  -- `σ / S ≤ √2 K₂`
  have hσS : σ / S ≤ Real.sqrt 2 * K₂ := by
    rw [div_le_iff₀ hSpos]
    have e : Real.sqrt κ₀ = Real.sqrt 2 * Real.sqrt (κ₀ / 2) := by
      rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
    calc σ ≤ K₂ * Real.sqrt κ₀ := hσ
      _ = Real.sqrt 2 * K₂ * Real.sqrt (κ₀ / 2) := by rw [e]; ring
      _ ≤ Real.sqrt 2 * K₂ * S := by gcongr
  -- `Im w ≤ h + C_E √(K₁ + 1) √(κ₀ + η)`
  have hSup : S ≤ Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η) :=
    Sh_sqrt_mono (K₁ + 1) (by linarith) hκ₀.le hη.le (by nlinarith) hk0 |>.trans' (by
      exact Real.sqrt_le_sqrt (by linarith))
  have hwim : (zx + Sh_m U μ t zx).im ≤ h + Sh_CE * Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η) := by
    rw [Complex.add_im, him]
    have : Sh_CE * S ≤ Sh_CE * (Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η)) := by gcongr
    linarith
  -- `|g' - R| ≤ C_E h / (15 √(κ₀/2))`
  have hratio := Sh_R_ratio H ht1 hzx
  have he : |((Sh_u U μ t zx).im - (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) /
      (Sh_m U μ t zx).im - Sh_R μ t (zx + Sh_m U μ t zx)| ≤ Sh_CE * h / (15 * Real.sqrt (κ₀ / 2)) := by
    rw [sub_div, hratio, show ∀ a b : ℝ, a - b - a = -b by intros; ring, abs_neg]
    have hu := Sh_u3 H ht1 hh
    have hlow : Sh_CE⁻¹ * Real.sqrt (κ₀ / 2) ≤ (Sh_m U μ t zx).im :=
      le_trans (mul_le_mul_of_nonneg_left hS2 (inv_nonneg.2 (by linarith))) e1
    have hpos : 0 < Sh_CE⁻¹ * Real.sqrt (κ₀ / 2) := mul_pos (inv_pos.2 (by linarith)) hs0
    rw [abs_div, abs_of_pos (lt_of_lt_of_le hpos hlow), div_le_iff₀ (lt_of_lt_of_le hpos hlow)]
    calc |(Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im| ≤ h / 15 := hu
      _ = Sh_CE * h / (15 * Real.sqrt (κ₀ / 2)) * (Sh_CE⁻¹ * Real.sqrt (κ₀ / 2)) := by
          field_simp
      _ ≤ _ := by gcongr
  have hM0 : 0 ≤ Sh_CE ^ 2 * (1600 / 49) := by positivity
  have hwim0 : 0 ≤ (zx + Sh_m U μ t zx).im := by
    rw [Complex.add_im, him]; linarith [(Sh_basic H ht1 hzx).1]
  calc Sh_CE ^ 2 * (1600 / 49) * (1 + σ / S) *
        (8 * σ * (zx + Sh_m U μ t zx).im +
          |((Sh_u U μ t zx).im - (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) /
            (Sh_m U μ t zx).im - Sh_R μ t (zx + Sh_m U μ t zx)|)
      ≤ Sh_CE ^ 2 * (1600 / 49) * (1 + Real.sqrt 2 * K₂) *
        (8 * σ * (h + Sh_CE * Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η)) +
          Sh_CE * h / (15 * Real.sqrt (κ₀ / 2))) := by
        gcongr

end ShiftMain5

section ShiftMain6

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Sh_hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf

set_option maxHeartbeats 1600000 in -- elaboration of large sums over the spectrum
/-- (A.34) [modification_shift_eigenvector] in general form:
`|Δ_ev(z₁) - (γ_k(1) - γ_k(0))| ≤ C ⟨Λ²⟩ √(κ₀ + η)` for `0 < η ≤ 1`. -/
private lemma Sh_T2 {U : Matrix.unitaryGroup ι ℂ} {μ : ι → ℝ} (H : Sh_Hyp U μ) {Mc k : ℕ}
    {κ₀ K₁ K₂ : ℝ} (Q : Sh_Q U μ Mc k κ₀ K₁) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hσ : ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 ≤ K₂ * Real.sqrt κ₀) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) :
    |(Sh_D U μ 1 ((quant (rho (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k : ℂ) +
        (η : ℂ) * Complex.I)).re -
      (quant (rho (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k -
        quant (rho (((0 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k)| ≤
      (Sh_KV * Real.sqrt (K₁ + 1) + Sh_CE ^ 2 * (1600 / 49) * (1 + Real.sqrt 2 * K₂) *
        (8 * Sh_CE * Real.sqrt (K₁ + 1))) *
        (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) * Real.sqrt (κ₀ + η) := by
  set γ : ℝ → ℝ := fun t => quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) Mc k with hγdef
  set σ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2
  have hσ0 : 0 ≤ σ := by positivity
  obtain ⟨hc0, hc1⟩ := Sh_c_bounds Q.k1 Q.kM
  set c := ((k : ℝ) - 1 / 2) / Mc
  have hκ₀ := Q.κpos
  obtain ⟨hCS, -⟩ := Sh_CS_spec
  obtain ⟨hCE, -⟩ := Sh_CE_spec
  obtain ⟨hKV1, hKV⟩ := Sh_KV_spec
  set M := Sh_CE ^ 2 * (1600 / 49) * (1 + Real.sqrt 2 * K₂)
  have hM : 0 ≤ M := by positivity
  set a := Sh_CE / (15 * Real.sqrt (κ₀ / 2))
  have ha : 0 ≤ a := by positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  set L := (1 + 34 / η) + 2
  have hL : 0 < L := by positivity
  set δ := min (κ₀ / 2) (ε / (2 * L))
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  have hδκ : δ ≤ κ₀ / 2 := min_le_left _ _
  have hδε : L * δ ≤ ε / 2 := by
    have := min_le_right (κ₀ / 2) (ε / (2 * L))
    calc L * δ ≤ L * (ε / (2 * L)) := by gcongr
      _ = ε / 2 := by field_simp
  set ρ₀ := Sh_CS⁻¹ * (κ₀ / 2)
  have hρ₀ : 0 < ρ₀ := by positivity
  set N := M * (8 * σ + a) + 1
  have hN : 0 < N := by positivity
  set h := min (min ((1 - c) / 2) η) (min (Real.pi * ρ₀ * δ / 4) (ε / (2 * N)))
  have hh : 0 < h := lt_min (lt_min (by linarith) hη) (lt_min (by positivity) (by positivity))
  have hh1c : h ≤ 1 - c := by
    have : h ≤ (1 - c) / 2 := (min_le_left (min ((1 - c) / 2) η) _).trans (min_le_left _ _)
    linarith
  have hhη : h ≤ η := (min_le_left _ _).trans (min_le_right _ _)
  have hh1 : h ≤ 1 := hhη.trans hη1
  have hsmall : 2 * h / Real.pi < ρ₀ * δ := by
    have : h ≤ Real.pi * ρ₀ * δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [Real.pi_pos, mul_pos hρ₀ hδ]
  have hNh : N * h ≤ ε / 2 := by
    have : h ≤ ε / (2 * N) := (min_le_right _ _).trans (min_le_right _ _)
    calc N * h ≤ N * (ε / (2 * N)) := by gcongr
      _ = ε / 2 := by field_simp
  obtain ⟨h3, hclose⟩ := Sh_setup H Q hδ hδκ hh hh1c hsmall
  set g := Sh_gh U μ c h
  have hgc := Sh_gh_contOn H hc0 hh hh1 h3
  set p : ℝ → ℂ := fun t => (g t : ℂ) + (h : ℂ) * Complex.I
  have hpc : ContinuousOn p (Set.Icc 0 1) :=
    (Complex.continuous_ofReal.comp_continuousOn hgc).add continuousOn_const
  have hmaps : Set.MapsTo (fun t : ℝ => ((t, p t) : ℝ × ℂ)) (Set.Icc 0 1)
      {q | |q.1| ≤ 1 ∧ 0 < q.2.im} := fun t ht => ⟨Sh_abs01 ht, Sh_im_hpath hh _⟩
  have hmc : ContinuousOn (fun t => Sh_m U μ t (p t)) (Set.Icc 0 1) := by
    have := ContinuousOn.comp (g := fun q : ℝ × ℂ => Sh_m U μ q.1 q.2)
      (f := fun t : ℝ => ((t, p t) : ℝ × ℂ)) (Sh_joint H) (continuousOn_id.prodMk hpc) hmaps
    exact this
  set D : ℝ → ℝ := fun t => (Sh_D U μ t (p t)).re - g t
  have hDc : ContinuousOn D (Set.Icc 0 1) := by
    have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, Sh_m U μ t (p t) ≠ 0 := fun t ht h0 => by
      have := (Sh_basic H (Sh_abs01 ht) (Sh_im_hpath hh (g t))).1
      simp only [p] at h0
      rw [h0, Complex.zero_im] at this; linarith
    have : ContinuousOn (fun t => Sh_D U μ t (p t)) (Set.Icc 0 1) :=
      (hpc.add hmc).add (hmc.inv₀ hne)
    exact (Complex.continuous_re.comp_continuousOn this).sub hgc
  -- derivative on `(0, 1)` and its bound
  have hDd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ d : ℝ, HasDerivAt D d t ∧
      |d| ≤ M * (8 * σ * (h + Sh_CE * Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η)) + a * h) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have habs : |t| < 1 := by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
    have hg' := Sh_gh_deriv H hc0 hh hh1 h3 ht
    have hp' : HasDerivAt p (((((Sh_u U μ t ((g t : ℂ) + (h : ℂ) * Complex.I)).im -
          (Sh_u U μ t ((3 : ℝ) + (h : ℂ) * Complex.I)).im) /
        (Sh_m U μ t ((g t : ℂ) + (h : ℂ) * Complex.I)).im : ℝ) : ℂ)) t :=
      hg'.ofReal_comp.add_const _
    have hDp := Sh_D_path H habs hp' (Sh_im_hpath hh (g t))
    have hre := (Sh_hasDerivAt_re hDp).sub hg'
    refine ⟨_, hre, ?_⟩
    have hb := Sh_pt2 H ht' (Q.edges t ht') (Q.bulk t ht') (Q.kup t ht') hK₁ hK₂ hσ hκ₀
      (hclose t ht') hδκ hh hhη hη1
    rw [Complex.add_re, Complex.ofReal_re, add_sub_cancel_left]
    refine (Complex.abs_re_le_norm _).trans (hb.trans (le_of_eq ?_))
    simp only [M, a]
    ring
  choose d hd1 hd2 using hDd
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope D
    (fun t => if ht : t ∈ Set.Ioo (0 : ℝ) 1 then d t ht else 0) zero_lt_one hDc
    (fun t ht => by simp only [ht, dif_pos]; exact hd1 t ht)
  simp only [hξ, dif_pos, sub_zero, div_one] at hslope
  have hD1 : |D 1 - D 0| ≤ M * (8 * σ * (h + Sh_CE * Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η)) +
      a * h) := by rw [← hslope]; exact hd2 ξ hξ
  have hD0 : D 0 = -g 0 := by
    simp only [D, p]
    rw [Sh_D0 U μ (Sh_im_hpath hh (g 0))]
    simp
  -- vertical and horizontal moves at `t = 1`
  have h1I : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  obtain ⟨hxE, hx3, hγ3, hκlo, hκhi⟩ := Sh_near (Q.edges 1 h1I) (Q.bulk 1 h1I) hκ₀
    (hclose 1 h1I) hδκ
  have hk0 : 0 ≤ kappa (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) (g 1) :=
    le_min (abs_nonneg _) (abs_nonneg _)
  have hκx : kappa (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) (g 1) ≤ (K₁ + 1) * κ₀ := by
    have e1 : kappa (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) (g 1) =
      min |Eplus (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) - g 1|
        |g 1 - Eminus (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))| := rfl
    have e2 := Q.kup 1 h1I
    have e3 : kappa (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) (γ 1) =
      min |Eplus (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) - γ 1|
        |γ 1 - Eminus (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))| := rfl
    rw [e1]
    have : kappa (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) (γ 1) ≤ K₁ * κ₀ := e2
    rw [e3] at this
    linarith
  have hV := (hKV ι U μ H 1 (by norm_num) (g 1) hx3 hxE h η hh hhη hη1).2
  have hsq : Real.sqrt (kappa (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) (g 1) + η) ≤
      Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η) :=
    Sh_sqrt_mono (K₁ + 1) (by linarith) hκ₀.le hη.le hκx hk0
  have hHz := (Sh_horiz H (t := 1) (by norm_num) hη hη1 hγ3 hx3).2
  have hc1' := hclose 1 h1I
  have hc0' := hclose 0 h0I
  -- assemble
  set z₁ : ℂ := (γ 1 : ℂ) + (η : ℂ) * Complex.I
  have hsplit : (Sh_D U μ 1 z₁).re - (γ 1 - γ 0) =
      (Sh_D U μ 1 z₁ - Sh_D U μ 1 ((g 1 : ℂ) + (η : ℂ) * Complex.I)).re +
      (Sh_D U μ 1 ((g 1 : ℂ) + (η : ℂ) * Complex.I) - Sh_D U μ 1 (p 1)).re +
      (D 1 - D 0) + (g 1 - γ 1) - (g 0 - γ 0) := by
    simp only [D, Complex.sub_re, hD0]; ring
  rw [hsplit]
  have t1 : |(Sh_D U μ 1 z₁ - Sh_D U μ 1 ((g 1 : ℂ) + (η : ℂ) * Complex.I)).re| ≤
      (1 + 34 / η) * δ := by
    refine (Complex.abs_re_le_norm _).trans (hHz.trans ?_)
    gcongr
    rw [abs_sub_comm]; exact hc1'.le
  have t2 : |(Sh_D U μ 1 ((g 1 : ℂ) + (η : ℂ) * Complex.I) - Sh_D U μ 1 (p 1)).re| ≤
      Sh_KV * σ * (Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η)) := by
    refine (Complex.abs_re_le_norm _).trans (hV.trans ?_)
    gcongr
  have habs5 := abs_add_three ((Sh_D U μ 1 z₁ - Sh_D U μ 1 ((g 1 : ℂ) + (η : ℂ) * Complex.I)).re)
    ((Sh_D U μ 1 ((g 1 : ℂ) + (η : ℂ) * Complex.I) - Sh_D U μ 1 (p 1)).re) (D 1 - D 0)
  have habs6 := abs_add_three ((Sh_D U μ 1 z₁ - Sh_D U μ 1 ((g 1 : ℂ) + (η : ℂ) * Complex.I)).re +
    (Sh_D U μ 1 ((g 1 : ℂ) + (η : ℂ) * Complex.I) - Sh_D U μ 1 (p 1)).re + (D 1 - D 0))
    (g 1 - γ 1) (-(g 0 - γ 0))
  rw [abs_neg, ← sub_eq_add_neg] at habs6
  have hsqK := Real.sqrt_nonneg (K₁ + 1)
  have hsqe := Real.sqrt_nonneg (κ₀ + η)
  have hmain : M * (8 * σ * (h + Sh_CE * Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η)) + a * h) =
      M * (8 * Sh_CE * Real.sqrt (K₁ + 1)) * σ * Real.sqrt (κ₀ + η) + M * (8 * σ + a) * h := by
    ring
  have hNh' : M * (8 * σ + a) * h ≤ ε / 2 := by
    have : M * (8 * σ + a) * h ≤ N * h := by
      simp only [N]; nlinarith
    linarith
  have hLδ' : (1 + 34 / η) * δ + δ + δ = L * δ := by simp only [L]; ring
  calc |(Sh_D U μ 1 z₁ - Sh_D U μ 1 ((g 1 : ℂ) + (η : ℂ) * Complex.I)).re +
        (Sh_D U μ 1 ((g 1 : ℂ) + (η : ℂ) * Complex.I) - Sh_D U μ 1 (p 1)).re +
        (D 1 - D 0) + (g 1 - γ 1) - (g 0 - γ 0)|
      ≤ (1 + 34 / η) * δ + Sh_KV * σ * (Real.sqrt (K₁ + 1) * Real.sqrt (κ₀ + η)) +
        (M * (8 * Sh_CE * Real.sqrt (K₁ + 1)) * σ * Real.sqrt (κ₀ + η) + M * (8 * σ + a) * h) +
        δ + δ := by
        rw [← hmain]
        linarith [hc1'.le, hc0'.le, habs5, habs6, t1, t2, hD1]
    _ ≤ _ := by nlinarith

end ShiftMain6

/-! ### The block interaction `Λ = lam D N A` -/

section ShiftLam
open scoped Matrix.Norms.L2Operator

/-- The embedding of the `N`-dimensional space as the `a`-th block. -/
private def Sh_J (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Fin N) ℂ :=
  Matrix.of fun p i => if p = (a, i) then 1 else 0

private lemma Sh_J_conj_mul (D N : ℕ) (a : Fin D) : (Sh_J D N a)ᴴ * Sh_J D N a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Sh_J, Matrix.of_apply, Matrix.one_apply]
  have : ∀ p : Idx D N, star (if p = (a, i) then (1 : ℂ) else 0) * (if p = (a, j) then 1 else 0) =
      if p = (a, i) then (if i = j then 1 else 0) else 0 := by
    intro p
    by_cases h : p = (a, i)
    · subst h
      by_cases hij : i = j <;> simp [hij]
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma Sh_J_norm (D N : ℕ) (hN : 1 ≤ N) (a : Fin D) : ‖Sh_J D N a‖ ≤ 1 := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (Sh_J D N a)
  rw [Sh_J_conj_mul, norm_one] at h1
  have h0 : 0 ≤ ‖Sh_J D N a‖ := norm_nonneg _
  nlinarith

private lemma Sh_block_norm (D N : ℕ) (hN : 1 ≤ N) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖Sh_J D N a * M * (Sh_J D N b)ᴴ‖ ≤ ‖M‖ := by
  have ha := Sh_J_norm D N hN a
  have hb := Sh_J_norm D N hN b
  calc ‖Sh_J D N a * M * (Sh_J D N b)ᴴ‖ ≤ ‖Sh_J D N a * M‖ * ‖(Sh_J D N b)ᴴ‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Sh_J D N a‖ * ‖M‖) * ‖(Sh_J D N b)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
    _ = ‖M‖ := by ring

private lemma Sh_block_apply (D N : ℕ) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ) (p q : Idx D N) :
    (Sh_J D N a * M * (Sh_J D N b)ᴴ) p q = if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = a <;> by_cases h2 : q1 = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Sh_J, Prod.ext_iff, h1, h2]

private lemma Sh_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = ∑ a : Fin D, ∑ b : Fin D,
      ((if fwd D a b then Sh_J D N a * A * (Sh_J D N b)ᴴ else 0) +
        (if fwd D b a then Sh_J D N a * Aᴴ * (Sh_J D N b)ᴴ else 0)) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.add_apply]
  have e1 : ∀ a b : Fin D, (if fwd D a b then Sh_J D N a * A * (Sh_J D N b)ᴴ else 0) p q =
      if fwd D a b ∧ p.1 = a ∧ q.1 = b then A p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D a b <;> simp [h, Sh_block_apply]
  have e2 : ∀ a b : Fin D, (if fwd D b a then Sh_J D N a * Aᴴ * (Sh_J D N b)ᴴ else 0) p q =
      if fwd D b a ∧ p.1 = a ∧ q.1 = b then Aᴴ p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D b a <;> simp [h, Sh_block_apply]
  simp only [e1, e2, Finset.sum_add_distrib]
  unfold lam
  congr 1
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha, ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb, hb]) (by simp)]
    by_cases h : fwd D p.1 q.1 <;> simp [h]
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha, ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb, hb]) (by simp)]
    by_cases h : fwd D q.1 p.1 <;> simp [h, Matrix.conjTranspose_apply]

/-- `‖lam D N A‖ ≤ 2D²‖A‖`. -/
private lemma Sh_opNorm_lam (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := by
  show ‖lam D N A‖ ≤ 2 * (D : ℝ) ^ 2 * ‖A‖
  rw [Sh_lam_eq]
  have hb : ∀ a b : Fin D, ‖(if fwd D a b then Sh_J D N a * A * (Sh_J D N b)ᴴ else 0) +
      (if fwd D b a then Sh_J D N a * Aᴴ * (Sh_J D N b)ᴴ else 0)‖ ≤ 2 * ‖A‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D a b then Sh_J D N a * A * (Sh_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact Sh_block_norm D N hN a b A
      · simp
    have h2 : ‖(if fwd D b a then Sh_J D N a * Aᴴ * (Sh_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact (Sh_block_norm D N hN a b Aᴴ).trans (by rw [Matrix.l2_opNorm_conjTranspose])
      · simp
    linarith
  calc ‖∑ a : Fin D, ∑ b : Fin D, _‖ ≤ ∑ a : Fin D, ‖∑ b : Fin D, _‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin D, ∑ b : Fin D, 2 * ‖A‖ := by
        refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun b _ => hb a b)
    _ = 2 * (D : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end ShiftLam

section ShiftLam2

private lemma Sh_lam_smul (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    (t : ℂ) • lam D N A = lam D N ((t : ℂ) • A) := by
  ext p q
  simp only [lam, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [mul_add, Complex.conj_ofReal]

private lemma Sh_lam_diag (D N : ℕ) (hD : 2 ≤ D) (A : Matrix (Fin N) (Fin N) ℂ) (p : Idx D N) :
    lam D N A p p = 0 := by
  have h : ¬ fwd D p.1 p.1 := by
    unfold fwd
    rintro (h | ⟨h3, h1, h0⟩)
    · omega
    · omega
  simp [lam, h]

private lemma Sh_ntr_lam (D N : ℕ) (hD : 2 ≤ D) (A : Matrix (Fin N) (Fin N) ℂ) :
    ntr (lam D N A) = 0 := by
  simp [ntr, Matrix.trace, Sh_lam_diag D N hD]

private lemma Sh_opNorm_smul' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (c : ℂ) :
    opNorm (c • A) = ‖c‖ * opNorm A := by
  unfold opNorm
  rw [map_smul, norm_smul]

/-- `⟨Λ²⟩ ≤ 4D ‖A‖²_HS / N` for `Λ = lam D N A`. -/
private lemma Sh_avgSq_lam (D N : ℕ) (hD : 2 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    avgSq (lam D N A) ≤ 4 * D * hsNorm A ^ 2 / N := by
  have hH := lam_isHermitian D N A
  set Λ := lam D N A
  have hn : (Fintype.card (Idx D N) : ℝ) = D * N := by simp
  have hDN : (0 : ℝ) < D * N := by
    have : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  -- `⟨Λ²⟩ = (DN)⁻¹ Σ_{p,q} |Λ_pq|²`
  have e : avgSq Λ = ((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2 := by
    unfold avgSq ntr
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply]
    have : ∀ p q : Idx D N, Λ p q * Λ q p = ((‖Λ p q‖ ^ 2 : ℝ) : ℂ) := by
      intro p q
      have : Λ q p = star (Λ p q) := by
        have := congrFun (congrFun hH.eq q) p
        simpa [Matrix.conjTranspose_apply] using this.symm
      rw [this, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [this]
    rw [show ((Fintype.card (Idx D N) : ℂ))⁻¹ * ∑ p : Idx D N, ∑ q : Idx D N,
        ((‖Λ p q‖ ^ 2 : ℝ) : ℂ) = ((((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2 : ℝ) : ℂ) by
      push_cast [Fintype.card_prod, Fintype.card_fin]; ring]
    rw [Complex.ofReal_re]
  -- each entry
  have hent : ∀ p q : Idx D N, ‖Λ p q‖ ^ 2 ≤ 2 * (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) := by
    intro p q
    simp only [Λ, lam]
    have h1 : ‖(if fwd D p.1 q.1 then A p.2 q.2 else 0)‖ ≤ ‖A p.2 q.2‖ := by
      split_ifs <;> simp
    have h2 : ‖(if fwd D q.1 p.1 then star (A q.2 p.2) else 0)‖ ≤ ‖A q.2 p.2‖ := by
      split_ifs <;> simp
    set x := (if fwd D p.1 q.1 then A p.2 q.2 else 0)
    set y := (if fwd D q.1 p.1 then star (A q.2 p.2) else 0)
    have hxy := norm_add_le x y
    have h3 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
    have h1' : ‖x‖ ^ 2 ≤ ‖A p.2 q.2‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' : ‖y‖ ^ 2 ≤ ‖A q.2 p.2‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have key : ∀ g : Fin N → Fin N → ℝ, ∑ p : Idx D N, ∑ q : Idx D N, g p.2 q.2 =
      (D : ℝ) ^ 2 * ∑ i, ∑ j, g i j := by
    intro g
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  have hsum : ∑ p : Idx D N, ∑ q : Idx D N, (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) =
      2 * (D : ℝ) ^ 2 * hsNorm A ^ 2 := by
    have hs : hsNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
      unfold hsNorm; rw [Real.sq_sqrt (by positivity)]
    simp only [Finset.sum_add_distrib]
    rw [key (fun i j => ‖A i j‖ ^ 2), key (fun i j => ‖A j i‖ ^ 2), hs,
      Finset.sum_comm (f := fun i j => ‖A j i‖ ^ 2)]
    ring
  rw [e]
  calc ((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2
      ≤ ((D : ℝ) * N)⁻¹ * ∑ p : Idx D N, ∑ q : Idx D N,
          2 * (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) := by
        gcongr with p _ q _; exact hent p q
    _ = 4 * D * hsNorm A ^ 2 / N := by
        simp only [← Finset.mul_sum]
        rw [hsum]
        field_simp
        ring

end ShiftLam2

section ShiftClass

/-- `𝔯(k) ≥ 1`, `𝔯(k) ≤ k`, `𝔯(k) ≤ DN + 1 - k`, and `𝔯(k)` is one of the two. -/
private lemma Sh_rk (D N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ D * N) :
    1 ≤ rk D N k ∧ rk D N k ≤ k ∧ rk D N k ≤ ((D * N + 1 - k : ℕ) : ℝ) ∧
      (rk D N k = k ∨ rk D N k = ((D * N + 1 - k : ℕ) : ℝ)) := by
  unfold rk
  refine ⟨by exact_mod_cast (le_min hk (by omega)), by exact_mod_cast min_le_left _ _,
    by exact_mod_cast min_le_right _ _, ?_⟩
  rcases min_choice k (D * N + 1 - k) with h | h
  · left; rw [h]
  · right; rw [h]

/-- The facts on `Λ = lam D N A` used for Lemma A.3 [lemma_modification_of_shift] and (A.13)
[de_ir_1]: a spectral decomposition, `‖Λ‖ ≤ 1/10`, `⟨Λ⟩ = 0`, the edges in `(-3, 3)` and the
quantile bounds (2.21) [eq:kappa_gamma_k] along `tΛ`, `t ∈ [0, 1]`, with
`κ₀ = c 𝔯(k)^{2/3} N^{-2/3}`. -/
private lemma Sh_class (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      ∃ (U : Matrix.unitaryGroup (Idx D N) ℂ) (μ : Idx D N → ℝ),
        lam D N A = Sh_cd U (fun j => (μ j : ℂ)) ∧ Sh_Hyp U μ ∧
        Sh_Q U μ (D * N) k (c * rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) (C / c) ∧
        avgSq (lam D N A) = ((Fintype.card (Idx D N) : ℝ))⁻¹ * ∑ j, μ j ^ 2 := by
  obtain ⟨c, C, hc, hC, N₁, hkg⟩ := kappa_gamma_k D hD δA hδA
  obtain ⟨Ce, hCe, hedge⟩ := edge_close_to_edge_sc
  set T : ℝ := 20 * (D : ℝ) ^ 2 * (1 + Ce)
  have hT : 0 < T := by positivity
  refine ⟨c, C, hc, hC, max (max N₁ 1) ⌈T ^ (1 / δA)⌉₊, le_max_of_le_left (le_max_right _ _),
    fun N hN A hA k hk hkN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  haveI : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  have hNT : T ≤ (N : ℝ) ^ δA := by
    have hc : ⌈T ^ (1 / δA)⌉₊ ≤ N := (le_max_right _ _).trans hN
    have h1 : T ^ (1 / δA) ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hc)
    calc T = (T ^ (1 / δA)) ^ δA := by
          rw [← Real.rpow_mul hT.le, one_div_mul_cancel hδA.ne', Real.rpow_one]
      _ ≤ (N : ℝ) ^ δA := Real.rpow_le_rpow (by positivity) h1 hδA.le
  have hNd : (N : ℝ) ^ (-δA) ≤ T⁻¹ := by
    rw [Real.rpow_neg hNpos.le]
    exact inv_anti₀ hT hNT
  -- norms along `tΛ`
  have hlamt : ∀ t ∈ Set.Icc (0 : ℝ) 1, opNorm ((t : ℂ) • A) ≤ (N : ℝ) ^ (-δA) ∧
      opNorm (lam D N ((t : ℂ) • A)) ≤ 1 / (10 * (1 + Ce)) := by
    intro t ht
    have h1 : opNorm ((t : ℂ) • A) ≤ (N : ℝ) ^ (-δA) := by
      rw [Sh_opNorm_smul', Complex.norm_real, Real.norm_eq_abs]
      calc |t| * opNorm A ≤ 1 * (N : ℝ) ^ (-δA) :=
            mul_le_mul (Sh_abs01 ht) hA (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    refine ⟨h1, (Sh_opNorm_lam D N hN1 _).trans ?_⟩
    calc 2 * (D : ℝ) ^ 2 * opNorm ((t : ℂ) • A) ≤ 2 * (D : ℝ) ^ 2 * T⁻¹ := by
          gcongr; exact h1.trans hNd
      _ = 1 / (10 * (1 + Ce)) := by simp only [T]; field_simp; ring
  have hsmall : ∀ t ∈ Set.Icc (0 : ℝ) 1, opNorm (lam D N ((t : ℂ) • A)) ≤ 1 / 10 := by
    intro t ht
    refine (hlamt t ht).2.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  -- the decomposition of `Λ`
  have hH := lam_isHermitian D N A
  obtain ⟨U, μ, hΛ, hμ⟩ := Sh_decomp hH
  have h1A : lam D N A = lam D N (((1 : ℝ) : ℂ) • A) := by simp
  have hn1 : opNorm (lam D N A) ≤ 1 / 10 := by
    rw [h1A]; exact hsmall 1 ⟨zero_le_one, le_refl _⟩
  have hsum : ∑ j, μ j = 0 := by
    have := Sh_ntr_lam D N hD A
    rw [hΛ, Sh_ntr_cd] at this
    have hn : ((Fintype.card (Idx D N) : ℂ))⁻¹ ≠ 0 := by
      apply inv_ne_zero; simp; omega
    have h2 : ∑ j, (μ j : ℂ) = 0 := (mul_eq_zero.1 this).resolve_left hn
    exact_mod_cast h2
  have H : Sh_Hyp U μ := ⟨by rw [← hΛ]; exact hn1, fun j => (hμ j).trans hn1, hsum⟩
  refine ⟨U, μ, hΛ, H, ?_, ?_⟩
  · -- the flow hypotheses
    have hst : ∀ t : ℝ, (t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)) = lam D N ((t : ℂ) • A) := by
      intro t; rw [← hΛ, Sh_lam_smul]
    obtain ⟨r1, rk', rk'', rch⟩ := Sh_rk D N k hk hkN
    have hr0 : (0 : ℝ) ≤ rk D N k := by linarith
    have hk' : 1 ≤ D * N + 1 - k := by omega
    have hk'' : D * N + 1 - k ≤ D * N := by omega
    have hkk : D * N + 1 - (D * N + 1 - k) = k := by omega
    have hmono : ∀ x : ℝ, rk D N k ≤ x →
        c * rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤
          c * (x ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
      intro x hx
      rw [← mul_assoc]
      gcongr
    refine ⟨hk, hkN, by positivity, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · rw [hst]
      have hE := hedge (Idx D N) (lam D N ((t : ℂ) • A)) (lam_isHermitian _ _ _) (hsmall t ht)
      have hb : Ce * opNorm (lam D N ((t : ℂ) • A)) < 1 := by
        calc Ce * opNorm (lam D N ((t : ℂ) • A)) ≤ Ce * (1 / (10 * (1 + Ce))) := by
              gcongr; exact (hlamt t ht).2
          _ < 1 := by rw [mul_one_div, div_lt_one (by positivity)]; nlinarith
      have hs2 := lt_of_le_of_lt hE hb
      have a1 := abs_nonneg (2 - Eplus (lam D N ((t : ℂ) • A)))
      have a2 := abs_nonneg (2 + Eminus (lam D N ((t : ℂ) • A)))
      have h2 : |2 + Eminus (lam D N ((t : ℂ) • A))| < 1 := by linarith
      have h3 : |2 - Eplus (lam D N ((t : ℂ) • A))| < 1 := by linarith
      exact ⟨by linarith [(abs_lt.1 h2).1], by linarith [(abs_lt.1 h3).1]⟩
    · rw [hst]
      obtain ⟨a1, -, -, -⟩ := hkg N hNN₁ ((t : ℂ) • A) (hlamt t ht).1 k hk hkN
      obtain ⟨-, -, b3, -⟩ := hkg N hNN₁ ((t : ℂ) • A) (hlamt t ht).1 (D * N + 1 - k) hk' hk''
      rw [hkk] at b3
      constructor
      · have := hmono _ (by exact_mod_cast rk'' : rk D N k ≤ ((D * N + 1 - k : ℕ) : ℝ))
        linarith
      · have := hmono _ rk'
        linarith
    · rw [hst]
      obtain ⟨a1, a2, -, -⟩ := hkg N hNN₁ ((t : ℂ) • A) (hlamt t ht).1 k hk hkN
      obtain ⟨-, -, b3, b4⟩ := hkg N hNN₁ ((t : ℂ) • A) (hlamt t ht).1 (D * N + 1 - k) hk' hk''
      rw [hkk] at b3 b4
      have hcC : C / c * (c * rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) =
          C * (rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
        field_simp
      rw [hcC]
      unfold kappa
      have p1 : 0 ≤ c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by positivity
      have p2 : 0 ≤ c * (((D * N + 1 - k : ℕ) : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
        positivity
      rcases rch with h | h
      · refine (min_le_left _ _).trans ?_
        rw [abs_of_nonneg (by linarith), h]; exact a2
      · refine (min_le_right _ _).trans ?_
        rw [abs_of_nonneg (by linarith), h]; exact b4
  · rw [hΛ]
    simp only [avgSq, Sh_cd_mul, Sh_ntr_cd]
    rw [show ((Fintype.card (Idx D N) : ℂ))⁻¹ * ∑ j, (μ j : ℂ) * (μ j : ℂ) =
      ((((Fintype.card (Idx D N) : ℝ))⁻¹ * ∑ j, μ j ^ 2 : ℝ) : ℂ) by push_cast; simp [sq]]
    rw [Complex.ofReal_re]

end ShiftClass

section ShiftConv

variable {D N : ℕ}

/-- `Δ_ev(z) = Re Δ̃_1(z)` for `Im z > 0`. -/
private lemma Sh_shiftEv_eq (U : Matrix.unitaryGroup (Idx D N) ℂ) (μ : Idx D N → ℝ) {z : ℂ}
    (hz : 0 < z.im) : shiftEv (Sh_cd U (fun j => (μ j : ℂ))) z = (Sh_D U μ 1 z).re := by
  have e : Sh_m U μ 1 z = mExt (Sh_cd U (fun j => (μ j : ℂ))) z := by
    simp only [Sh_m, Complex.ofReal_one, one_smul, mExt, hz, ite_true]
  simp only [shiftEv, Sh_D, e]

/-- `Δ(t)` of (5.19) [definition_shift_eigenvalue] in spectral form. -/
private lemma Sh_shiftT_eq [NeZero D] [NeZero N] (U : Matrix.unitaryGroup (Idx D N) ℂ)
    (μ : Idx D N → ℝ) (k : ℕ) (ε t : ℝ) (hη : 0 < etaK D N k ε) :
    shiftT (Sh_cd U (fun j => (μ j : ℂ))) k ε t =
      Sh_R μ t (zOne ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) k ε +
        Sh_m U μ t (zOne ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) k ε)) := by
  haveI : Nonempty (Idx D N) := ⟨(0, 0)⟩
  set z := zOne ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) k ε
  have hz : 0 < z.im := by simp [z, zOne, hη]
  obtain ⟨-, -, hM⟩ := Sh_bridge U μ t hz
  have hME : MExt ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z =
      MSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z := by
    simp only [MExt, MSol, mExt, hz, ite_true]
  have hn : (0 : ℝ) < Fintype.card (Idx D N) := by exact_mod_cast Fintype.card_pos
  set a : Idx D N → ℂ := fun j => (((t * μ j : ℝ) : ℂ) - (z + Sh_m U μ t z))⁻¹
  have hM' : MSol ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) z = Sh_cd U a := hM
  unfold shiftT
  rw [show zOne ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ))) k ε = z from rfl, hME, hM',
    Sh_cd_conjTranspose, Sh_cd_mul, Sh_cd_mul, Sh_cd_mul, Sh_ntr_cd, Sh_ntr_cd]
  have e1 : ∀ j, a j * (μ j : ℂ) * star (a j) = ((μ j * ‖a j‖ ^ 2 : ℝ) : ℂ) := fun j => by
    rw [mul_comm (a j), mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have e2 : ∀ j, a j * star (a j) = ((‖a j‖ ^ 2 : ℝ) : ℂ) := fun j => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [e1, e2, ← Complex.ofReal_sum]
  have hS : 0 < ∑ j, ‖a j‖ ^ 2 := by
    obtain ⟨j⟩ := ‹Nonempty (Idx D N)›
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i _ => sq_nonneg ‖a i‖)
      (Finset.mem_univ j))
    have hm : 0 < (Sh_m U μ t z).im := (Sh_bridge U μ t hz).1
    have : a j ≠ 0 := inv_ne_zero (Sh_ne_of_im _ (by
      simp only [Complex.add_im]; linarith))
    positivity
  rw [mul_div_mul_left _ _ (by
    simp only [ne_eq, inv_eq_zero, Nat.cast_eq_zero]; exact Fintype.card_ne_zero)]
  rw [← Complex.ofReal_div, Complex.ofReal_re]
  rfl

end ShiftConv

section ShiftCore

private lemma Sh_sqrt_rpow {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : Real.sqrt (x ^ a) = x ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; ring_nf

private lemma Sh_rpow_sq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num; ring_nf

/-- (2.8) [eq:condA2] gives `⟨Λ²⟩ ≤ (4D/√c) √κ₀` with `κ₀ = c 𝔯(k)^{2/3} N^{-2/3}`. -/
private lemma Sh_E7 {n r c hs εA : ℝ} (D : ℝ) (hD : 0 ≤ D) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hc : 0 < c) (hεA : 0 < εA) (hhs0 : 0 ≤ hs)
    (hhs : hs ≤ n ^ ((1 / 3 : ℝ) - εA) * r ^ (-(1 / 3 : ℝ))) :
    4 * D * hs ^ 2 / n ≤ 4 * D / Real.sqrt c *
      Real.sqrt (c * r ^ (2 / 3 : ℝ) * n ^ (-(2 / 3 : ℝ))) := by
  have hn0 : 0 < n := by linarith
  have hr0 : 0 < r := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hc.le, Sh_sqrt_rpow hr0.le,
    Sh_sqrt_rpow hn0.le]
  have h2 : hs ^ 2 ≤ n ^ (2 * ((1 / 3 : ℝ) - εA)) * r ^ (2 * (-(1 / 3 : ℝ))) := by
    calc hs ^ 2 ≤ (n ^ ((1 / 3 : ℝ) - εA) * r ^ (-(1 / 3 : ℝ))) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, Sh_rpow_sq hn0.le, Sh_rpow_sq hr0.le]
  have h3 : n ^ (2 * ((1 / 3 : ℝ) - εA)) / n ≤ n ^ (-(2 / 3 : ℝ) / 2) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hn0]
    exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have h4 : r ^ (2 * (-(1 / 3 : ℝ))) ≤ r ^ ((2 / 3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  have hp1 : 0 ≤ n ^ (2 * ((1 / 3 : ℝ) - εA)) := by positivity
  calc 4 * D * hs ^ 2 / n ≤ 4 * D * (n ^ (2 * ((1 / 3 : ℝ) - εA)) * r ^ (2 * (-(1 / 3 : ℝ)))) / n := by
        gcongr
    _ = 4 * D * (n ^ (2 * ((1 / 3 : ℝ) - εA)) / n) * r ^ (2 * (-(1 / 3 : ℝ))) := by ring
    _ ≤ 4 * D * n ^ (-(2 / 3 : ℝ) / 2) * r ^ ((2 / 3 : ℝ) / 2) := by gcongr
    _ = 4 * D / Real.sqrt c * (Real.sqrt c * r ^ ((2 / 3 : ℝ) / 2) * n ^ (-(2 / 3 : ℝ) / 2)) := by
        field_simp

end ShiftCore

section ShiftCore2

private lemma Sh_etaK_pos (D N k : ℕ) (ε : ℝ) (hN : 1 ≤ N) (hr : 1 ≤ rk D N k) :
    0 < etaK D N k ε := by
  have : (0 : ℝ) < N := by exact_mod_cast hN
  unfold etaK; positivity

set_option maxHeartbeats 1600000 in -- elaboration of large sums over the spectrum
/-- Both shifts are `γ_k - γ_k^sc` up to `C ⟨Λ²⟩ √(κ(γ_k) + η)` (Lemma A.3
[lemma_modification_of_shift], with the case `η > 1`), and `κ(γ_k) ≤ C 𝔯(k)^{2/3} N^{-2/3}`. -/
private lemma Sh_core (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) → ∀ ε : ℝ,
        |shiftEv (lam D N A) (zOne (lam D N A) k ε) -
            (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k)| ≤
          C * avgSq (lam D N A) *
            Real.sqrt (kappa (lam D N A) (quant (rho (lam D N A)) (D * N) k) + etaK D N k ε) ∧
        |shiftE (lam D N A) k ε -
            (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k)| ≤
          C * avgSq (lam D N A) *
            Real.sqrt (kappa (lam D N A) (quant (rho (lam D N A)) (D * N) k) + etaK D N k ε) ∧
        kappa (lam D N A) (quant (rho (lam D N A)) (D * N) k) ≤
          C * (rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
  obtain ⟨c, C₁, hc, hC₁, N₀, hN₀, hcl⟩ := Sh_class D hD δA hδA
  set K₁ := C₁ / c
  have hK₁ : 0 ≤ K₁ := by positivity
  set K₂ := 4 * D / Real.sqrt c
  have hK₂ : 0 ≤ K₂ := by positivity
  set C2 := Sh_KV * Real.sqrt (K₁ + 1) + Sh_CE ^ 2 * (1600 / 49) * (1 + Real.sqrt 2 * K₂) *
    (8 * Sh_CE * Real.sqrt (K₁ + 1))
  set C3 := 10 * (1 + Sh_KV * Real.sqrt (K₁ + 1))
  obtain ⟨hKV1, -⟩ := Sh_KV_spec
  obtain ⟨hCE1, -⟩ := Sh_CE_spec
  have hC2 : 0 ≤ C2 := by positivity
  have hC3 : 0 ≤ C3 := by positivity
  refine ⟨8 + 3 * (C2 + C3) + C₁, by positivity, N₀, hN₀, ?_⟩
  intro N hN A hA k hk hkN hhs ε
  have hN1 : 1 ≤ N := hN₀.trans hN
  haveI : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  haveI : NeZero D := ⟨by omega⟩
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨U, μ, hΛ, H, Q, hσrep⟩ := hcl N hN A hA k hk hkN
  obtain ⟨r1, -, -, -⟩ := Sh_rk D N k hk hkN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set κ₀ := c * rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))
  have hκ₀ : 0 < κ₀ := Q.κpos
  set σ := avgSq (lam D N A)
  have hσ0 : 0 ≤ σ := by rw [hσrep]; positivity
  -- `⟨Λ²⟩ ≤ K₂ √κ₀`
  have hσK : ((Fintype.card (Idx D N) : ℝ))⁻¹ * ∑ j, μ j ^ 2 ≤ K₂ * Real.sqrt κ₀ := by
    rw [← hσrep]
    refine (Sh_avgSq_lam D N hD hN1 A).trans ?_
    exact Sh_E7 (D : ℝ) (by positivity) hn1 r1 hc hεA (Real.sqrt_nonneg _) hhs
  have e1 : ((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)) = Sh_cd U (fun j => (μ j : ℂ)) := by
    simp
  have e0 : ((0 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)) = 0 := by simp
  have hrho0 : rho (0 : Matrix (Idx D N) (Idx D N) ℂ) = rhoSc := (rho_zero (ι := Idx D N)).2.1
  set γ1 := quant (rho (Sh_cd U (fun j => (μ j : ℂ)))) (D * N) k
  set η := etaK D N k ε
  have hη : 0 < η := Sh_etaK_pos D N k ε hN1 r1
  -- `κ₀ ≤ κ(γ_k) ≤ K₁ κ₀ ≤ 6`
  have h1I : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  obtain ⟨b1, b2⟩ := Q.bulk 1 h1I
  obtain ⟨ed1, ed2⟩ := Q.edges 1 h1I
  have hkup := Q.kup 1 h1I
  rw [e1] at b1 b2 ed1 ed2 hkup
  set κ := kappa (Sh_cd U (fun j => (μ j : ℂ))) γ1
  have hκ : κ₀ ≤ κ := by
    show κ₀ ≤ min |_ - γ1| |γ1 - _|
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact le_min (by linarith) (by linarith)
  have hκ6 : κ₀ ≤ 6 := by linarith
  have hsq1 : Real.sqrt (κ₀ + η) ≤ Real.sqrt (κ + η) := Real.sqrt_le_sqrt (by linarith)
  have hsq7 : Real.sqrt (κ₀ + 1) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  -- rewrite everything in spectral form
  rw [hΛ]
  have hshE : shiftE (Sh_cd U (fun j => (μ j : ℂ))) k ε = ∫ t in (0 : ℝ)..1,
      Sh_R μ t ((quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) (D * N) k : ℂ) +
        (η : ℂ) * Complex.I + Sh_m U μ t ((quant (rho ((t : ℂ) • Sh_cd U
          (fun j => (μ j : ℂ)))) (D * N) k : ℂ) + (η : ℂ) * Complex.I)) := by
    unfold shiftE
    congr 1
    funext t
    exact Sh_shiftT_eq U μ k ε t hη
  have hz1 : 0 < (zOne (Sh_cd U (fun j => (μ j : ℂ))) k ε).im := by
    show 0 < ((γ1 : ℂ) + (η : ℂ) * Complex.I).im
    simpa using hη
  rw [Sh_shiftEv_eq U μ hz1, hshE]
  have hzOne : zOne (Sh_cd U (fun j => (μ j : ℂ))) k ε = (γ1 : ℂ) + (η : ℂ) * Complex.I := rfl
  rw [hzOne]
  have hγ0 : quant rhoSc (D * N) k =
      quant (rho (((0 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) (D * N) k := by
    rw [e0, hrho0]
  have hγ1 : γ1 = quant (rho (((1 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) (D * N) k := by
    rw [e1]
  rw [hγ0]
  -- the bound on `κ(γ_k)`
  have hkapp : κ ≤ (8 + 3 * (C2 + C3) + C₁) * (rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
    have : K₁ * κ₀ = C₁ * (rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
      simp only [K₁, κ₀]; field_simp
    have hp : 0 ≤ rk D N k ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
    nlinarith
  rw [← hσrep] at hσK
  have hσ' : σ = ((Fintype.card (Idx D N) : ℝ))⁻¹ * ∑ j, μ j ^ 2 := hσrep
  refine ⟨?_, ?_, hkapp⟩
  · -- the eigenvector shift
    by_cases hη1 : η ≤ 1
    · have h2 := Sh_T2 H Q hK₁ hK₂ (by rw [← hσ']; exact hσK) hη hη1
      rw [← hγ1, ← hσ'] at h2
      refine h2.trans ?_
      have : C2 ≤ 8 + 3 * (C2 + C3) + C₁ := by linarith
      calc C2 * σ * Real.sqrt (κ₀ + η) ≤ C2 * σ * Real.sqrt (κ + η) := by gcongr
        _ ≤ _ := by gcongr
    · push_neg at hη1
      have h2 := Sh_T2 H Q hK₁ hK₂ (by rw [← hσ']; exact hσK) one_pos (le_refl 1)
      rw [← hγ1, ← hσ'] at h2
      have hD1 : ∀ x : ℝ, ∀ s : ℝ, 0 < s →
          |(Sh_D U μ 1 ((x : ℂ) + (s : ℂ) * Complex.I)).re| ≤ 10 / 7 * σ := by
        intro x s hs
        have hz : 0 < ((x : ℂ) + (s : ℂ) * Complex.I).im := by simpa using hs
        obtain ⟨-, b2', b3', -⟩ := Sh_basic H (t := 1) (by norm_num) hz
        obtain ⟨-, -, m3, -, -⟩ := Sh_m_bd μ 1 H.sum_zero H.eig_le (by norm_num) b3'.le
        have hmA : Sh_m U μ 1 ((x : ℂ) + (s : ℂ) * Complex.I) = ((Fintype.card (Idx D N) : ℂ))⁻¹ *
            ∑ j, ((((1 : ℝ) * μ j : ℝ) : ℂ) - ((x : ℂ) + (s : ℂ) * Complex.I +
              Sh_m U μ 1 ((x : ℂ) + (s : ℂ) * Complex.I)))⁻¹ := b2'
        rw [← hmA, ← hσ'] at m3
        refine (Complex.abs_re_le_norm _).trans ?_
        simp only [Sh_D]
        rw [add_assoc] at m3 ⊢
        simpa [add_assoc] using m3
      have hsqbig : 1 ≤ Real.sqrt (κ + η) := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
      have hγdiff : |γ1 - quant (rho (((0 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) (D * N) k| ≤
          10 / 7 * σ + C2 * σ * 3 := by
        have a := hD1 γ1 1 one_pos
        have hb : C2 * σ * Real.sqrt (κ₀ + 1) ≤ C2 * σ * 3 := by gcongr
        have h2' := h2.trans hb
        have ha := abs_le.1 a
        have hb' := abs_le.1 h2'
        rw [abs_le]; constructor <;> linarith
      have a := hD1 γ1 η hη
      calc |(Sh_D U μ 1 ((γ1 : ℂ) + (η : ℂ) * Complex.I)).re -
            (γ1 - quant (rho (((0 : ℝ) : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) (D * N) k)|
          ≤ 10 / 7 * σ + (10 / 7 * σ + C2 * σ * 3) := by
            refine (abs_sub _ _).trans ?_; linarith
        _ ≤ (8 + 3 * (C2 + C3) + C₁) * σ * 1 := by nlinarith
        _ ≤ _ := by gcongr
  · -- the eigenvalue shift
    by_cases hη1 : η ≤ 1
    · have h3 := Sh_T3 H Q hK₁ hη hη1
      rw [← hγ1, ← hσ'] at h3
      refine h3.trans ?_
      have : C3 ≤ 8 + 3 * (C2 + C3) + C₁ := by linarith
      calc 10 * σ * (1 + Sh_KV * Real.sqrt (K₁ + 1)) * Real.sqrt (κ₀ + η)
          = C3 * σ * Real.sqrt (κ₀ + η) := by simp only [C3]; ring
        _ ≤ C3 * σ * Real.sqrt (κ + η) := by gcongr
        _ ≤ _ := by gcongr
    · push_neg at hη1
      have h3 := Sh_T3 H Q hK₁ one_pos (le_refl 1)
      rw [← hγ1, ← hσ'] at h3
      have hRb : ∀ s : ℝ, 0 < s → |∫ t in (0 : ℝ)..1,
          Sh_R μ t ((quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) (D * N) k : ℂ) +
            (s : ℂ) * Complex.I + Sh_m U μ t ((quant (rho ((t : ℂ) • Sh_cd U
              (fun j => (μ j : ℂ)))) (D * N) k : ℂ) + (s : ℂ) * Complex.I))| ≤ 4 * σ := by
        intro s hs
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 4 * σ)
          (f := fun t => Sh_R μ t ((quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) (D * N) k
            : ℂ) + (s : ℂ) * Complex.I + Sh_m U μ t ((quant (rho ((t : ℂ) • Sh_cd U
              (fun j => (μ j : ℂ)))) (D * N) k : ℂ) + (s : ℂ) * Complex.I))) (fun t ht => by
            rw [Set.uIoc_of_le zero_le_one] at ht
            have ht1 : |t| ≤ 1 := Sh_abs01 ⟨ht.1.le, ht.2⟩
            have hz : 0 < ((quant (rho ((t : ℂ) • Sh_cd U (fun j => (μ j : ℂ)))) (D * N) k : ℂ) +
                (s : ℂ) * Complex.I).im := by simpa using hs
            rw [Real.norm_eq_abs, hσ']
            exact Sh_R_bd μ t H.sum_zero H.eig_le ht1 (Sh_basic H ht1 hz).2.2.1.le)
        rw [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at this
        exact this
      have hsqbig : 1 ≤ Real.sqrt (κ + η) := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
      have a1 := hRb 1 one_pos
      have a2 := hRb η hη
      have hb : C3 * σ * Real.sqrt (κ₀ + 1) ≤ C3 * σ * 3 := by gcongr
      have e3 : 10 * σ * (1 + Sh_KV * Real.sqrt (K₁ + 1)) * Real.sqrt (κ₀ + 1) =
          C3 * σ * Real.sqrt (κ₀ + 1) := by simp only [C3]; ring
      rw [e3] at h3
      have x1 := abs_le.1 h3
      have x2 := abs_le.1 a1
      have x3 := abs_le.1 a2
      have hfin : 8 * σ + C3 * σ * 3 ≤ (8 + 3 * (C2 + C3) + C₁) * σ * Real.sqrt (κ + η) := by
        have : 8 * σ + C3 * σ * 3 ≤ (8 + 3 * (C2 + C3) + C₁) * σ := by nlinarith
        calc 8 * σ + C3 * σ * 3 ≤ (8 + 3 * (C2 + C3) + C₁) * σ * 1 := by linarith
          _ ≤ _ := by gcongr
      rw [abs_le]
      constructor <;> linarith

end ShiftCore2

section ShiftRpow

private lemma Sh_sqrt_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have h4 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by nlinarith
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h4
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- `(4D ‖A‖²_HS/N) √(κ + η) ≤ 4D(√C + 1) 𝔯^{1/3} ‖A‖²_HS N^{-(4/3 - ε/2)}` for
`κ ≤ C 𝔯^{2/3} N^{-2/3}` and `η = N^{-2/3+ε} 𝔯^{-1/3}`. -/
private lemma Sh_hs_form {n r κ C ε hs D : ℝ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ C * (r ^ (2 / 3 : ℝ) * n ^ (-(2 / 3 : ℝ)))) (hC : 0 < C) (hε : 0 < ε)
    (hD : 0 ≤ D) :
    4 * D * hs ^ 2 / n * Real.sqrt (κ + n ^ (-(2 / 3 : ℝ) + ε) * r ^ (-(1 / 3 : ℝ))) ≤
      4 * D * (Real.sqrt C + 1) * (r ^ (1 / 3 : ℝ) * hs ^ 2 / n ^ ((4 / 3 : ℝ) - ε / 2)) := by
  have hn0 : 0 < n := by linarith
  have hr0 : 0 < r := by linarith
  have hsq : Real.sqrt (κ + n ^ (-(2 / 3 : ℝ) + ε) * r ^ (-(1 / 3 : ℝ))) ≤
      Real.sqrt C * (r ^ (1 / 3 : ℝ) * n ^ (-(1 / 3 : ℝ))) +
        n ^ (-(1 / 3 : ℝ) + ε / 2) * r ^ (-(1 / 6 : ℝ)) := by
    refine (Sh_sqrt_add hκ0 (by positivity)).trans ?_
    gcongr
    · calc Real.sqrt κ ≤ Real.sqrt (C * (r ^ (2 / 3 : ℝ) * n ^ (-(2 / 3 : ℝ)))) :=
            Real.sqrt_le_sqrt hκ
        _ = _ := by
          rw [Real.sqrt_mul hC.le, Real.sqrt_mul (by positivity), Sh_sqrt_rpow hr0.le,
            Sh_sqrt_rpow hn0.le]
          norm_num
    · rw [Real.sqrt_mul (by positivity), Sh_sqrt_rpow hn0.le, Sh_sqrt_rpow hr0.le]
      apply le_of_eq; congr 2 <;> ring
  -- `n⁻¹ n^{-1/3} ≤ n^{-(4/3 - ε/2)}` and `n⁻¹ n^{-1/3 + ε/2} = n^{-(4/3 - ε/2)}`
  have e1 : n⁻¹ * n ^ (-(1 / 3 : ℝ)) ≤ (n ^ ((4 / 3 : ℝ) - ε / 2))⁻¹ := by
    rw [← Real.rpow_neg hn0.le, ← Real.rpow_neg_one, ← Real.rpow_add hn0]
    exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have e2 : n⁻¹ * n ^ (-(1 / 3 : ℝ) + ε / 2) = (n ^ ((4 / 3 : ℝ) - ε / 2))⁻¹ := by
    rw [← Real.rpow_neg hn0.le, ← Real.rpow_neg_one, ← Real.rpow_add hn0]
    congr 1; ring
  have e3 : r ^ (-(1 / 6 : ℝ)) ≤ r ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  have hA : 0 ≤ 4 * D * hs ^ 2 := by positivity
  calc 4 * D * hs ^ 2 / n * Real.sqrt (κ + n ^ (-(2 / 3 : ℝ) + ε) * r ^ (-(1 / 3 : ℝ)))
      ≤ 4 * D * hs ^ 2 / n * (Real.sqrt C * (r ^ (1 / 3 : ℝ) * n ^ (-(1 / 3 : ℝ))) +
          n ^ (-(1 / 3 : ℝ) + ε / 2) * r ^ (-(1 / 6 : ℝ))) := by gcongr
    _ = 4 * D * hs ^ 2 * (Real.sqrt C * r ^ (1 / 3 : ℝ) * (n⁻¹ * n ^ (-(1 / 3 : ℝ))) +
          (n⁻¹ * n ^ (-(1 / 3 : ℝ) + ε / 2)) * r ^ (-(1 / 6 : ℝ))) := by
        field_simp
    _ ≤ 4 * D * hs ^ 2 * (Real.sqrt C * r ^ (1 / 3 : ℝ) * (n ^ ((4 / 3 : ℝ) - ε / 2))⁻¹ +
          (n ^ ((4 / 3 : ℝ) - ε / 2))⁻¹ * r ^ (1 / 3 : ℝ)) := by
        rw [e2]; gcongr
    _ = _ := by field_simp

/-- For `ε < ε_A` and `N ≥ C^{2/ε_A}`: `C 𝔯^{1/3} ‖A‖²_HS N^{-(4/3 - ε/2)} ≤ N^{-2/3-ε_A} 𝔯^{-1/3}`
under (2.8) [eq:condA2]. -/
private lemma Sh_third {n r hs C ε εA : ℝ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hC : 0 < C) (hε : 0 < ε)
    (hεεA : ε < εA) (hnC : C ^ (2 / εA) ≤ n) (hhs0 : 0 ≤ hs)
    (hhs : hs ≤ n ^ ((1 / 3 : ℝ) - εA) * r ^ (-(1 / 3 : ℝ))) :
    C * (r ^ (1 / 3 : ℝ) * hs ^ 2 / n ^ ((4 / 3 : ℝ) - ε / 2)) ≤
      n ^ (-(2 / 3 : ℝ) - εA) * r ^ (-(1 / 3 : ℝ)) := by
  have hn0 : 0 < n := by linarith
  have hr0 : 0 < r := by linarith
  have hεA : 0 < εA := by linarith
  have h2 : hs ^ 2 ≤ n ^ (2 * ((1 / 3 : ℝ) - εA)) * r ^ (2 * (-(1 / 3 : ℝ))) := by
    calc hs ^ 2 ≤ (n ^ ((1 / 3 : ℝ) - εA) * r ^ (-(1 / 3 : ℝ))) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, Sh_rpow_sq hn0.le, Sh_rpow_sq hr0.le]
  -- `C ≤ n^{ε_A/2} ≤ n^{ε_A - ε/2}`
  have hCn : C ≤ n ^ (εA - ε / 2) := by
    have h1 : C ≤ n ^ (εA / 2) := by
      calc C = (C ^ (2 / εA)) ^ (εA / 2) := by
            rw [← Real.rpow_mul hC.le]; field_simp; simp
        _ ≤ n ^ (εA / 2) := Real.rpow_le_rpow (by positivity) hnC (by positivity)
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  have key : r ^ (1 / 3 : ℝ) * (n ^ (2 * ((1 / 3 : ℝ) - εA)) * r ^ (2 * (-(1 / 3 : ℝ)))) /
      n ^ ((4 / 3 : ℝ) - ε / 2) * n ^ (εA - ε / 2) = n ^ (-(2 / 3 : ℝ) - εA) * r ^ (-(1 / 3 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le]
    have e1 : r ^ (1 / 3 : ℝ) * r ^ (2 * (-(1 / 3 : ℝ))) = r ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_add hr0]; norm_num
    have e2 : n ^ (2 * ((1 / 3 : ℝ) - εA)) * n ^ (-((4 / 3 : ℝ) - ε / 2)) * n ^ (εA - ε / 2) =
        n ^ (-(2 / 3 : ℝ) - εA) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; congr 1; ring
    calc r ^ (1 / 3 : ℝ) * (n ^ (2 * ((1 / 3 : ℝ) - εA)) * r ^ (2 * (-(1 / 3 : ℝ)))) *
          n ^ (-((4 / 3 : ℝ) - ε / 2)) * n ^ (εA - ε / 2)
        = (n ^ (2 * ((1 / 3 : ℝ) - εA)) * n ^ (-((4 / 3 : ℝ) - ε / 2)) * n ^ (εA - ε / 2)) *
          (r ^ (1 / 3 : ℝ) * r ^ (2 * (-(1 / 3 : ℝ)))) := by ring
      _ = _ := by rw [e1, e2]
  calc C * (r ^ (1 / 3 : ℝ) * hs ^ 2 / n ^ ((4 / 3 : ℝ) - ε / 2))
      ≤ n ^ (εA - ε / 2) * (r ^ (1 / 3 : ℝ) *
          (n ^ (2 * ((1 / 3 : ℝ) - εA)) * r ^ (2 * (-(1 / 3 : ℝ)))) /
          n ^ ((4 / 3 : ℝ) - ε / 2)) := by gcongr
    _ = _ := by rw [← key]; ring

end ShiftRpow

/-- (A.34) [modification_shift_eigenvector] of Lemma A.3 [lemma_modification_of_shift]: under
(2.8) [eq:condA2] at `k`, `Δ_ev(z₁) = γ_k - γ_k^sc + O(⟨Λ²⟩² + ⟨Λ²⟩√(κ(γ_k)+η))`, the error is
`O(‖A‖⁴_HS N^{-2} + 𝔯(k)^{1/3} ‖A‖²_HS N^{-4/3+ε/2})`, and it is at most
`N^{-2/3-ε_A} 𝔯(k)^{-1/3}` when `ε < ε_A`. -/
theorem modification_shift_eigenvector (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA)
    (hεA : 0 < εA) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        |shiftEv (lam D N A) (zOne (lam D N A) k ε) -
            (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k)| ≤
          C * (avgSq (lam D N A) ^ 2 + avgSq (lam D N A) *
            Real.sqrt (kappa (lam D N A) (quant (rho (lam D N A)) (D * N) k) + etaK D N k ε)) ∧
        |shiftEv (lam D N A) (zOne (lam D N A) k ε) -
            (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k)| ≤
          C * (hsNorm A ^ 4 / (N : ℝ) ^ 2 +
            rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2)) ∧
        (ε < εA → |shiftEv (lam D N A) (zOne (lam D N A) k ε) -
            (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k)| ≤
          (N : ℝ) ^ (-(2 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨C, hC, N₁, hN₁, hcore⟩ := Sh_core D hD δA εA hδA hεA
  set C' := 4 * (D : ℝ) * (Real.sqrt C + 1) * C
  have hC' : 0 < C' := by
    have : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    positivity
  refine ⟨C + C', by positivity, max N₁ ⌈C' ^ (2 / εA)⌉₊, ?_⟩
  intro N hN A hA k hk hkN hhs
  have hNN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := hN₁.trans hNN₁
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hnC : C' ^ (2 / εA) ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast
    ((le_max_right N₁ ⌈C' ^ (2 / εA)⌉₊).trans hN))
  obtain ⟨r1, -, -, -⟩ := Sh_rk D N k hk hkN
  obtain ⟨e1, -, e3⟩ := hcore N hNN₁ A hA k hk hkN hhs ε
  set err := |shiftEv (lam D N A) (zOne (lam D N A) k ε) -
    (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k)|
  set κ := kappa (lam D N A) (quant (rho (lam D N A)) (D * N) k)
  set σ := avgSq (lam D N A)
  have hσ0 : 0 ≤ σ := by
    have := (Sh_E7 (D : ℝ) (by positivity) hn1 r1 zero_lt_one hεA (Real.sqrt_nonneg _)
      hhs).trans' (Sh_avgSq_lam D N hD hN1 A)
    unfold σ avgSq ntr
    rw [Matrix.trace]
    have hH := lam_isHermitian D N A
    simp only [Matrix.diag, Matrix.mul_apply]
    have : ∀ p q : Idx D N, lam D N A p q * lam D N A q p = ((‖lam D N A p q‖ ^ 2 : ℝ) : ℂ) := by
      intro p q
      have : lam D N A q p = star (lam D N A p q) := by
        have := congrFun (congrFun hH.eq q) p
        simpa [Matrix.conjTranspose_apply] using this.symm
      rw [this, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [this, ← Complex.ofReal_sum]
    rw [show ((Fintype.card (Idx D N) : ℂ))⁻¹ = ((((Fintype.card (Idx D N) : ℝ))⁻¹ : ℝ) : ℂ) by
      push_cast; rfl, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  have hκ0 : 0 ≤ κ := le_min (abs_nonneg _) (abs_nonneg _)
  have hS0 : 0 ≤ Real.sqrt (κ + etaK D N k ε) := Real.sqrt_nonneg _
  have hη : etaK D N k ε = (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * rk D N k ^ (-(1 / 3 : ℝ)) := rfl
  -- the `‖A‖_HS` form
  have hhsf : C * σ * Real.sqrt (κ + etaK D N k ε) ≤
      C' * (rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2)) := by
    have hσle := Sh_avgSq_lam D N hD hN1 A
    have := Sh_hs_form (D := (D : ℝ)) (hs := hsNorm A) hn1 r1 hκ0 e3 hC hε (by positivity)
    rw [← hη] at this
    calc C * σ * Real.sqrt (κ + etaK D N k ε)
        ≤ C * (4 * D * hsNorm A ^ 2 / N * Real.sqrt (κ + etaK D N k ε)) := by
          rw [mul_assoc]; gcongr
      _ ≤ C * (4 * D * (Real.sqrt C + 1) *
          (rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2))) := by
          gcongr
      _ = _ := by simp only [C']; ring
  have hX : 0 ≤ rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2) := by
    positivity
  refine ⟨?_, ?_, fun hεε => ?_⟩
  · calc err ≤ C * σ * Real.sqrt (κ + etaK D N k ε) := e1
      _ ≤ (C + C') * (σ ^ 2 + σ * Real.sqrt (κ + etaK D N k ε)) := by
          nlinarith [mul_nonneg hσ0 hS0, sq_nonneg σ]
  · calc err ≤ C * σ * Real.sqrt (κ + etaK D N k ε) := e1
      _ ≤ C' * (rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2)) := hhsf
      _ ≤ (C + C') * (hsNorm A ^ 4 / (N : ℝ) ^ 2 +
          rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2)) := by
          have : 0 ≤ hsNorm A ^ 4 / (N : ℝ) ^ 2 := by positivity
          nlinarith
  · calc err ≤ C * σ * Real.sqrt (κ + etaK D N k ε) := e1
      _ ≤ C' * (rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2)) := hhsf
      _ ≤ _ := Sh_third hn1 r1 hC' hε hεε hnC (Real.sqrt_nonneg _) hhs


/-- (A.35) [modification_shift_eigenvalue] of Lemma A.3 [lemma_modification_of_shift]: the
same three bounds for `Δ_e(k, η)` of (5.19) [definition_shift_eigenvalue]. -/
theorem modification_shift_eigenvalue (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ) (hδA : 0 < δA)
    (hεA : 0 < εA) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        |shiftE (lam D N A) k ε -
            (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k)| ≤
          C * (avgSq (lam D N A) ^ 2 + avgSq (lam D N A) *
            Real.sqrt (kappa (lam D N A) (quant (rho (lam D N A)) (D * N) k) + etaK D N k ε)) ∧
        |shiftE (lam D N A) k ε -
            (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k)| ≤
          C * (hsNorm A ^ 4 / (N : ℝ) ^ 2 +
            rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2)) ∧
        (ε < εA → |shiftE (lam D N A) k ε -
            (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k)| ≤
          (N : ℝ) ^ (-(2 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨C, hC, N₁, hN₁, hcore⟩ := Sh_core D hD δA εA hδA hεA
  set C' := 4 * (D : ℝ) * (Real.sqrt C + 1) * C
  have hC' : 0 < C' := by
    have : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    positivity
  refine ⟨C + C', by positivity, max N₁ ⌈C' ^ (2 / εA)⌉₊, ?_⟩
  intro N hN A hA k hk hkN hhs
  have hNN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := hN₁.trans hNN₁
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hnC : C' ^ (2 / εA) ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast
    ((le_max_right N₁ ⌈C' ^ (2 / εA)⌉₊).trans hN))
  obtain ⟨r1, -, -, -⟩ := Sh_rk D N k hk hkN
  obtain ⟨-, e1, e3⟩ := hcore N hNN₁ A hA k hk hkN hhs ε
  set err := |shiftE (lam D N A) k ε -
    (quant (rho (lam D N A)) (D * N) k - quant rhoSc (D * N) k)|
  set κ := kappa (lam D N A) (quant (rho (lam D N A)) (D * N) k)
  set σ := avgSq (lam D N A)
  have hσ0 : 0 ≤ σ := by
    have := (Sh_E7 (D : ℝ) (by positivity) hn1 r1 zero_lt_one hεA (Real.sqrt_nonneg _)
      hhs).trans' (Sh_avgSq_lam D N hD hN1 A)
    unfold σ avgSq ntr
    rw [Matrix.trace]
    have hH := lam_isHermitian D N A
    simp only [Matrix.diag, Matrix.mul_apply]
    have : ∀ p q : Idx D N, lam D N A p q * lam D N A q p = ((‖lam D N A p q‖ ^ 2 : ℝ) : ℂ) := by
      intro p q
      have : lam D N A q p = star (lam D N A p q) := by
        have := congrFun (congrFun hH.eq q) p
        simpa [Matrix.conjTranspose_apply] using this.symm
      rw [this, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [this, ← Complex.ofReal_sum]
    rw [show ((Fintype.card (Idx D N) : ℂ))⁻¹ = ((((Fintype.card (Idx D N) : ℝ))⁻¹ : ℝ) : ℂ) by
      push_cast; rfl, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  have hκ0 : 0 ≤ κ := le_min (abs_nonneg _) (abs_nonneg _)
  have hS0 : 0 ≤ Real.sqrt (κ + etaK D N k ε) := Real.sqrt_nonneg _
  have hη : etaK D N k ε = (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * rk D N k ^ (-(1 / 3 : ℝ)) := rfl
  -- the `‖A‖_HS` form
  have hhsf : C * σ * Real.sqrt (κ + etaK D N k ε) ≤
      C' * (rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2)) := by
    have hσle := Sh_avgSq_lam D N hD hN1 A
    have := Sh_hs_form (D := (D : ℝ)) (hs := hsNorm A) hn1 r1 hκ0 e3 hC hε (by positivity)
    rw [← hη] at this
    calc C * σ * Real.sqrt (κ + etaK D N k ε)
        ≤ C * (4 * D * hsNorm A ^ 2 / N * Real.sqrt (κ + etaK D N k ε)) := by
          rw [mul_assoc]; gcongr
      _ ≤ C * (4 * D * (Real.sqrt C + 1) *
          (rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2))) := by
          gcongr
      _ = _ := by simp only [C']; ring
  have hX : 0 ≤ rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2) := by
    positivity
  refine ⟨?_, ?_, fun hεε => ?_⟩
  · calc err ≤ C * σ * Real.sqrt (κ + etaK D N k ε) := e1
      _ ≤ (C + C') * (σ ^ 2 + σ * Real.sqrt (κ + etaK D N k ε)) := by
          nlinarith [mul_nonneg hσ0 hS0, sq_nonneg σ]
  · calc err ≤ C * σ * Real.sqrt (κ + etaK D N k ε) := e1
      _ ≤ C' * (rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2)) := hhsf
      _ ≤ (C + C') * (hsNorm A ^ 4 / (N : ℝ) ^ 2 +
          rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2)) := by
          have : 0 ≤ hsNorm A ^ 4 / (N : ℝ) ^ 2 := by positivity
          nlinarith
  · calc err ≤ C * σ * Real.sqrt (κ + etaK D N k ε) := e1
      _ ≤ C' * (rk D N k ^ (1 / 3 : ℝ) * hsNorm A ^ 2 / (N : ℝ) ^ ((4 / 3 : ℝ) - ε / 2)) := hhsf
      _ ≤ _ := Sh_third hn1 r1 hC' hε hεε hnC (Real.sqrt_nonneg _) hhs

end RBMTransitionEdge

end
