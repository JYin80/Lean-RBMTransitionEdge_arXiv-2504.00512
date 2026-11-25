module

public import RBMTransitionEdge.Flow.CharFlow
public import RBMTransitionEdge.Flow.Endpoint
public import RBMTransitionEdge.Flow.KTheta
public import RBMTransitionEdge.LocalLaw.Dyson

@[expose] public section

/-!
# The time to the real axis and the operator bounds of §3.3

The time `t_c − t₀` of Lemma 3.5 [lem_prop_flow], the flowed `Im m`, the hypotheses of Lemma 3.8
[lem_flow_1], the operator bounds behind (3.67) [Tnorm] for one, two and three resolvents, and
two identities of the closed-form flow (3.10) [eq:deterflow].
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `t_c - t₀ = log(1 + η/Im m)` of Lemma 3.5 [lem_prop_flow] at the start `z = z_{t₀}`: the time
at which the closed-form flow reaches the real axis. -/
def flowTc {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ) : ℝ :=
  Real.log (1 + z.im / (mExt Λ z).im)

/-- `Im m_s = Im m(z_s, Λ_s)` along the flow (3.10) [eq:deterflow], `Λ_s = e^{-s/2} Λ`. -/
def flowIm {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ) (s : ℝ) : ℝ :=
  (mExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s)).im

/-- The hypotheses of Lemma 3.8 [lem_flow_1] on the start `z = z_{t₀}` and the horizon `S`:
`‖A‖ ≤ N^{-δ_A}`, `z ∈ 𝐃(τ)`, `η ≥ c⁻¹ N^{-1/3+τ_e}`, `η / Im m ∈ [c⁻¹ N^{-ε_g}, c N^{-ε_g}]`,
`0 ≤ S < t_c - t₀` and `N η_S Im m_S ≥ N^{C₀ ε_g}`, so that `t₀ + S ≤ t_m`. -/
def flowAdm (D N : ℕ) (δA τ τe εg c C₀ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (S : ℝ) :
    Prop :=
  opNorm A ≤ (N : ℝ) ^ (-δA) ∧ z ∈ specDom τ N ∧ 0 < z.im ∧
    c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ) + τe) ≤ z.im ∧
    c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im ∧
    z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) ∧
    0 ≤ S ∧ S < flowTc (lam D N A) z ∧
    (N : ℝ) ^ (C₀ * εg) ≤ N * (charFlowZ (lam D N A) z S).im * flowIm (lam D N A) z S


section TOp_Fourier

open scoped Matrix.Norms.L2Operator

private lemma TOp_op_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    opNorm A = ‖A‖ := rfl


/-- The primitive root `ζ = e^{2πi/D}`. -/
private def TOp_zeta (D : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / D)

private lemma TOp_zeta_prim (D : ℕ) (hD : D ≠ 0) : IsPrimitiveRoot (TOp_zeta D) D :=
  Complex.isPrimitiveRoot_exp D hD

private lemma TOp_norm_zeta_pow (D : ℕ) (hD : D ≠ 0) (k : ℕ) : ‖TOp_zeta D ^ k‖ = 1 := by
  rw [norm_pow, (TOp_zeta_prim D hD).norm'_eq_one hD, one_pow]

private lemma TOp_star_zeta_pow (D : ℕ) (hD : D ≠ 0) (k : ℕ) :
    star (TOp_zeta D ^ k) * TOp_zeta D ^ k = 1 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    TOp_norm_zeta_pow D hD]
  simp

private lemma TOp_fourierVec_eq (D : ℕ) (l a : Fin D) :
    fourierVec D l a = ((Real.sqrt D : ℂ))⁻¹ * TOp_zeta D ^ ((l : ℕ) * (a : ℕ)) := by
  unfold fourierVec TOp_zeta
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The unitary matrix whose columns are the Fourier vectors `u_l`. -/
private def TOp_F (D : ℕ) : Matrix (Fin D) (Fin D) ℂ := Matrix.of fun a l => fourierVec D l a

private lemma TOp_sqrt_inv_sq (D : ℕ) :
    star ((Real.sqrt D : ℂ))⁻¹ * ((Real.sqrt D : ℂ))⁻¹ = (D : ℂ)⁻¹ := by
  have h : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt h]
  simp

private lemma TOp_F_unitary (D : ℕ) (hD : D ≠ 0) : (TOp_F D)ᴴ * TOp_F D = 1 := by
  have hζ := TOp_zeta_prim D hD
  ext l l'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, TOp_F, Matrix.of_apply,
    TOp_fourierVec_eq, Matrix.one_apply]
  have e : ∀ a : Fin D, star (((Real.sqrt D : ℂ))⁻¹ * TOp_zeta D ^ ((l : ℕ) * (a : ℕ))) *
      (((Real.sqrt D : ℂ))⁻¹ * TOp_zeta D ^ ((l' : ℕ) * (a : ℕ))) =
      (D : ℂ)⁻¹ * (star (TOp_zeta D ^ (l : ℕ)) * TOp_zeta D ^ (l' : ℕ)) ^ (a : ℕ) := by
    intro a
    rw [star_mul', mul_pow, ← star_pow, ← pow_mul, ← pow_mul, ← TOp_sqrt_inv_sq D]
    ring
  simp only [e, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range
    (fun a => (star (TOp_zeta D ^ (l : ℕ)) * TOp_zeta D ^ (l' : ℕ)) ^ a)]
  by_cases hll : l = l'
  · subst hll
    rw [TOp_star_zeta_pow D hD]
    simp [hD]
  · simp only [hll, ↓reduceIte]
    set r := star (TOp_zeta D ^ (l : ℕ)) * TOp_zeta D ^ (l' : ℕ) with hr
    have hrD : r ^ D = 1 := by
      rw [hr, mul_pow, ← star_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ), mul_comm (l' : ℕ),
        pow_mul, pow_mul, hζ.pow_eq_one, one_pow, one_pow, star_one, one_mul]
    have hr1 : r ≠ 1 := by
      intro h1
      have : TOp_zeta D ^ (l' : ℕ) = TOp_zeta D ^ (l : ℕ) := by
        have h2 := congrArg (fun x => TOp_zeta D ^ (l : ℕ) * x) h1
        simp only [mul_one] at h2
        rw [hr, ← mul_assoc, mul_comm (TOp_zeta D ^ (l : ℕ)), TOp_star_zeta_pow D hD, one_mul] at h2
        exact h2
      exact hll (Fin.ext (hζ.pow_inj l.isLt l'.isLt this.symm))
    have hg := geom_sum_mul r D
    rw [hrD, sub_self] at hg
    have : ∑ i ∈ Finset.range D, r ^ i = 0 :=
      (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hr1)
    rw [this, mul_zero]

private lemma TOp_F_unitary' (D : ℕ) (hD : D ≠ 0) : TOp_F D * (TOp_F D)ᴴ = 1 :=
  mul_eq_one_comm.mp (TOp_F_unitary D hD)

private lemma TOp_F_norm (D : ℕ) (hD : D ≠ 0) : ‖TOp_F D‖ ≤ 1 := by
  have : Nonempty (Fin D) := ⟨⟨0, Nat.pos_of_ne_zero hD⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (TOp_F D)
  rw [TOp_F_unitary D hD, norm_one] at h1
  nlinarith [norm_nonneg (TOp_F D)]

/-- A matrix with eigenvectors `u_l` and eigenvalues `μ_l` is `F diag(μ) F^*`. -/
private lemma TOp_circ (D : ℕ) (hD : D ≠ 0) (B : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ)
    (hB : ∀ l, B *ᵥ fourierVec D l = μ l • fourierVec D l) :
    B = TOp_F D * diagonal μ * (TOp_F D)ᴴ := by
  have h1 : B * TOp_F D = TOp_F D * diagonal μ := by
    ext a l
    have := congrFun (hB l) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, TOp_F, Matrix.of_apply]
    rw [this, mul_comm]
  calc B = B * (TOp_F D * (TOp_F D)ᴴ) := by rw [TOp_F_unitary' D hD, Matrix.mul_one]
    _ = TOp_F D * diagonal μ * (TOp_F D)ᴴ := by rw [← Matrix.mul_assoc, h1]

private lemma TOp_conjF_norm (D : ℕ) (hD : D ≠ 0) (X : Matrix (Fin D) (Fin D) ℂ) :
    ‖TOp_F D * X * (TOp_F D)ᴴ‖ = ‖X‖ := by
  have hF := TOp_F_norm D hD
  have hF' : ‖(TOp_F D)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hF
  apply le_antisymm
  · calc ‖TOp_F D * X * (TOp_F D)ᴴ‖ ≤ ‖TOp_F D‖ * ‖X‖ * ‖(TOp_F D)ᴴ‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖X‖ * 1 := by gcongr
      _ = ‖X‖ := by ring
  · have e : X = (TOp_F D)ᴴ * (TOp_F D * X * (TOp_F D)ᴴ) * TOp_F D := by
      simp only [← Matrix.mul_assoc, TOp_F_unitary D hD, Matrix.one_mul]
      rw [Matrix.mul_assoc, TOp_F_unitary D hD, Matrix.mul_one]
    calc ‖X‖ = ‖(TOp_F D)ᴴ * (TOp_F D * X * (TOp_F D)ᴴ) * TOp_F D‖ := by rw [← e]
      _ ≤ ‖(TOp_F D)ᴴ‖ * ‖TOp_F D * X * (TOp_F D)ᴴ‖ * ‖TOp_F D‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖TOp_F D * X * (TOp_F D)ᴴ‖ * 1 := by gcongr
      _ = _ := by ring

/-- For `B` with eigenvectors `u_l` and eigenvalues `μ_l ≠ 1`: `1 - B` is invertible,
`(1 - B)⁻¹ = F diag((1 - μ)⁻¹) F^*`, and `‖(1 - B)⁻¹‖ = max_l |1 - μ_l|⁻¹`. -/
private lemma TOp_circ_inv (D : ℕ) (hD : D ≠ 0) (B : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ)
    (hB : ∀ l, B *ᵥ fourierVec D l = μ l • fourierVec D l) (hμ : ∀ l, 1 - μ l ≠ 0) :
    (1 - B).det ≠ 0 ∧
      (1 - B)⁻¹ = TOp_F D * diagonal (fun l => (1 - μ l)⁻¹) * (TOp_F D)ᴴ ∧
      opNorm ((1 - B)⁻¹) = ‖fun l => (1 - μ l)⁻¹‖ := by
  have hc := TOp_circ D hD B μ hB
  have h1 : 1 - B = TOp_F D * diagonal (fun l => 1 - μ l) * (TOp_F D)ᴴ := by
    have : diagonal (fun l => 1 - μ l) = 1 - diagonal μ := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, TOp_F_unitary' D hD, ← hc]
  have hinv : (1 - B)⁻¹ = TOp_F D * diagonal (fun l => (1 - μ l)⁻¹) * (TOp_F D)ᴴ := by
    rw [h1]
    apply Matrix.inv_eq_right_inv
    have e : TOp_F D * diagonal (fun l => 1 - μ l) * (TOp_F D)ᴴ *
        (TOp_F D * diagonal (fun l => (1 - μ l)⁻¹) * (TOp_F D)ᴴ) =
        TOp_F D * (diagonal (fun l => 1 - μ l) * ((TOp_F D)ᴴ * TOp_F D) *
          diagonal (fun l => (1 - μ l)⁻¹)) * (TOp_F D)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, TOp_F_unitary D hD, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    have : (fun l => (1 - μ l) * (1 - μ l)⁻¹) = fun _ => (1 : ℂ) := by
      funext l; exact mul_inv_cancel₀ (hμ l)
    rw [this, Matrix.diagonal_one, Matrix.mul_one, TOp_F_unitary' D hD]
  refine ⟨?_, hinv, ?_⟩
  · rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hdet : (TOp_F D).det * ((TOp_F D)ᴴ).det = 1 := by
      rw [← Matrix.det_mul, TOp_F_unitary' D hD, Matrix.det_one]
    have : (TOp_F D).det * (∏ l, (1 - μ l)) * ((TOp_F D)ᴴ).det = ∏ l, (1 - μ l) := by
      linear_combination (∏ l, (1 - μ l)) * hdet
    rw [this]
    exact Finset.prod_ne_zero_iff.2 fun l _ => hμ l
  · rw [hinv, TOp_op_eq, TOp_conjF_norm D hD, Matrix.l2_opNorm_diagonal]

/-- `Σ_b ζ^{lb} = 0` for `l ≠ 0`. -/
private lemma TOp_sum_zeta (D : ℕ) (hD : D ≠ 0) (l : Fin D) (hl : (l : ℕ) ≠ 0) :
    ∑ b : Fin D, TOp_zeta D ^ ((l : ℕ) * (b : ℕ)) = 0 := by
  have hζ := TOp_zeta_prim D hD
  set r := TOp_zeta D ^ (l : ℕ) with hr
  have e : ∀ b : Fin D, TOp_zeta D ^ ((l : ℕ) * (b : ℕ)) = r ^ (b : ℕ) := fun b => by
    rw [hr, ← pow_mul]
  simp only [e]
  rw [Fin.sum_univ_eq_sum_range (fun b => r ^ b) D]
  have hrD : r ^ D = 1 := by
    rw [hr, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hr1 : r ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hl l.isLt
  have hg := geom_sum_mul r D
  rw [hrD, sub_self] at hg
  exact (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hr1)

/-- The block profile `P_θ` acts on `u_0` as the identity and on `u_l`, `l ≠ 0`, as `θ`. -/
private lemma TOp_P_eig (D : ℕ) (hD : D ≠ 0) (θ : ℝ) (l : Fin D) :
    PTheta D θ *ᵥ fourierVec D l =
      (if (l : ℕ) = 0 then (1 : ℂ) else (θ : ℂ)) • fourierVec D l := by
  have : NeZero D := ⟨hD⟩
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  have hJ : ∀ a : Fin D, ((Matrix.of fun _ _ => (1 : ℂ)) *ᵥ fourierVec D l) a =
      ∑ b, fourierVec D l b := fun a => by simp [Matrix.mulVec, dotProduct]
  have hsum : ∑ b, fourierVec D l b =
      ((Real.sqrt D : ℂ))⁻¹ * ∑ b : Fin D, TOp_zeta D ^ ((l : ℕ) * (b : ℕ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => TOp_fourierVec_eq D l b
  ext a
  simp only [PTheta, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, hJ, hsum]
  by_cases hl : (l : ℕ) = 0
  · simp only [hl, ↓reduceIte, zero_mul, pow_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [TOp_fourierVec_eq, hl]
    simp only [zero_mul, pow_zero, mul_one]
    push_cast
    field_simp
    ring
  · simp only [hl, ↓reduceIte, TOp_sum_zeta D hD l hl, mul_zero, add_zero]

/-- `(1 - B')⁻¹ B = F diag((1 - ν)⁻¹ μ) F^*` for `B`, `B'` with the Fourier eigenvectors and
eigenvalues `μ`, `ν`, `1 - ν_l ≠ 0`. -/
private lemma TOp_K_form (D : ℕ) (hD : D ≠ 0) (B B' : Matrix (Fin D) (Fin D) ℂ)
    (μ ν : Fin D → ℂ) (hB : ∀ l, B *ᵥ fourierVec D l = μ l • fourierVec D l)
    (hB' : ∀ l, B' *ᵥ fourierVec D l = ν l • fourierVec D l) (hν : ∀ l, 1 - ν l ≠ 0) :
    (1 - B')⁻¹ * B = TOp_F D * diagonal (fun l => (1 - ν l)⁻¹ * μ l) * (TOp_F D)ᴴ := by
  obtain ⟨-, hinv, -⟩ := TOp_circ_inv D hD B' ν hB' hν
  rw [hinv, TOp_circ D hD B μ hB]
  have e : TOp_F D * diagonal (fun l => (1 - ν l)⁻¹) * (TOp_F D)ᴴ *
      (TOp_F D * diagonal μ * (TOp_F D)ᴴ) =
      TOp_F D * (diagonal (fun l => (1 - ν l)⁻¹) * ((TOp_F D)ᴴ * TOp_F D) * diagonal μ) *
        (TOp_F D)ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [e, TOp_F_unitary D hD, Matrix.mul_one, Matrix.diagonal_mul_diagonal]

end TOp_Fourier


/-- The elementary inequality behind the disc lemma: for `q > 0`, `θ ∈ [0, 1]`, `0 < r` with
`r (1 + q) ≤ 1`, and `u² ≤ e ≤ r²`, one has `1 + (1 - q - 2θ) u - (1 - θ)(θ + q) e ≥ 0`. -/
private lemma TOp_G_nonneg (q θ r u e : ℝ) (hq : 0 < q) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hr0 : 0 < r) (hr1 : r * (1 + q) ≤ 1) (hu : u ^ 2 ≤ e) (he : e ≤ r ^ 2) :
    0 ≤ 1 + (1 - q - 2 * θ) * u - (1 - θ) * (θ + q) * e := by
  have hrr : r ≤ 1 := by nlinarith
  have hur : u ≤ r := by nlinarith [sq_nonneg (u - r), sq_nonneg (u + r)]
  have hul : -r ≤ u := by nlinarith [sq_nonneg (u - r), sq_nonneg (u + r)]
  have hk : 0 ≤ (1 - θ) * (θ + q) := mul_nonneg (by linarith) (by linarith)
  have hGm : 0 ≤ 1 - (1 - q - 2 * θ) * r - (1 - θ) * (θ + q) * r ^ 2 := by
    have : 1 - (1 - q - 2 * θ) * r - (1 - θ) * (θ + q) * r ^ 2 =
        (1 - r) * (1 + q * r) + θ * r * (2 - r + q * r) + θ ^ 2 * r ^ 2 := by ring
    rw [this]
    have h1 : 0 ≤ (1 - r) * (1 + q * r) := mul_nonneg (by linarith) (by positivity)
    have h2 : 0 ≤ θ * r * (2 - r + q * r) := mul_nonneg (by positivity) (by nlinarith)
    positivity
  have hGp : 0 ≤ 1 + (1 - q - 2 * θ) * r - (1 - θ) * (θ + q) * r ^ 2 := by
    have : 1 + (1 - q - 2 * θ) * r - (1 - θ) * (θ + q) * r ^ 2 =
        (1 - (1 + q) * r) + r * (2 - (1 + q) * r) * (1 - θ) + r ^ 2 * (1 - θ) ^ 2 := by ring
    rw [this]
    have h1 : 0 ≤ 1 - (1 + q) * r := by linarith
    have h2 : 0 ≤ r * (2 - (1 + q) * r) * (1 - θ) :=
      mul_nonneg (mul_nonneg hr0.le (by nlinarith)) (by linarith)
    positivity
  have key : 2 * r * (1 + (1 - q - 2 * θ) * u - (1 - θ) * (θ + q) * r ^ 2) =
      (r - u) * (1 - (1 - q - 2 * θ) * r - (1 - θ) * (θ + q) * r ^ 2) +
        (r + u) * (1 + (1 - q - 2 * θ) * r - (1 - θ) * (θ + q) * r ^ 2) := by ring
  have h3 : 0 ≤ 2 * r * (1 + (1 - q - 2 * θ) * u - (1 - θ) * (θ + q) * r ^ 2) := by
    rw [key]
    exact add_nonneg (mul_nonneg (by linarith) hGm) (mul_nonneg (by linarith) hGp)
  have h4 : 0 ≤ 1 + (1 - q - 2 * θ) * u - (1 - θ) * (θ + q) * r ^ 2 := by
    by_contra hneg
    have hneg := not_le.1 hneg
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left he hk]

/-- For `q > 0`, `θ ∈ [0, 1]` and `|d| ≤ e^{-q}`: `1 - θ d ≠ 0` and `ξ = q d/(1 - θ d)` satisfies
`|ξ| ≤ 1` and `|ξ - (1 - q)/2| ≤ (1 + q)/2`. This is the disc lemma behind the operator bounds
(3.67) [Tnorm]: the image of the disc `|d| ≤ e^{-q}` under `d ↦ q d/(1 - θ d)` is a disc symmetric
about `ℝ` whose real diameter lies in `[-q, 1] ∩ [-1, 1]`-compatible position for every `q > 0`. -/
private lemma TOp_disk (q θ : ℝ) (hq : 0 < q) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (d : ℂ)
    (hd : ‖d‖ ≤ Real.exp (-q)) :
    1 - (θ : ℂ) * d ≠ 0 ∧ ‖(q : ℂ) * ((1 - (θ : ℂ) * d)⁻¹ * d)‖ ≤ 1 ∧
      ‖(q : ℂ) * ((1 - (θ : ℂ) * d)⁻¹ * d) - (((1 - q) / 2 : ℝ) : ℂ)‖ ≤ (1 + q) / 2 := by
  set r := Real.exp (-q) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r * (1 + q) ≤ 1 := by
    have h1 : q + 1 ≤ Real.exp q := Real.add_one_le_exp q
    have h2 : r * Real.exp q = 1 := by rw [hr, ← Real.exp_add]; simp
    nlinarith
  have hrr : r < 1 := by nlinarith
  have hθd : ‖(θ : ℂ) * d‖ ≤ θ * r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ₀]
    exact mul_le_mul_of_nonneg_left hd hθ₀
  have hδ : 1 - r ≤ ‖1 - (θ : ℂ) * d‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((θ : ℂ) * d)
    rw [norm_one] at h
    nlinarith
  have hδpos : 0 < ‖1 - (θ : ℂ) * d‖ := by linarith
  have hne : 1 - (θ : ℂ) * d ≠ 0 := norm_pos_iff.1 hδpos
  refine ⟨hne, ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, norm_mul, norm_inv]
    rw [← div_eq_inv_mul, ← mul_div_assoc, div_le_one hδpos]
    nlinarith
  · have e : (q : ℂ) * ((1 - (θ : ℂ) * d)⁻¹ * d) - (((1 - q) / 2 : ℝ) : ℂ) =
        ((q : ℂ) * d - (((1 - q) / 2 : ℝ) : ℂ) * (1 - (θ : ℂ) * d)) * (1 - (θ : ℂ) * d)⁻¹ := by
      field_simp
    rw [e, norm_mul, norm_inv, ← div_eq_mul_inv, div_le_iff₀ hδpos]
    have hsq : ‖(q : ℂ) * d - (((1 - q) / 2 : ℝ) : ℂ) * (1 - (θ : ℂ) * d)‖ ^ 2 ≤
        ((1 + q) / 2 * ‖1 - (θ : ℂ) * d‖) ^ 2 := by
      rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      have hnd : d.re * d.re + d.im * d.im ≤ r ^ 2 := by
        have := Complex.sq_norm d
        rw [Complex.normSq_apply] at this
        nlinarith [norm_nonneg d]
      have hG := TOp_G_nonneg q θ r d.re (d.re * d.re + d.im * d.im) hq hθ₀ hθ₁ hr0 hr1
        (by nlinarith [sq_nonneg d.im]) hnd
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.one_im]
      nlinarith [mul_nonneg hq.le hG]
    exact abs_le_of_sq_le_sq' (by simpa using hsq) (by positivity) |>.2


section TOp_Bound

variable {ι : Type*} [Fintype ι]

/-- `∑ᵢⱼ |Aᵢⱼ|²`. -/
private def TOp_S (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private lemma TOp_S_conj (A : Matrix ι ι ℂ) : TOp_S Aᴴ = TOp_S A := by
  unfold TOp_S
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

/-- Cauchy–Schwarz for the trace pairing: `|tr(XY)|² ≤ (∑|X_{ij}|²)(∑|Y_{ij}|²)`. -/
private lemma TOp_tr_mul_le (X Y : Matrix ι ι ℂ) :
    ‖(X * Y).trace‖ ≤ Real.sqrt (TOp_S X) * Real.sqrt (TOp_S Y) := by
  have h1 : ‖(X * Y).trace‖ ≤ ∑ p : ι × ι, ‖X p.1 p.2‖ * ‖Y p.2 p.1‖ := by
    rw [Matrix.trace]
    calc ‖∑ i, (X * Y).diag i‖ ≤ ∑ i, ‖(X * Y).diag i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Y j i‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [Matrix.diag, Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
      _ = _ := by rw [Fintype.sum_prod_type]
  refine h1.trans ?_
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ι × ι))
    (fun p => ‖X p.1 p.2‖) (fun p => ‖Y p.2 p.1‖)
  have e1 : ∑ p : ι × ι, ‖X p.1 p.2‖ ^ 2 = TOp_S X := by
    rw [Fintype.sum_prod_type]; rfl
  have e2 : ∑ p : ι × ι, ‖Y p.2 p.1‖ ^ 2 = TOp_S Y := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rw [e1, e2] at h2
  exact h2

private lemma TOp_trace_mul_conj (Z : Matrix ι ι ℂ) : (Z * Zᴴ).trace = (TOp_S Z : ℂ) := by
  unfold TOp_S
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- `D ⟨X⟩ = N⁻¹ tr X` on `Idx D N`. -/
private lemma TOp_D_ntr (D N : ℕ) (hD : D ≠ 0) (X : Matrix (Idx D N) (Idx D N) ℂ) :
    (D : ℂ) * ntr X = (N : ℂ)⁻¹ * X.trace := by
  unfold ntr
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  by_cases hN : (N : ℂ) = 0
  · simp [hN]
  · field_simp

/-- For `Im z > 0` and `z₁ ∈ {z, z̄}`: `∑ |M(z₁)_{pq}|² = D N Im m/(Im m + η)`, by (A.3)
[equation_z_im_m]. -/
private lemma TOp_S_MExt (D N : ℕ) (hD : D ≠ 0) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (z₁ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) :
    TOp_S (MExt (lam D N A) z₁) = D * N * ((mExt (lam D N A) z).im /
      ((mExt (lam D N A) z).im + z.im)) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, Nat.pos_of_ne_zero hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hm : mExt (lam D N A) z = mSol (lam D N A) z := by simp only [mExt, hz, ↓reduceIte]
  have hM : MExt (lam D N A) z = MSol (lam D N A) z := by rw [MExt, MSol, hm]
  have h1 := (equation_z_im_m (lam D N A) hΛ z hz).1
  rw [hm]
  set y := (mSol (lam D N A) z).im
  have hS : TOp_S (MExt (lam D N A) z) = D * N * (y / (y + z.im)) := by
    have hcard : ((D * N : ℕ) : ℂ) ≠ 0 := by
      have := (Fintype.card_pos (α := Idx D N)).ne'
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
      exact_mod_cast this
    have e : (TOp_S (MSol (lam D N A) z) : ℂ) =
        ((D * N : ℕ) : ℂ) * ((y / (y + z.im) : ℝ) : ℂ) := by
      rw [← TOp_trace_mul_conj, ← h1]
      unfold ntr
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    have e' : TOp_S (MSol (lam D N A) z) = ((D * N : ℕ) : ℝ) * (y / (y + z.im)) := by
      exact_mod_cast e
    rw [hM, e']
    push_cast
    ring
  rcases h₁ with rfl | rfl
  · exact hS
  · rw [(mExt_conj (lam D N A) hΛ z hz.ne').2, TOp_S_conj]
    exact hS

/-- Every eigenvalue `λ̂_l` of `M̂(z₁, z₂)`, `z₁, z₂ ∈ {z, z̄}`, `Im z > 0`, has modulus at most
`Im m/(Im m + η) = e^{-q}`, `q = log(1 + η/Im m)`: `λ̂_l = ⟨M(z₁) V^* M(z₂) V⟩` for the diagonal
unitary `V = diag(e^{2πi l a / D})`, and Cauchy–Schwarz with (A.3) [equation_z_im_m] bounds it by
`√(⟨M₁M₁^*⟩⟨M₂^*M₂⟩)`. -/
private lemma TOp_circEig_le (D N : ℕ) (hD : D ≠ 0) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im) (hm : 0 < (mExt (lam D N A) z).im)
    (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (l : Fin D) :
    ‖circEig (Mhat (lam D N A) z₁ z₂) l‖ ≤
      (mExt (lam D N A) z).im / ((mExt (lam D N A) z).im + z.im) := by
  have : NeZero D := ⟨hD⟩
  set r := (mExt (lam D N A) z).im / ((mExt (lam D N A) z).im + z.im) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  set M₁ := MExt (lam D N A) z₁
  set M₂ := MExt (lam D N A) z₂
  set u := fourierVec D l with hu
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hun : ∀ a : Fin D, ‖u a‖ = (Real.sqrt D)⁻¹ := by
    intro a
    rw [hu, TOp_fourierVec_eq, norm_mul, TOp_norm_zeta_pow D hD, mul_one, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hV₁ : (Matrix.diagonal fun p : Idx D N => star (u p.1)) =
      ∑ a, star (u a) • Ea D N a := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.smul_apply, Ea, Matrix.diagonal_apply, smul_eq_mul]
    by_cases hpq : p = q
    · subst hpq; simp
    · simp [hpq]
  have hV₂ : (Matrix.diagonal fun p : Idx D N => u p.1) = ∑ b, u b • Ea D N b := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.smul_apply, Ea, Matrix.diagonal_apply, smul_eq_mul]
    by_cases hpq : p = q
    · subst hpq; simp
    · simp [hpq]
  have hc : circEig (Mhat (lam D N A) z₁ z₂) l =
      (N : ℂ)⁻¹ * (M₁ * (Matrix.diagonal fun p : Idx D N => star (u p.1)) * M₂ *
        (Matrix.diagonal fun p : Idx D N => u p.1)).trace := by
    unfold circEig Mhat
    simp only [TOp_D_ntr D N hD]
    rw [hV₁, hV₂]
    simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hu]
    ring
  have hS₁ := TOp_S_MExt D N hD hN A z hz z₁ h₁
  have hS₂ := TOp_S_MExt D N hD hN A z hz z₂ h₂
  set V₁ : Matrix (Idx D N) (Idx D N) ℂ := Matrix.diagonal fun p : Idx D N => star (u p.1)
  set V₂ : Matrix (Idx D N) (Idx D N) ℂ := Matrix.diagonal fun p : Idx D N => u p.1
  have hq : ((Real.sqrt D)⁻¹) ^ 2 = (D : ℝ)⁻¹ := by rw [inv_pow, Real.sq_sqrt hDpos.le]
  have hS : TOp_S (V₁ * M₂ * V₂) = ((D : ℝ)⁻¹) ^ 2 * TOp_S M₂ := by
    unfold TOp_S
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [V₁, V₂, Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_star, hun]
    rw [← hq]
    ring
  have htr := TOp_tr_mul_le M₁ (V₁ * M₂ * V₂)
  have e : M₁ * V₁ * M₂ * V₂ = M₁ * (V₁ * M₂ * V₂) := by simp only [Matrix.mul_assoc]
  have hsq : Real.sqrt (TOp_S (V₁ * M₂ * V₂)) = (D : ℝ)⁻¹ * Real.sqrt (TOp_S M₂) := by
    rw [hS, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hDNr : Real.sqrt (D * N * r) * Real.sqrt (D * N * r) = D * N * r :=
    Real.mul_self_sqrt (mul_nonneg (by positivity) hr0)
  rw [hc, e, norm_mul, norm_inv, Complex.norm_natCast]
  rw [hsq] at htr
  calc (N : ℝ)⁻¹ * ‖(M₁ * (V₁ * M₂ * V₂)).trace‖
      ≤ (N : ℝ)⁻¹ * (Real.sqrt (TOp_S M₁) * ((D : ℝ)⁻¹ * Real.sqrt (TOp_S M₂))) := by
        gcongr
    _ = (N : ℝ)⁻¹ * (D : ℝ)⁻¹ * (Real.sqrt (D * N * r) * Real.sqrt (D * N * r)) := by
        rw [hS₁, hS₂]
        ring
    _ = r := by
        rw [hDNr]
        field_simp


end TOp_Bound

/-- `Im m > 0` for `m = m(z, Λ)` at `Im z > 0` ((2.16) [self_m], Definition 2.7 [defn_Mm]). -/
private lemma TOp_im_m_pos {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) : 0 < (mExt Λ z).im := by
  obtain ⟨-, -, h⟩ := MExt_spec Λ hΛ z hz.ne'
  exact (mul_pos_iff_of_pos_right hz).1 h

/-- `t_c - t₀ > 0` at `Im z > 0`. -/
private lemma TOp_flowTc_pos {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) : 0 < flowTc Λ z :=
  Real.log_pos (by have := div_pos hz (TOp_im_m_pos Λ hΛ z hz); linarith)

/-- `e^{-(t_c - t₀)} = Im m/(Im m + η)` at `Im z > 0`. -/
private lemma TOp_exp_flowTc {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    Real.exp (-flowTc Λ z) = (mExt Λ z).im / ((mExt Λ z).im + z.im) := by
  have hm := TOp_im_m_pos Λ hΛ z hz
  have hq : 0 < 1 + z.im / (mExt Λ z).im := by have := div_pos hz hm; linarith
  rw [flowTc, Real.exp_neg, Real.exp_log hq]
  field_simp

/-- The Fourier vectors are eigenvectors of `M̂(z₁, z₂)` for every `D ≥ 1` ((A.25) [eq_lambdak];
for `D = 1` the matrix is `1 × 1`). -/
private lemma TOp_eigvec (D N : ℕ) [NeZero D] (A : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0) (l : Fin D) :
    Mhat (lam D N A) z₁ z₂ *ᵥ fourierVec D l =
      circEig (Mhat (lam D N A) z₁ z₂) l • fourierVec D l := by
  by_cases hD : 2 ≤ D
  · exact Mhat_eigvec D hD N A z₁ z₂ h₁ h₂ l
  · obtain rfl : D = 1 := by have := NeZero.pos D; omega
    have hl : l = 0 := Subsingleton.elim _ _
    subst hl
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    have hu : fourierVec 1 0 0 = 1 := by simp [fourierVec]
    simp [Matrix.mulVec, dotProduct, circEig, hu]

/-- `1 - M̂ P_θ` is invertible and `K_θ(z₁, z₂) = F diag(κ) F^*` for the Fourier unitary `F`, with
`|q κ_l| ≤ 1` and `|q κ_l - (1 - q)/2| ≤ (1 + q)/2` for `q = log(1 + η/Im m)`, `z₁, z₂ ∈ {z, z̄}`:
the eigenvalues of `M̂(z₁, z₂)` have modulus at most `e^{-q}` and `P_θ` has eigenvalues `1` and `θ`,
so the disc lemma applies to each `λ̂_l`. -/
private lemma TOp_Kdiag (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) :
    (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
      ∃ κ : Fin D → ℂ, KTheta (lam D N A) θ z₁ z₂ = TOp_F D * diagonal κ * (TOp_F D)ᴴ ∧
        ∀ l, ‖((flowTc (lam D N A) z : ℝ) : ℂ) * κ l‖ ≤ 1 ∧
          ‖((flowTc (lam D N A) z : ℝ) : ℂ) * κ l -
            (((1 - flowTc (lam D N A) z) / 2 : ℝ) : ℂ)‖ ≤ (1 + flowTc (lam D N A) z) / 2 := by
  have hD : D ≠ 0 := NeZero.ne D
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have : Nonempty (Idx D N) := ⟨(⟨0, Nat.pos_of_ne_zero hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hm := TOp_im_m_pos (lam D N A) hΛ z hz
  have hq := TOp_flowTc_pos (lam D N A) hΛ z hz
  have hr := TOp_exp_flowTc (lam D N A) hΛ z hz
  have hz₁ : z₁.im ≠ 0 := by rcases h₁ with rfl | rfl <;> simp [hz.ne']
  have hz₂ : z₂.im ≠ 0 := by rcases h₂ with rfl | rfl <;> simp [hz.ne']
  set B := Mhat (lam D N A) z₁ z₂ with hB
  set q := flowTc (lam D N A) z with hqdef
  set d : Fin D → ℂ := fun l => circEig B l with hd
  have hBu : ∀ l, B *ᵥ fourierVec D l = d l • fourierVec D l := fun l =>
    TOp_eigvec D N A z₁ z₂ hz₁ hz₂ l
  have hdle : ∀ l, ‖d l‖ ≤ Real.exp (-q) := fun l => by
    rw [hr]
    exact TOp_circEig_le D N hD hN A z hz hm z₁ z₂ h₁ h₂ l
  set t : Fin D → ℝ := fun l => if (l : ℕ) = 0 then 1 else θ with ht
  have ht₀ : ∀ l, 0 ≤ t l := fun l => by
    simp only [ht]
    split_ifs <;> linarith
  have ht₁ : ∀ l, t l ≤ 1 := fun l => by
    simp only [ht]
    split_ifs <;> linarith
  set ν : Fin D → ℂ := fun l => (t l : ℂ) * d l with hν
  have hBP : ∀ l, (B * PTheta D θ) *ᵥ fourierVec D l = ν l • fourierVec D l := by
    intro l
    rw [← Matrix.mulVec_mulVec, TOp_P_eig D hD, Matrix.mulVec_smul, hBu l, smul_smul]
    have : (if (l : ℕ) = 0 then (1 : ℂ) else (θ : ℂ)) = (t l : ℂ) := by
      change _ = ((if (l : ℕ) = 0 then 1 else θ : ℝ) : ℂ)
      split_ifs <;> simp
    rw [this, hν]
  have hdisk := fun l => TOp_disk q (t l) hq (ht₀ l) (ht₁ l) (d l) (hdle l)
  have hne : ∀ l, 1 - ν l ≠ 0 := fun l => (hdisk l).1
  obtain ⟨hdet, -, -⟩ := TOp_circ_inv D hD (B * PTheta D θ) ν hBP hne
  refine ⟨hdet, fun l => (1 - ν l)⁻¹ * d l, TOp_K_form D hD B (B * PTheta D θ) d ν hBu hBP hne,
    fun l => ⟨(hdisk l).2.1, (hdisk l).2.2⟩⟩


section TOp_Norms

open scoped Matrix.Norms.L2Operator

/-- The operator norm bounds the Euclidean norm of the image: `‖X v‖² ≤ ‖X‖² ‖v‖²`. -/
private lemma TOp_vec_sq {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (v : n → ℂ) :
    ∑ i, ‖(X *ᵥ v) i‖ ^ 2 ≤ opNorm X ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) X).le_opNorm (WithLp.toLp 2 v)
  rw [Matrix.toEuclideanCLM_toLp] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa [opNorm] using h2

/-- The Hilbert–Schmidt norm as a Euclidean norm on `n × n`. -/
private lemma TOp_hs_eq {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    hsNorm A = ‖(WithLp.toLp 2 (fun p : n × n => A p.1 p.2) : EuclideanSpace ℂ (n × n))‖ := by
  rw [EuclideanSpace.norm_eq, hsNorm, Fintype.sum_prod_type]

/-- The triangle inequality for the Hilbert–Schmidt norm. -/
private lemma TOp_hs_add_le {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    hsNorm (A + B) ≤ hsNorm A + hsNorm B := by
  rw [TOp_hs_eq, TOp_hs_eq, TOp_hs_eq]
  exact norm_add_le (WithLp.toLp 2 (fun p : n × n => A p.1 p.2) : EuclideanSpace ℂ (n × n))
    (WithLp.toLp 2 (fun p : n × n => B p.1 p.2))

/-- `‖X V‖_HS ≤ ‖X‖ ‖V‖_HS`. -/
private lemma TOp_hs_mul_le {n : Type*} [Fintype n] [DecidableEq n] (X V : Matrix n n ℂ) :
    hsNorm (X * V) ≤ opNorm X * hsNorm V := by
  have hX : 0 ≤ opNorm X := norm_nonneg _
  have key : ∑ i, ∑ j, ‖(X * V) i j‖ ^ 2 ≤ opNorm X ^ 2 * ∑ i, ∑ j, ‖V i j‖ ^ 2 := by
    calc ∑ i, ∑ j, ‖(X * V) i j‖ ^ 2 = ∑ j, ∑ i, ‖(X *ᵥ fun k => V k j) i‖ ^ 2 := by
          rw [Finset.sum_comm]; rfl
      _ ≤ ∑ j, opNorm X ^ 2 * ∑ i, ‖V i j‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => TOp_vec_sq X _
      _ = opNorm X ^ 2 * ∑ i, ∑ j, ‖V i j‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
  unfold hsNorm
  rw [← Real.sqrt_sq hX, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt key

/-- `‖V X‖_HS ≤ ‖X‖ ‖V‖_HS`. -/
private lemma TOp_hs_mul_le' {n : Type*} [Fintype n] [DecidableEq n] (X V : Matrix n n ℂ) :
    hsNorm (V * X) ≤ opNorm X * hsNorm V := by
  have hc : ∀ W : Matrix n n ℂ, hsNorm Wᴴ = hsNorm W := fun W => by
    unfold hsNorm
    rw [Finset.sum_comm]
    simp [Matrix.conjTranspose_apply]
  have e : V * X = (Xᴴ * Vᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  rw [e, hc]
  refine (TOp_hs_mul_le Xᴴ Vᴴ).trans ?_
  rw [hc]
  have : opNorm Xᴴ = opNorm X := Matrix.l2_opNorm_conjTranspose X
  rw [this]

/-- The `ℓ²` norm of `D × D × D` tensors as a Euclidean norm. -/
private lemma TOp_ten3_eq {D : ℕ} (T : Fin D → Fin D → Fin D → ℂ) :
    ten3Norm T = ‖(WithLp.toLp 2 (fun p : Fin D × Fin D × Fin D => T p.1 p.2.1 p.2.2) :
      EuclideanSpace ℂ (Fin D × Fin D × Fin D))‖ := by
  rw [EuclideanSpace.norm_eq, ten3Norm, Fintype.sum_prod_type]
  simp [Fintype.sum_prod_type]

/-- The triangle inequality for `ten3Norm`. -/
private lemma TOp_ten3_add_le {D : ℕ} (S T : Fin D → Fin D → Fin D → ℂ) :
    ten3Norm (fun x y w => S x y w + T x y w) ≤ ten3Norm S + ten3Norm T := by
  rw [TOp_ten3_eq, TOp_ten3_eq, TOp_ten3_eq]
  exact norm_add_le (WithLp.toLp 2 (fun p : Fin D × Fin D × Fin D => S p.1 p.2.1 p.2.2) :
    EuclideanSpace ℂ (Fin D × Fin D × Fin D))
    (WithLp.toLp 2 (fun p : Fin D × Fin D × Fin D => T p.1 p.2.1 p.2.2))

/-- A matrix acting on the first slot of a tensor does not increase `ten3Norm` by more than its
operator norm. -/
private lemma TOp_ten3_slot₁ {D : ℕ} (X : Matrix (Fin D) (Fin D) ℂ)
    (V : Fin D → Fin D → Fin D → ℂ) :
    ten3Norm (fun x y w => ∑ a, X x a * V a y w) ≤ opNorm X * ten3Norm V := by
  have hX : 0 ≤ opNorm X := norm_nonneg _
  have key : ∑ x, ∑ y, ∑ w, ‖∑ a, X x a * V a y w‖ ^ 2 ≤
      opNorm X ^ 2 * ∑ a, ∑ y, ∑ w, ‖V a y w‖ ^ 2 := by
    calc ∑ x, ∑ y, ∑ w, ‖∑ a, X x a * V a y w‖ ^ 2
        = ∑ y, ∑ w, ∑ x, ‖(X *ᵥ fun a => V a y w) x‖ ^ 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_comm]
          rfl
      _ ≤ ∑ y, ∑ w, opNorm X ^ 2 * ∑ a, ‖V a y w‖ ^ 2 :=
          Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun w _ => TOp_vec_sq X _
      _ = opNorm X ^ 2 * ∑ a, ∑ y, ∑ w, ‖V a y w‖ ^ 2 := by
          simp only [← Finset.mul_sum]
          congr 1
          calc ∑ y, ∑ w, ∑ a, ‖V a y w‖ ^ 2 = ∑ y, ∑ a, ∑ w, ‖V a y w‖ ^ 2 :=
                Finset.sum_congr rfl fun y _ => Finset.sum_comm
            _ = ∑ a, ∑ y, ∑ w, ‖V a y w‖ ^ 2 := Finset.sum_comm
  unfold ten3Norm
  rw [← Real.sqrt_sq hX, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt key

/-- A matrix acting on the second slot of a tensor. -/
private lemma TOp_ten3_slot₂ {D : ℕ} (X : Matrix (Fin D) (Fin D) ℂ)
    (V : Fin D → Fin D → Fin D → ℂ) :
    ten3Norm (fun x y w => ∑ a, X y a * V x a w) ≤ opNorm X * ten3Norm V := by
  have hX : 0 ≤ opNorm X := norm_nonneg _
  have key : ∑ x, ∑ y, ∑ w, ‖∑ a, X y a * V x a w‖ ^ 2 ≤
      opNorm X ^ 2 * ∑ x, ∑ a, ∑ w, ‖V x a w‖ ^ 2 := by
    calc ∑ x, ∑ y, ∑ w, ‖∑ a, X y a * V x a w‖ ^ 2
        = ∑ x, ∑ w, ∑ y, ‖(X *ᵥ fun a => V x a w) y‖ ^ 2 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          rfl
      _ ≤ ∑ x, ∑ w, opNorm X ^ 2 * ∑ a, ‖V x a w‖ ^ 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun w _ => TOp_vec_sq X _
      _ = opNorm X ^ 2 * ∑ x, ∑ a, ∑ w, ‖V x a w‖ ^ 2 := by
          simp only [← Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
  unfold ten3Norm
  rw [← Real.sqrt_sq hX, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt key

/-- A matrix acting on the third slot of a tensor. -/
private lemma TOp_ten3_slot₃ {D : ℕ} (X : Matrix (Fin D) (Fin D) ℂ)
    (V : Fin D → Fin D → Fin D → ℂ) :
    ten3Norm (fun x y w => ∑ a, X w a * V x y a) ≤ opNorm X * ten3Norm V := by
  have hX : 0 ≤ opNorm X := norm_nonneg _
  have key : ∑ x, ∑ y, ∑ w, ‖∑ a, X w a * V x y a‖ ^ 2 ≤
      opNorm X ^ 2 * ∑ x, ∑ y, ∑ a, ‖V x y a‖ ^ 2 := by
    calc ∑ x, ∑ y, ∑ w, ‖∑ a, X w a * V x y a‖ ^ 2
        = ∑ x, ∑ y, ∑ w, ‖(X *ᵥ fun a => V x y a) w‖ ^ 2 := rfl
      _ ≤ ∑ x, ∑ y, opNorm X ^ 2 * ∑ a, ‖V x y a‖ ^ 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => TOp_vec_sq X _
      _ = opNorm X ^ 2 * ∑ x, ∑ y, ∑ a, ‖V x y a‖ ^ 2 := by
          simp only [← Finset.mul_sum]
  unfold ten3Norm
  rw [← Real.sqrt_sq hX, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt key

/-- Applying `q K - c` to a vector: `∑_a (q K - c)_{xa} f_a = q ∑_a K_{xa} f_a - c f_x`. -/
private lemma TOp_X_apply {D : ℕ} (K : Matrix (Fin D) (Fin D) ℂ) (q c : ℂ) (f : Fin D → ℂ)
    (x : Fin D) :
    ∑ a, (q • K - c • (1 : Matrix (Fin D) (Fin D) ℂ)) x a * f a =
      q * (∑ a, K x a * f a) - c * f x := by
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]

/-- `opNorm (F diag(κ) F^*) ≤ ρ` when `|κ_l| ≤ ρ`. -/
private lemma TOp_opNorm_diag (D : ℕ) (hD : D ≠ 0) (κ : Fin D → ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ l, ‖κ l‖ ≤ ρ) : opNorm (TOp_F D * diagonal κ * (TOp_F D)ᴴ) ≤ ρ := by
  rw [TOp_op_eq, TOp_conjF_norm D hD, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hρ).2 h

end TOp_Norms


/-- `c₁ (F diag(κ) F^*) - c₂ I = F diag(c₁ κ - c₂) F^*`. -/
private lemma TOp_lin (D : ℕ) (hD : D ≠ 0) (κ : Fin D → ℂ) (c₁ c₂ : ℂ) :
    c₁ • (TOp_F D * diagonal κ * (TOp_F D)ᴴ) - c₂ • (1 : Matrix (Fin D) (Fin D) ℂ) =
      TOp_F D * diagonal (fun l => c₁ * κ l - c₂) * (TOp_F D)ᴴ := by
  have hd : diagonal (fun l => c₁ * κ l - c₂) =
      c₁ • diagonal κ - c₂ • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.mul_one, TOp_F_unitary' D hD]

/-- The three consequences of the spectral analysis used by the operator bounds, for
`q = log(1 + η/Im m)`: `1 - M̂ P_θ` is invertible, `‖q K_θ‖ ≤ 1`, and
`‖q K_θ - (1 - q)/2‖ ≤ (1 + q)/2`. -/
private lemma TOp_Kbounds (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) :
    (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
      opNorm (((flowTc (lam D N A) z : ℝ) : ℂ) • KTheta (lam D N A) θ z₁ z₂) ≤ 1 ∧
      opNorm (((flowTc (lam D N A) z : ℝ) : ℂ) • KTheta (lam D N A) θ z₁ z₂ -
        (((1 - flowTc (lam D N A) z) / 2 : ℝ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ)) ≤
        (1 + flowTc (lam D N A) z) / 2 := by
  have hD : D ≠ 0 := NeZero.ne D
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have : Nonempty (Idx D N) := ⟨(⟨0, Nat.pos_of_ne_zero hD⟩, ⟨0, hN⟩)⟩
  have hq := TOp_flowTc_pos (lam D N A) (lam_isHermitian D N A) z hz
  obtain ⟨hdet, κ, hK, hκ⟩ := TOp_Kdiag D N A z hz θ hθ₀ hθ₁ z₁ z₂ h₁ h₂
  refine ⟨hdet, ?_, ?_⟩
  · have e := TOp_lin D hD κ ((flowTc (lam D N A) z : ℝ) : ℂ) 0
    rw [zero_smul, sub_zero, ← hK] at e
    rw [e]
    exact TOp_opNorm_diag D hD _ 1 zero_le_one fun l => by simpa using (hκ l).1
  · have e := TOp_lin D hD κ ((flowTc (lam D N A) z : ℝ) : ℂ)
      (((1 - flowTc (lam D N A) z) / 2 : ℝ) : ℂ)
    rw [← hK] at e
    rw [e]
    exact TOp_opNorm_diag D hD _ _ (by positivity) fun l => (hκ l).2

/-- Applying `(q K - c)ᵀ` to a vector. -/
private lemma TOp_Xt_apply {D : ℕ} (K : Matrix (Fin D) (Fin D) ℂ) (q c : ℂ) (f : Fin D → ℂ)
    (x : Fin D) :
    ∑ a, (q • K - c • (1 : Matrix (Fin D) (Fin D) ℂ)) a x * f a =
      q * (∑ a, K a x * f a) - c * f x := by
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]

/-- The operator bound behind (3.67) [Tnorm] at one point, with the class parameter: for
`q = log(1 + η/Im m)` and `z₁, z₂ ∈ {z, z̄}`, `1 - M̂ P_θ` is invertible, `‖q K_θ‖ ≤ 1`, and
`V ↦ q K_θ V + V q K_θ - (1 - q) V` of (3.62) [eq:TtV] has norm at most `1 + q` on `ℂ^{D×D}` with
the Hilbert–Schmidt norm. -/
theorem tOp_norm_le (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) :
    (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
      opNorm (((flowTc (lam D N A) z : ℝ) : ℂ) • KTheta (lam D N A) θ z₁ z₂) ≤ 1 ∧
      ∀ V : Matrix (Fin D) (Fin D) ℂ,
        hsNorm (((flowTc (lam D N A) z : ℝ) : ℂ) • (KTheta (lam D N A) θ z₁ z₂ * V +
            V * KTheta (lam D N A) θ z₁ z₂) - ((1 - flowTc (lam D N A) z : ℝ) : ℂ) • V) ≤
          (1 + flowTc (lam D N A) z) * hsNorm V := by
  obtain ⟨hdet, hK1, hK2⟩ := TOp_Kbounds D N A z hz θ hθ₀ hθ₁ z₁ z₂ h₁ h₂
  refine ⟨hdet, hK1, fun V => ?_⟩
  set q := flowTc (lam D N A) z with hq
  set K := KTheta (lam D N A) θ z₁ z₂ with hKdef
  set X : Matrix (Fin D) (Fin D) ℂ :=
    (q : ℂ) • K - (((1 - q) / 2 : ℝ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) with hX
  have e : (q : ℂ) • (K * V + V * K) - ((1 - q : ℝ) : ℂ) • V = X * V + V * X := by
    simp only [hX, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_add]
    push_cast
    module
  rw [e]
  refine (TOp_hs_add_le _ _).trans ?_
  have h1 := TOp_hs_mul_le X V
  have h2 := TOp_hs_mul_le' X V
  have h3 : opNorm X * hsNorm V ≤ (1 + q) / 2 * hsNorm V :=
    mul_le_mul_of_nonneg_right hK2 (Real.sqrt_nonneg _)
  linarith

/-- The three-resolvent operator bound at one point: for `z₁, z₂, z₃ ∈ {z, z̄}` and
`K̃_{(i,j)} = q K_θ(z_i, z_j)`, the map `V ↦ Σ_a (K̃_{(1,2),xa} V_{ayw} + K̃_{(2,3),ya} V_{xaw} +
K̃_{(3,1),wa} V_{xya}) - (3/2)(1 - q) V` has norm at most `(3/2)(1 + q)` for the `ℓ²` norm of
`D × D × D` tensors. -/
theorem tOp3_norm_le (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ z₂ z₃ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (h₃ : z₃ = z ∨ z₃ = star z)
    (V : Fin D → Fin D → Fin D → ℂ) :
    ten3Norm (fun x y w => ((flowTc (lam D N A) z : ℝ) : ℂ) * (∑ a,
        (KTheta (lam D N A) θ z₁ z₂ x a * V a y w + KTheta (lam D N A) θ z₂ z₃ y a * V x a w +
          KTheta (lam D N A) θ z₃ z₁ w a * V x y a)) -
        (3 / 2 : ℂ) * ((1 - flowTc (lam D N A) z : ℝ) : ℂ) * V x y w) ≤
      3 / 2 * (1 + flowTc (lam D N A) z) * ten3Norm V := by
  obtain ⟨-, -, hK₁⟩ := TOp_Kbounds D N A z hz θ hθ₀ hθ₁ z₁ z₂ h₁ h₂
  obtain ⟨-, -, hK₂⟩ := TOp_Kbounds D N A z hz θ hθ₀ hθ₁ z₂ z₃ h₂ h₃
  obtain ⟨-, -, hK₃⟩ := TOp_Kbounds D N A z hz θ hθ₀ hθ₁ z₃ z₁ h₃ h₁
  set q := flowTc (lam D N A) z with hq
  set c : ℂ := (((1 - q) / 2 : ℝ) : ℂ) with hc
  set X₁ : Matrix (Fin D) (Fin D) ℂ :=
    (q : ℂ) • KTheta (lam D N A) θ z₁ z₂ - c • (1 : Matrix (Fin D) (Fin D) ℂ) with hX₁
  set X₂ : Matrix (Fin D) (Fin D) ℂ :=
    (q : ℂ) • KTheta (lam D N A) θ z₂ z₃ - c • (1 : Matrix (Fin D) (Fin D) ℂ) with hX₂
  set X₃ : Matrix (Fin D) (Fin D) ℂ :=
    (q : ℂ) • KTheta (lam D N A) θ z₃ z₁ - c • (1 : Matrix (Fin D) (Fin D) ℂ) with hX₃
  have hfun : (fun x y w => (q : ℂ) * (∑ a,
        (KTheta (lam D N A) θ z₁ z₂ x a * V a y w + KTheta (lam D N A) θ z₂ z₃ y a * V x a w +
          KTheta (lam D N A) θ z₃ z₁ w a * V x y a)) -
        (3 / 2 : ℂ) * ((1 - q : ℝ) : ℂ) * V x y w) =
      fun x y w => ((∑ a, X₁ x a * V a y w) + ∑ a, X₂ y a * V x a w) + ∑ a, X₃ w a * V x y a := by
    funext x y w
    rw [hX₁, hX₂, hX₃, TOp_X_apply _ _ _ (fun a => V a y w) x,
      TOp_X_apply _ _ _ (fun a => V x a w) y, TOp_X_apply _ _ _ (fun a => V x y a) w]
    simp only [Finset.sum_add_distrib, mul_add, hc]
    push_cast
    ring
  rw [hfun]
  refine (TOp_ten3_add_le _ _).trans ?_
  have h12 := TOp_ten3_add_le (fun x y w => ∑ a, X₁ x a * V a y w)
    (fun x y w => ∑ a, X₂ y a * V x a w)
  have s1 := TOp_ten3_slot₁ X₁ V
  have s2 := TOp_ten3_slot₂ X₂ V
  have s3 := TOp_ten3_slot₃ X₃ V
  have hT : 0 ≤ ten3Norm V := Real.sqrt_nonneg _
  have m1 : opNorm X₁ * ten3Norm V ≤ (1 + q) / 2 * ten3Norm V := mul_le_mul_of_nonneg_right hK₁ hT
  have m2 : opNorm X₂ * ten3Norm V ≤ (1 + q) / 2 * ten3Norm V := mul_le_mul_of_nonneg_right hK₂ hT
  have m3 : opNorm X₃ * ten3Norm V ≤ (1 + q) / 2 * ten3Norm V := mul_le_mul_of_nonneg_right hK₃ hT
  linarith

/-- The one-resolvent operator bound at one point: for `z₁ ∈ {z, z̄}`, the map
`v ↦ q K_θ(z₁, z₁)ᵀ v - (1/2)(1 - q) v` has norm at most `(1 + q)/2` on `ℂ^D`. -/
theorem tOp1_norm_le (D N : ℕ) [NeZero D] [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : 0 < z.im) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (z₁ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (v : Fin D → ℂ) :
    Real.sqrt (∑ x, ‖((flowTc (lam D N A) z : ℝ) : ℂ) *
        (∑ a, KTheta (lam D N A) θ z₁ z₁ a x * v a) -
        (1 / 2 : ℂ) * ((1 - flowTc (lam D N A) z : ℝ) : ℂ) * v x‖ ^ 2) ≤
      (1 + flowTc (lam D N A) z) / 2 * Real.sqrt (∑ x, ‖v x‖ ^ 2) := by
  obtain ⟨-, -, hK⟩ := TOp_Kbounds D N A z hz θ hθ₀ hθ₁ z₁ z₁ h₁ h₁
  set q := flowTc (lam D N A) z with hq
  set X : Matrix (Fin D) (Fin D) ℂ := (q : ℂ) • KTheta (lam D N A) θ z₁ z₁ -
    (((1 - q) / 2 : ℝ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) with hX
  have he : ∀ x, ‖(q : ℂ) * (∑ a, KTheta (lam D N A) θ z₁ z₁ a x * v a) -
      (1 / 2 : ℂ) * ((1 - q : ℝ) : ℂ) * v x‖ = ‖(Xᴴ *ᵥ fun a => star (v a)) x‖ := by
    intro x
    have h1 : (Xᴴ *ᵥ fun a => star (v a)) x = star (∑ a, X a x * v a) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [star_mul', mul_comm]
    rw [h1, norm_star, hX, TOp_Xt_apply]
    congr 1
    push_cast
    ring
  have hsq : ∑ x, ‖(q : ℂ) * (∑ a, KTheta (lam D N A) θ z₁ z₁ a x * v a) -
      (1 / 2 : ℂ) * ((1 - q : ℝ) : ℂ) * v x‖ ^ 2 ≤ opNorm X ^ 2 * ∑ x, ‖v x‖ ^ 2 := by
    simp only [he]
    refine (TOp_vec_sq Xᴴ _).trans ?_
    have : opNorm Xᴴ = opNorm X := Matrix.l2_opNorm_conjTranspose X
    rw [this]
    simp only [norm_star, le_refl]
  have hX0 : 0 ≤ opNorm X := norm_nonneg _
  calc _ ≤ Real.sqrt (opNorm X ^ 2 * ∑ x, ‖v x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = opNorm X * Real.sqrt (∑ x, ‖v x‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hX0]
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg _)


/-- The flow from the backward point: the closed form (3.10) [eq:deterflow] started at `z_{-S}`
with `Λ_{-S} = e^{S/2} Λ` is the closed form started at `z`, shifted by `S`, for `S ≥ 0`. -/
theorem charFlowZ_comp {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (S s : ℝ) (hS : 0 ≤ S) :
    charFlowZ (((Real.exp (S / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z (-S)) s =
      charFlowZ Λ z (s - S) := by
  have hq := TOp_flowTc_pos Λ hΛ z hz
  have hs : -S < Real.log (1 + z.im / (mExt Λ z).im) := by
    have : flowTc Λ z = Real.log (1 + z.im / (mExt Λ z).im) := rfl
    linarith
  obtain ⟨-, -, hm⟩ := charFlow_M Λ hΛ z hz (-S) hs
  have e0 : -(-S) / 2 = S / 2 := by ring
  rw [e0] at hm
  have e1 : Real.exp (-s / 2) * Real.exp (S / 2) = Real.exp (-(s - S) / 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (s / 2) * Real.exp (-S / 2) = Real.exp ((s - S) / 2) := by
    rw [← Real.exp_add]; ring_nf
  have c1 : ((Real.exp (-s / 2) : ℝ) : ℂ) * ((Real.exp (S / 2) : ℝ) : ℂ) =
      ((Real.exp (-(s - S) / 2) : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, e1]
  have c2 : ((Real.exp (s / 2) : ℝ) : ℂ) * ((Real.exp (-S / 2) : ℝ) : ℂ) =
      ((Real.exp ((s - S) / 2) : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, e2]
  change ((Real.exp (-s / 2) : ℝ) : ℂ) * (charFlowZ Λ z (-S) +
      mExt (((Real.exp (S / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z (-S))) -
    ((Real.exp (s / 2) : ℝ) : ℂ) * mExt (((Real.exp (S / 2) : ℝ) : ℂ) • Λ)
      (charFlowZ Λ z (-S)) = charFlowZ Λ z (s - S)
  rw [hm]
  simp only [charFlowZ, neg_neg]
  linear_combination (z + mExt Λ z) * c1 - mExt Λ z * c2

/-- (3.14) [t_eta] read at the flowed point: for `s < t_c - t₀`,
`log(1 + η_s / Im m_s) = log(1 + η / Im m) - s`, i.e. `t_c - t = (t_c - t₀) - s`. -/
theorem flowTc_flow {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s : ℝ) (hs : s < flowTc Λ z) :
    flowTc (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s) = flowTc Λ z - s := by
  have h := charFlow_teta Λ hΛ z hz s hs
  simp only [flowTc]
  rw [h, add_sub_cancel, Real.log_exp]


end RBMTransitionEdge

end
