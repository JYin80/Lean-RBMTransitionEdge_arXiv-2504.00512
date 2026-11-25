module

public import RBMTransitionEdge.Flow.LargeEta
public import RBMTransitionEdge.Flow.LargeEtaPrelim

@[expose] public section

/-!
# Lemmas 3.14 and 3.15 for the law of `H_t`

The leading fourth-cumulant terms of Lemma 3.15 [lem:fourthcumu2], (3.42) [eq:Exp_G1-M1], and of
Lemma 3.14 [lem:fourthcumu1], (3.41) [eq:G1HG2], for the law of `H_t` of (4.1) [defVt],
`t ∈ [0, 1]`, with the class parameter `θ = e^{-t}` and `K_θ`, and the circulant identities for
`K_θ` used in the proof of Lemma 3.7 [lemma_G_large_2].
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `K_{θ,ab}(B) = Σ_x ((1 - M̂ P_θ)⁻¹)_{ax} D ⟨M₁ E_x M₂ E_b B⟩`: the matrix `K_{ab}(B)` of §3.2
(proof of Lemma 3.7 [lemma_G_large_2]) with `(1 - M̂)⁻¹` replaced by `(1 - M̂ P_θ)⁻¹`; the matrix
`K̃_{ab}(B)` there, with `1` and `2` exchanged, is `KThetaB Λ θ z₂ z₁ B a b`. -/
def KThetaB {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ)
    (B : Matrix (Idx D N) (Idx D N) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun a b => ∑ x, (1 - Mhat Λ z₁ z₂ * PTheta D θ)⁻¹ a x *
    ((D : ℂ) * ntr (MExt Λ z₁ * Ea D N x * MExt Λ z₂ * Ea D N b * B))

/-- The bracket of (3.42) [eq:Exp_G1-M1] of Lemma 3.15 [lem:fourthcumu2], `M₁ = M(z₁)`:
`⟨diag(M₁)²⟩ [⟨M₁ B M₁ diag(M₁)⟩ + ⟨M₁² diag(M₁)⟩ ⟨M₁² B⟩ / (1 - ⟨M₁²⟩)]`. -/
def lead15 {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ : ℂ)
    (B : Matrix (Idx D N) (Idx D N) ℂ) : ℂ :=
  ntr (diagonal (diag (MExt Λ z₁)) * diagonal (diag (MExt Λ z₁))) *
    (ntr (MExt Λ z₁ * B * MExt Λ z₁ * diagonal (diag (MExt Λ z₁))) +
      ntr (MExt Λ z₁ * MExt Λ z₁ * diagonal (diag (MExt Λ z₁))) *
        ntr (MExt Λ z₁ * MExt Λ z₁ * B) / (1 - ntr (MExt Λ z₁ * MExt Λ z₁)))

/-- The sum of (3.41) [eq:G1HG2] of Lemma 3.14 [lem:fourthcumu1] with `K̃` replaced by
`K̃_θ(B) = KThetaB Λ θ z₂ z₁ B`: `Σ_x [⟨diag(M₂)² E_x⟩ K̃_{ba}(M₂ diag(M₂) E_x)
+ ⟨M₁ diag(M₂) E_x⟩ K̃_{bx}(diag(M₁ E_a M₂)) + ⟨M₁ E_a M₂ diag(M₁) E_x⟩ K̃_{bx}(diag M₁)
+ ⟨M₁ E_a M₂ diag(M₂) E_x⟩ K̃_{bx}(diag M₂)]`. -/
def lead14 {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ) (a b : Fin D) : ℂ :=
  ∑ x, (ntr (diagonal (diag (MExt Λ z₂)) * diagonal (diag (MExt Λ z₂)) * Ea D N x) *
        KThetaB Λ θ z₂ z₁ (MExt Λ z₂ * diagonal (diag (MExt Λ z₂)) * Ea D N x) b a +
      ntr (MExt Λ z₁ * diagonal (diag (MExt Λ z₂)) * Ea D N x) *
        KThetaB Λ θ z₂ z₁ (diagonal (diag (MExt Λ z₁ * Ea D N a * MExt Λ z₂))) b x +
      ntr (MExt Λ z₁ * Ea D N a * MExt Λ z₂ * diagonal (diag (MExt Λ z₁)) * Ea D N x) *
        KThetaB Λ θ z₂ z₁ (diagonal (diag (MExt Λ z₁))) b x +
      ntr (MExt Λ z₁ * Ea D N a * MExt Λ z₂ * diagonal (diag (MExt Λ z₂)) * Ea D N x) *
        KThetaB Λ θ z₂ z₁ (diagonal (diag (MExt Λ z₂))) b x)

/-! ### Auxiliary lemmas -/

section

section FC_Fourier

open scoped Matrix.Norms.L2Operator

private theorem FC_op_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    opNorm A = ‖A‖ := rfl

open scoped Matrix.Norms.L2Operator

private def FC_zeta (D : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / D)

private theorem FC_zeta_prim (D : ℕ) (hD : D ≠ 0) : IsPrimitiveRoot (FC_zeta D) D :=
  Complex.isPrimitiveRoot_exp D hD

private theorem FC_norm_zeta_pow (D : ℕ) (hD : D ≠ 0) (k : ℕ) : ‖FC_zeta D ^ k‖ = 1 := by
  rw [norm_pow, (FC_zeta_prim D hD).norm'_eq_one hD, one_pow]

private theorem FC_star_zeta_pow (D : ℕ) (hD : D ≠ 0) (k : ℕ) :
    star (FC_zeta D ^ k) * FC_zeta D ^ k = 1 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    FC_norm_zeta_pow D hD]
  simp

private theorem FC_fourierVec_eq (D : ℕ) (l a : Fin D) :
    fourierVec D l a = ((Real.sqrt D : ℂ))⁻¹ * FC_zeta D ^ ((l : ℕ) * (a : ℕ)) := by
  unfold fourierVec FC_zeta
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

private def FC_F (D : ℕ) : Matrix (Fin D) (Fin D) ℂ := Matrix.of fun a l => fourierVec D l a

private theorem FC_sqrt_inv_sq (D : ℕ) :
    star ((Real.sqrt D : ℂ))⁻¹ * ((Real.sqrt D : ℂ))⁻¹ = (D : ℂ)⁻¹ := by
  have h : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt h]
  simp

private theorem FC_F_unitary (D : ℕ) (hD : D ≠ 0) : (FC_F D)ᴴ * FC_F D = 1 := by
  have hζ := FC_zeta_prim D hD
  ext l l'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, FC_F, Matrix.of_apply,
    FC_fourierVec_eq, Matrix.one_apply]
  have e : ∀ a : Fin D, star (((Real.sqrt D : ℂ))⁻¹ * FC_zeta D ^ ((l : ℕ) * (a : ℕ))) *
      (((Real.sqrt D : ℂ))⁻¹ * FC_zeta D ^ ((l' : ℕ) * (a : ℕ))) =
      (D : ℂ)⁻¹ * (star (FC_zeta D ^ (l : ℕ)) * FC_zeta D ^ (l' : ℕ)) ^ (a : ℕ) := by
    intro a
    rw [star_mul', mul_pow, ← star_pow, ← pow_mul, ← pow_mul, ← FC_sqrt_inv_sq D]
    ring
  simp only [e, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun a => (star (FC_zeta D ^ (l : ℕ)) * FC_zeta D ^ (l' : ℕ)) ^ a)]
  by_cases hll : l = l'
  · subst hll
    rw [FC_star_zeta_pow D hD]
    simp [hD]
  · simp only [hll, ↓reduceIte]
    set r := star (FC_zeta D ^ (l : ℕ)) * FC_zeta D ^ (l' : ℕ) with hr
    have hrD : r ^ D = 1 := by
      rw [hr, mul_pow, ← star_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ), mul_comm (l' : ℕ),
        pow_mul, pow_mul, hζ.pow_eq_one, one_pow, one_pow, star_one, one_mul]
    have hr1 : r ≠ 1 := by
      intro h1
      have : FC_zeta D ^ (l' : ℕ) = FC_zeta D ^ (l : ℕ) := by
        have h2 := congrArg (fun x => FC_zeta D ^ (l : ℕ) * x) h1
        simp only [mul_one] at h2
        rw [hr, ← mul_assoc, mul_comm (FC_zeta D ^ (l : ℕ)), FC_star_zeta_pow D hD, one_mul] at h2
        exact h2
      exact hll (Fin.ext (hζ.pow_inj l.isLt l'.isLt this.symm))
    have hg := geom_sum_mul r D
    rw [hrD, sub_self] at hg
    have : ∑ i ∈ Finset.range D, r ^ i = 0 :=
      (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hr1)
    rw [this, mul_zero]

private theorem FC_F_unitary' (D : ℕ) (hD : D ≠ 0) : FC_F D * (FC_F D)ᴴ = 1 :=
  mul_eq_one_comm.mp (FC_F_unitary D hD)

private theorem FC_F_norm (D : ℕ) (hD : D ≠ 0) : ‖FC_F D‖ ≤ 1 := by
  have : Nonempty (Fin D) := ⟨⟨0, Nat.pos_of_ne_zero hD⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (FC_F D)
  rw [FC_F_unitary D hD, norm_one] at h1
  nlinarith [norm_nonneg (FC_F D)]

private theorem FC_circ (D : ℕ) (hD : D ≠ 0) (B : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ)
    (hB : ∀ l, B *ᵥ fourierVec D l = μ l • fourierVec D l) :
    B = FC_F D * diagonal μ * (FC_F D)ᴴ := by
  have h1 : B * FC_F D = FC_F D * diagonal μ := by
    ext a l
    have := congrFun (hB l) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, FC_F, Matrix.of_apply]
    rw [this, mul_comm]
  calc B = B * (FC_F D * (FC_F D)ᴴ) := by rw [FC_F_unitary' D hD, Matrix.mul_one]
    _ = FC_F D * diagonal μ * (FC_F D)ᴴ := by rw [← Matrix.mul_assoc, h1]

private theorem FC_conjF_norm (D : ℕ) (hD : D ≠ 0) (X : Matrix (Fin D) (Fin D) ℂ) :
    ‖FC_F D * X * (FC_F D)ᴴ‖ = ‖X‖ := by
  have hF := FC_F_norm D hD
  have hF' : ‖(FC_F D)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hF
  apply le_antisymm
  · calc ‖FC_F D * X * (FC_F D)ᴴ‖ ≤ ‖FC_F D‖ * ‖X‖ * ‖(FC_F D)ᴴ‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖X‖ * 1 := by gcongr
      _ = ‖X‖ := by ring
  · have e : X = (FC_F D)ᴴ * (FC_F D * X * (FC_F D)ᴴ) * FC_F D := by
      simp only [← Matrix.mul_assoc, FC_F_unitary D hD, Matrix.one_mul]
      rw [Matrix.mul_assoc, FC_F_unitary D hD, Matrix.mul_one]
    calc ‖X‖ = ‖(FC_F D)ᴴ * (FC_F D * X * (FC_F D)ᴴ) * FC_F D‖ := by rw [← e]
      _ ≤ ‖(FC_F D)ᴴ‖ * ‖FC_F D * X * (FC_F D)ᴴ‖ * ‖FC_F D‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖FC_F D * X * (FC_F D)ᴴ‖ * 1 := by gcongr
      _ = _ := by ring

private theorem FC_sum_zeta (D : ℕ) (hD : D ≠ 0) (l : Fin D) (hl : (l : ℕ) ≠ 0) :
    ∑ b : Fin D, FC_zeta D ^ ((l : ℕ) * (b : ℕ)) = 0 := by
  have hζ := FC_zeta_prim D hD
  set r := FC_zeta D ^ (l : ℕ) with hr
  have e : ∀ b : Fin D, FC_zeta D ^ ((l : ℕ) * (b : ℕ)) = r ^ (b : ℕ) := fun b => by
    rw [hr, ← pow_mul]
  simp only [e]
  rw [Fin.sum_univ_eq_sum_range (fun b => r ^ b) D]
  have hrD : r ^ D = 1 := by
    rw [hr, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hr1 : r ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hl l.isLt
  have hg := geom_sum_mul r D
  rw [hrD, sub_self] at hg
  exact (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hr1)

private theorem FC_P_eig (D : ℕ) (hD : D ≠ 0) (θ : ℝ) (l : Fin D) :
    PTheta D θ *ᵥ fourierVec D l =
      (if (l : ℕ) = 0 then (1 : ℂ) else (θ : ℂ)) • fourierVec D l := by
  have : NeZero D := ⟨hD⟩
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  have hJ : ∀ a : Fin D, ((Matrix.of fun _ _ => (1 : ℂ)) *ᵥ fourierVec D l) a =
      ∑ b, fourierVec D l b := fun a => by simp [Matrix.mulVec, dotProduct]
  have hsum : ∑ b, fourierVec D l b =
      ((Real.sqrt D : ℂ))⁻¹ * ∑ b : Fin D, FC_zeta D ^ ((l : ℕ) * (b : ℕ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => FC_fourierVec_eq D l b
  ext a
  simp only [PTheta, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, hJ, hsum]
  by_cases hl : (l : ℕ) = 0
  · simp only [hl, ↓reduceIte, zero_mul, pow_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [FC_fourierVec_eq, hl]
    simp only [zero_mul, pow_zero, mul_one]
    push_cast
    field_simp
    ring
  · simp only [hl, ↓reduceIte, FC_sum_zeta D hD l hl, mul_zero, add_zero]

end FC_Fourier

section FC_Bound

variable {ι : Type*} [Fintype ι]

private def FC_S (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private theorem FC_S_conj (A : Matrix ι ι ℂ) : FC_S Aᴴ = FC_S A := by
  unfold FC_S
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

private theorem FC_tr_mul_le (X Y : Matrix ι ι ℂ) :
    ‖(X * Y).trace‖ ≤ Real.sqrt (FC_S X) * Real.sqrt (FC_S Y) := by
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
  have e1 : ∑ p : ι × ι, ‖X p.1 p.2‖ ^ 2 = FC_S X := by
    rw [Fintype.sum_prod_type]; rfl
  have e2 : ∑ p : ι × ι, ‖Y p.2 p.1‖ ^ 2 = FC_S Y := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rw [e1, e2] at h2
  exact h2

private theorem FC_trace_mul_conj (Z : Matrix ι ι ℂ) : (Z * Zᴴ).trace = (FC_S Z : ℂ) := by
  unfold FC_S
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

private theorem FC_D_ntr (D N : ℕ) (hD : D ≠ 0) (X : Matrix (Idx D N) (Idx D N) ℂ) :
    (D : ℂ) * ntr X = (N : ℂ)⁻¹ * X.trace := by
  unfold ntr
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  by_cases hN : (N : ℂ) = 0
  · simp [hN]
  · field_simp

private theorem FC_S_MExt (D N : ℕ) (hD : D ≠ 0) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (z₁ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) :
    FC_S (MExt (lam D N A) z₁) ≤ D * N := by
  have : Nonempty (Idx D N) := ⟨(⟨0, Nat.pos_of_ne_zero hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hm : mExt (lam D N A) z = mSol (lam D N A) z := by simp only [mExt, hz, ↓reduceIte]
  have hM : MExt (lam D N A) z = MSol (lam D N A) z := by rw [MExt, MSol, hm]
  have hy := (mSol_spec (lam D N A) hΛ z hz).1
  have h1 := (equation_z_im_m (lam D N A) hΛ z hz).1
  set y := (mSol (lam D N A) z).im
  have hS : FC_S (MExt (lam D N A) z) ≤ D * N := by
    have hcard : ((D * N : ℕ) : ℂ) ≠ 0 := by
      have := (Fintype.card_pos (α := Idx D N)).ne'
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
      exact_mod_cast this
    have e : (FC_S (MSol (lam D N A) z) : ℂ) =
        ((D * N : ℕ) : ℂ) * ((y / (y + z.im) : ℝ) : ℂ) := by
      rw [← FC_trace_mul_conj, ← h1]
      unfold ntr
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    have e' : FC_S (MSol (lam D N A) z) = ((D * N : ℕ) : ℝ) * (y / (y + z.im)) := by
      exact_mod_cast e
    rw [hM, e']
    have hd : y / (y + z.im) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have : (0 : ℝ) ≤ ((D * N : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at this ⊢
    nlinarith
  rcases h₁ with rfl | rfl
  · exact hS
  · rw [(mExt_conj (lam D N A) hΛ z hz.ne').2, FC_S_conj]
    exact hS

private theorem FC_circEig_le (D N : ℕ) (hD : D ≠ 0) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (l : Fin D) :
    ‖circEig (Mhat (lam D N A) z₁ z₂) l‖ ≤ 1 := by
  have : NeZero D := ⟨hD⟩
  set M₁ := MExt (lam D N A) z₁
  set M₂ := MExt (lam D N A) z₂
  set u := fourierVec D l with hu
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hun : ∀ a : Fin D, ‖u a‖ = (Real.sqrt D)⁻¹ := by
    intro a
    rw [hu, FC_fourierVec_eq, norm_mul, FC_norm_zeta_pow D hD, mul_one, norm_inv,
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
    simp only [FC_D_ntr D N hD]
    rw [hV₁, hV₂]
    simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hu]
    ring
  have hS₁ := FC_S_MExt D N hD hN A z hz z₁ h₁
  have hS₂ := FC_S_MExt D N hD hN A z hz z₂ h₂
  set V₁ : Matrix (Idx D N) (Idx D N) ℂ := Matrix.diagonal fun p : Idx D N => star (u p.1)
  set V₂ : Matrix (Idx D N) (Idx D N) ℂ := Matrix.diagonal fun p : Idx D N => u p.1
  have hq : ((Real.sqrt D)⁻¹) ^ 2 = (D : ℝ)⁻¹ := by rw [inv_pow, Real.sq_sqrt hDpos.le]
  have hS : FC_S (V₁ * M₂ * V₂) = ((D : ℝ)⁻¹) ^ 2 * FC_S M₂ := by
    unfold FC_S
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [V₁, V₂, Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_star, hun]
    rw [← hq]
    ring
  have htr := FC_tr_mul_le M₁ (V₁ * M₂ * V₂)
  have e : M₁ * V₁ * M₂ * V₂ = M₁ * (V₁ * M₂ * V₂) := by simp only [Matrix.mul_assoc]
  have hsq : Real.sqrt (FC_S (V₁ * M₂ * V₂)) = (D : ℝ)⁻¹ * Real.sqrt (FC_S M₂) := by
    rw [hS, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have h1 : Real.sqrt (FC_S M₁) ≤ Real.sqrt (D * N) := Real.sqrt_le_sqrt hS₁
  have h2 : Real.sqrt (FC_S M₂) ≤ Real.sqrt (D * N) := Real.sqrt_le_sqrt hS₂
  have hDN : Real.sqrt (D * N) * Real.sqrt (D * N) = D * N :=
    Real.mul_self_sqrt (by positivity)
  rw [hc, e, norm_mul, norm_inv, Complex.norm_natCast]
  rw [hsq] at htr
  calc (N : ℝ)⁻¹ * ‖(M₁ * (V₁ * M₂ * V₂)).trace‖
      ≤ (N : ℝ)⁻¹ * (Real.sqrt (FC_S M₁) * ((D : ℝ)⁻¹ * Real.sqrt (FC_S M₂))) := by
        gcongr
    _ ≤ (N : ℝ)⁻¹ * (Real.sqrt (D * N) * ((D : ℝ)⁻¹ * Real.sqrt (D * N))) := by
        gcongr
    _ = 1 := by
        have : (N : ℝ)⁻¹ * (Real.sqrt (D * N) * ((D : ℝ)⁻¹ * Real.sqrt (D * N))) =
            (N : ℝ)⁻¹ * (D : ℝ)⁻¹ * (Real.sqrt (D * N) * Real.sqrt (D * N)) := by ring
        rw [this, hDN]
        field_simp

end FC_Bound

section FC_Dg

open scoped Matrix.Norms.L2Operator

private def FC_dg (D : ℕ) (κ : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  FC_F D * diagonal κ * (FC_F D)ᴴ

private theorem FC_dg_mul (D : ℕ) (hD : D ≠ 0) (κ κ' : Fin D → ℂ) :
    FC_dg D κ * FC_dg D κ' = FC_dg D (fun l => κ l * κ' l) := by
  unfold FC_dg
  have e : FC_F D * diagonal κ * (FC_F D)ᴴ * (FC_F D * diagonal κ' * (FC_F D)ᴴ) =
      FC_F D * (diagonal κ * ((FC_F D)ᴴ * FC_F D) * diagonal κ') * (FC_F D)ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [e, FC_F_unitary D hD, Matrix.mul_one, Matrix.diagonal_mul_diagonal]

private theorem FC_dg_sub (D : ℕ) (κ κ' : Fin D → ℂ) :
    FC_dg D κ - FC_dg D κ' = FC_dg D (fun l => κ l - κ' l) := by
  unfold FC_dg
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]

private theorem FC_dg_one (D : ℕ) (hD : D ≠ 0) : (1 : Matrix (Fin D) (Fin D) ℂ) = FC_dg D (fun _ => 1) := by
  unfold FC_dg
  rw [Matrix.diagonal_one, Matrix.mul_one, FC_F_unitary' D hD]

private theorem FC_dg_det (D : ℕ) (hD : D ≠ 0) (κ : Fin D → ℂ) : (FC_dg D κ).det = ∏ l, κ l := by
  unfold FC_dg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hdet : (FC_F D).det * ((FC_F D)ᴴ).det = 1 := by
    rw [← Matrix.det_mul, FC_F_unitary' D hD, Matrix.det_one]
  linear_combination (∏ l, κ l) * hdet

private theorem FC_dg_inv (D : ℕ) (hD : D ≠ 0) (κ : Fin D → ℂ) (hκ : ∀ l, κ l ≠ 0) :
    (FC_dg D κ)⁻¹ = FC_dg D (fun l => (κ l)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [FC_dg_mul D hD, FC_dg_one D hD]
  congr 1
  funext l
  exact mul_inv_cancel₀ (hκ l)

private theorem FC_dg_opNorm (D : ℕ) (hD : D ≠ 0) (κ : Fin D → ℂ) : opNorm (FC_dg D κ) = ‖κ‖ := by
  rw [FC_op_eq]
  unfold FC_dg
  rw [FC_conjF_norm D hD, Matrix.l2_opNorm_diagonal]

private theorem FC_dg_comm (D : ℕ) (hD : D ≠ 0) (κ κ' : Fin D → ℂ) :
    FC_dg D κ * FC_dg D κ' = FC_dg D κ' * FC_dg D κ := by
  rw [FC_dg_mul D hD, FC_dg_mul D hD]
  congr 1
  funext l
  ring

private theorem FC_four (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z)
    (h₂ : z₂ = z ∨ z₂ = star z) (θ : ℝ) :
    Mhat (lam D N A) z₁ z₂ = FC_dg D (fun l => circEig (Mhat (lam D N A) z₁ z₂) l) ∧
      (∀ l, ‖circEig (Mhat (lam D N A) z₁ z₂) l‖ ≤ 1) ∧
      PTheta D θ = FC_dg D (fun l => if (l : ℕ) = 0 then (1 : ℂ) else (θ : ℂ)) := by
  have hD0 : D ≠ 0 := by omega
  have him : ∀ z' : ℂ, (z' = z ∨ z' = star z) → z'.im ≠ 0 := by
    rintro z' (rfl | rfl)
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  refine ⟨FC_circ D hD0 _ _ (Mhat_eigvec D hD N A z₁ z₂ (him z₁ h₁) (him z₂ h₂)),
    fun l => FC_circEig_le D N hD0 hN A z hz z₁ z₂ h₁ h₂ l,
    FC_circ D hD0 _ _ (FC_P_eig D hD0 θ)⟩

end FC_Dg

private theorem FC_Mhat_swap {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) :
    Mhat Λ z₂ z₁ = (Mhat Λ z₁ z₂)ᵀ := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.transpose_apply]
  show (D : ℂ) * ntr (MExt Λ z₂ * Ea D N a * MExt Λ z₁ * Ea D N b) =
    (D : ℂ) * ntr (MExt Λ z₁ * Ea D N b * MExt Λ z₂ * Ea D N a)
  have e1 : MExt Λ z₂ * Ea D N a * MExt Λ z₁ * Ea D N b =
      (MExt Λ z₂ * Ea D N a) * (MExt Λ z₁ * Ea D N b) := by simp only [Matrix.mul_assoc]
  have e2 : MExt Λ z₁ * Ea D N b * MExt Λ z₂ * Ea D N a =
      (MExt Λ z₁ * Ea D N b) * (MExt Λ z₂ * Ea D N a) := by simp only [Matrix.mul_assoc]
  rw [e1, e2, ntr, ntr, Matrix.trace_mul_comm]

private theorem FC_PTheta_transpose (D : ℕ) (θ : ℝ) : (PTheta D θ)ᵀ = PTheta D θ := by
  ext a b
  simp only [PTheta, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply]
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

private theorem FC_scalar2 (μ : ℂ) (hμ : ‖μ‖ ≤ 1) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ‖μ ^ 2 * ((1 - θ : ℝ) : ℂ)‖ ≤ ‖1 - (θ : ℂ) * μ‖ ∧
      ‖((1 - θ : ℝ) : ℂ) * μ‖ ≤ ‖1 - (θ : ℂ) * μ‖ := by
  have hr := norm_nonneg μ
  have h3 := norm_sub_norm_le (1 : ℂ) ((θ : ℂ) * μ)
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] at h3
  have e1 : ‖μ ^ 2 * ((1 - θ : ℝ) : ℂ)‖ = ‖μ‖ ^ 2 * (1 - θ) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have e2 : ‖((1 - θ : ℝ) : ℂ) * μ‖ = (1 - θ) * ‖μ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [e1, e2]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hμ) (mul_nonneg hr (sub_nonneg.2 h1))]
  · nlinarith

private theorem FC_Ea_mul (D N : ℕ) (x a : Fin D) :
    Ea D N x * Ea D N a = if x = a then Ea D N a else 0 := by
  unfold Ea
  rw [Matrix.diagonal_mul_diagonal]
  by_cases h : x = a
  · subst h
    simp only [↓reduceIte]
    congr 1
    funext p
    by_cases hp : p.1 = x <;> simp [hp]
  · simp only [h, ↓reduceIte]
    rw [← Matrix.diagonal_zero]
    congr 1
    funext p
    by_cases hp : p.1 = x
    · simp [hp, h]
    · simp [hp]

private theorem FC_circ_core (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z)
    (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hdet : (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0) :
    ((1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ * Mhat (lam D N A) z₂ z₁)ᵀ =
        KTheta (lam D N A) θ z₁ z₂ ∧
      opNorm (Mhat (lam D N A) z₁ z₂ * KTheta (lam D N A) θ z₁ z₂ -
          (KTheta (lam D N A) θ z₁ z₂ - Mhat (lam D N A) z₁ z₂)) ≤ 1 ∧
      opNorm (PTheta D θ * KTheta (lam D N A) θ z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) ≤ 1 := by
  have hD0 : D ≠ 0 := by omega
  obtain ⟨hM, hevb, hP⟩ := FC_four D hD N hN A z hz z₁ z₂ h₁ h₂ θ
  set ev := fun l => circEig (Mhat (lam D N A) z₁ z₂) l with hev
  set π := fun l : Fin D => if (l : ℕ) = 0 then (1 : ℂ) else (θ : ℂ) with hπ
  have h1MP : 1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ = FC_dg D (fun l => 1 - ev l * π l) := by
    rw [hM, hP, FC_dg_mul D hD0, FC_dg_one D hD0, FC_dg_sub]
  have hne : ∀ l, 1 - ev l * π l ≠ 0 := by
    rw [h1MP, FC_dg_det D hD0] at hdet
    exact fun l => Finset.prod_ne_zero_iff.1 hdet l (Finset.mem_univ l)
  have hR : (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ =
      FC_dg D (fun l => (1 - ev l * π l)⁻¹) := by
    rw [h1MP, FC_dg_inv D hD0 _ hne]
  have hK : KTheta (lam D N A) θ z₁ z₂ = FC_dg D (fun l => (1 - ev l * π l)⁻¹ * ev l) := by
    unfold KTheta
    rw [hR, hM, FC_dg_mul D hD0]
  have hPM : PTheta D θ * Mhat (lam D N A) z₁ z₂ = Mhat (lam D N A) z₁ z₂ * PTheta D θ := by
    rw [hM, hP, FC_dg_comm D hD0]
  refine ⟨?_, ?_, ?_⟩
  · rw [FC_Mhat_swap, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_mul, Matrix.transpose_transpose, FC_PTheta_transpose, hPM, hR, hK, hM,
      FC_dg_mul D hD0]
    congr 1
    funext l
    ring
  · rw [hK, hM, FC_dg_mul D hD0, FC_dg_sub, FC_dg_sub, FC_dg_opNorm D hD0]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => ?_
    have e : ev l * ((1 - ev l * π l)⁻¹ * ev l) - ((1 - ev l * π l)⁻¹ * ev l - ev l) =
        ev l ^ 2 * (1 - π l) * (1 - ev l * π l)⁻¹ := by
      field_simp [hne l]
      ring
    rw [e]
    by_cases hl : (l : ℕ) = 0
    · simp [hπ, hl]
    · have hπl : π l = (θ : ℂ) := by simp [hπ, hl]
      rw [hπl, norm_mul, norm_inv]
      have hne' : 1 - (θ : ℂ) * ev l ≠ 0 := by
        have := hne l; rw [hπl] at this; rwa [mul_comm]
      have hpos : 0 < ‖1 - (θ : ℂ) * ev l‖ := norm_pos_iff.2 hne'
      have h2 := (FC_scalar2 (ev l) (hevb l) θ h0 h1).1
      have e2 : (1 : ℂ) - (θ : ℂ) = ((1 - θ : ℝ) : ℂ) := by push_cast; ring
      rw [e2, mul_comm (ev l) (θ : ℂ)]
      rw [mul_inv_le_iff₀ hpos, one_mul]
      exact h2
  · rw [hK, hP, FC_dg_mul D hD0, FC_dg_sub, FC_dg_opNorm D hD0]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => ?_
    by_cases hl : (l : ℕ) = 0
    · simp [hπ, hl]
    · have hπl : π l = (θ : ℂ) := by simp [hπ, hl]
      have hne' : 1 - (θ : ℂ) * ev l ≠ 0 := by
        have := hne l; rw [hπl] at this; rwa [mul_comm]
      have hpos : 0 < ‖1 - (θ : ℂ) * ev l‖ := norm_pos_iff.2 hne'
      have e : π l * ((1 - ev l * π l)⁻¹ * ev l) - (1 - ev l * π l)⁻¹ * ev l =
          -(((1 - θ : ℝ) : ℂ) * ev l) * (1 - (θ : ℂ) * ev l)⁻¹ := by
        rw [hπl, mul_comm (ev l) (θ : ℂ)]
        push_cast
        ring
      rw [e, norm_mul, norm_neg, norm_inv, mul_inv_le_iff₀ hpos, one_mul]
      exact (FC_scalar2 (ev l) (hevb l) θ h0 h1).2

private theorem FC_KThetaB_eq {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ)
    (B : Matrix (Idx D N) (Idx D N) ℂ) (b x : Fin D) :
    KThetaB Λ θ z₂ z₁ B b x = ∑ y, (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ b y *
      ((D : ℂ) * ntr (MExt Λ z₂ * Ea D N y * MExt Λ z₁ * Ea D N x * B)) := rfl

private theorem FC_KTheta_circ (D : ℕ) (hD : 2 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im → ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) →
      (z₂ = z ∨ z₂ = star z) → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
        (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ).det ≠ 0 ∧
        (∀ a b x : Fin D, KThetaB (lam D N A) θ z₂ z₁ (Ea D N a) b x =
          if x = a then KTheta (lam D N A) θ z₁ z₂ a b else 0) ∧
        (∀ b x : Fin D, KThetaB (lam D N A) θ z₂ z₁ 1 b x = KTheta (lam D N A) θ z₁ z₂ x b) ∧
        opNorm (Mhat (lam D N A) z₁ z₂ * KTheta (lam D N A) θ z₁ z₂ -
          (KTheta (lam D N A) θ z₁ z₂ - Mhat (lam D N A) z₁ z₂)) ≤ 1 ∧
        opNorm (PTheta D θ * KTheta (lam D N A) θ z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) ≤ 1 := by
  obtain ⟨N₀, hN₀⟩ := oneSubMhatP_inv_le D hD δA τ hδA hτ
  refine ⟨max N₀ 1, fun N hN A hA z hzn hz z₁ z₂ h₁ h₂ θ h0 h1 => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hd₁₂ := (hN₀ N hN0 A hA z hzn hz z₁ z₂ h₁ h₂ θ h0 h1).1
  have hd₂₁ := (hN₀ N hN0 A hA z hzn hz z₂ z₁ h₂ h₁ θ h0 h1).1
  obtain ⟨hT, hn1, hn2⟩ := FC_circ_core D hD N hN1 A z hz z₁ z₂ h₁ h₂ θ h0 h1 hd₁₂
  have hentry : ∀ b x : Fin D, ∑ y, (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ b y *
      ((D : ℂ) * ntr (MExt (lam D N A) z₂ * Ea D N y * MExt (lam D N A) z₁ * Ea D N x)) =
      KTheta (lam D N A) θ z₁ z₂ x b := by
    intro b x
    rw [← hT, Matrix.transpose_apply, Matrix.mul_apply]
    rfl
  refine ⟨hd₁₂, hd₂₁, fun a b x => ?_, fun b x => ?_, hn1, hn2⟩
  · rw [FC_KThetaB_eq]
    by_cases hxa : x = a
    · subst hxa
      simp only [↓reduceIte]
      rw [← hentry b x]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Matrix.mul_assoc _ (Ea D N x) (Ea D N x), FC_Ea_mul]
      simp
    · simp only [hxa, ↓reduceIte]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [Matrix.mul_assoc _ (Ea D N x) (Ea D N a), FC_Ea_mul]
      simp [hxa, ntr]
  · rw [FC_KThetaB_eq, ← hentry b x]
    simp only [Matrix.mul_one]

end

section

private theorem FCc_diff_slice {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) :
    Differentiable ℝ (fun x : ℂ => setEntry h i j x) := by
  refine differentiable_pi.mpr fun p => differentiable_pi.mpr fun m => ?_
  by_cases hij : i = j
  · subst hij
    by_cases hpm : p = i ∧ m = i
    · have e : (fun x : ℂ => setEntry h i i x p m) = fun x => ((x.re : ℝ) : ℂ) := by
        funext x; simp [setEntry, hpm]
      rw [e]
      exact (Complex.ofRealCLM.comp Complex.reCLM).differentiable
    · have e : (fun x : ℂ => setEntry h i i x p m) = fun _ => h p m := by
        funext x; simp [setEntry, hpm]
      rw [e]
      exact differentiable_const _
  · by_cases h1 : p = i ∧ m = j
    · have e : (fun x : ℂ => setEntry h i j x p m) = fun x => x := by
        funext x; simp [setEntry, hij, h1]
      rw [e]
      exact differentiable_id
    · by_cases h2 : p = j ∧ m = i
      · have e : (fun x : ℂ => setEntry h i j x p m) = fun x => starRingEnd ℂ x := by
          funext x; simp [setEntry, hij, h2]
        rw [e]
        exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiable
      · have e : (fun x : ℂ => setEntry h i j x p m) = fun _ => h p m := by
          funext x; simp [setEntry, hij, h1, h2]
        rw [e]
        exact differentiable_const _

private theorem FCc_diff_res {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (ξ : ℂ) (hξ : ξ.im ≠ 0) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j p m : Idx D N) :
    Differentiable ℝ (fun x : ℂ => res (Matrix.of (setEntry h i j x) + Λ) ξ p m) := by
  have e : (fun x : ℂ => res (Matrix.of (setEntry h i j x) + Λ) ξ p m) =
      (fun h' : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h') + Λ) ξ p m) ∘
        fun x : ℂ => setEntry h i j x := by
    funext x
    simp only [Function.comp]
    rw [symArr_setEntry, symArr_of_isHermitian h hh]
  rw [e]
  exact ((contDiff_res_symArr Λ hΛ ξ hξ p m 1).differentiable (by norm_num)).comp
    (FCc_diff_slice h i j)

private theorem FCc_dW_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) {w : ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) w) :
    dW (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, dW (F a) w := by
  have e : fderiv ℝ (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, fderiv ℝ (F a) w := fderiv_fun_sum hF
  simp only [dW, e, _root_.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

private theorem FCc_dW_const_mul {F : ℂ → ℂ} {w : ℂ} (c : ℂ) (hF : DifferentiableAt ℝ F w) :
    dW (fun x => c * F x) w = c * dW F w := by
  have e : fderiv ℝ (fun x => c * F x) w = c • fderiv ℝ F w := fderiv_const_mul hF c
  simp only [dW, e, _root_.smul_apply, smul_eq_mul]; ring

private theorem FCc_dW_aux {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    ∀ l : List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ),
      (∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) → ∀ k m : Idx D N,
      Differentiable ℝ (fun w => chainB (setEntry h i j w) l k m) ∧
      dW (fun w => chainB (setEntry h i j w) l k m) = fun w =>
        -(if i = j then 1 / 2 else 1) * ∑ r : Fin l.length,
          chainB (setEntry h i j w) (l.take (r + 1)) k i *
            (res (Matrix.of (setEntry h i j w) + (l.get r).2.1) (l.get r).2.2 *
              chainB (setEntry h i j w) (l.drop (r + 1))) j m := by
  intro l
  induction l with
  | nil =>
    intro _ k m
    simp only [chainB, List.map_nil, List.prod_nil]
    refine ⟨differentiable_const _, ?_⟩
    funext w
    simp [dW]
  | cons a t ih =>
    intro hl k m
    have ha := hl a (by simp)
    have ht := ih (fun f hf => hl f (by simp [hf]))
    set Gm : ℂ → Matrix (Idx D N) (Idx D N) ℂ :=
      fun w => res (Matrix.of (setEntry h i j w) + a.2.1) a.2.2 with hGm
    set c : ℂ := -(if i = j then 1 / 2 else 1) with hc
    have hG : ∀ p q, Differentiable ℝ (fun x : ℂ => Gm x p q) := fun p q =>
      FCc_diff_res a.2.1 ha.1 a.2.2 ha.2 h hh i j p q
    have hGd : ∀ w p q, dW (fun x => Gm x p q) w = c * (Gm w p i * Gm w j q) := fun w p q =>
      congrFun (res_dW a.2.1 ha.1 a.2.2 ha.2 h hh i j p q).1 w
    have hcons : ∀ (w : ℂ) (t' : List (Matrix (Idx D N) (Idx D N) ℂ ×
        Matrix (Idx D N) (Idx D N) ℂ × ℂ)), chainB (setEntry h i j w) (a :: t') =
        (a.1 * Gm w) * chainB (setEntry h i j w) t' := fun w t' => by
      simp only [chainB, List.map_cons, List.prod_cons, hGm]
    have hE : (fun w => chainB (setEntry h i j w) (a :: t) k m) = fun w =>
        ∑ q, (∑ s, a.1 k s * Gm w s q) * chainB (setEntry h i j w) t q m := by
      funext w
      rw [hcons w t, Matrix.mul_apply]
      simp only [Matrix.mul_apply]
    have hP : ∀ q, Differentiable ℝ (fun x => ∑ s, a.1 k s * Gm x s q) := fun q =>
      Differentiable.fun_sum fun s _ => (hG s q).const_mul _
    rw [hE]
    refine ⟨Differentiable.fun_sum fun q _ => (hP q).mul (ht q m).1, ?_⟩
    funext w
    have hdw : dW (fun x => ∑ q, (∑ s, a.1 k s * Gm x s q) *
          chainB (setEntry h i j x) t q m) w =
        ∑ q, (dW (fun x => ∑ s, a.1 k s * Gm x s q) w * chainB (setEntry h i j w) t q m +
          (∑ s, a.1 k s * Gm w s q) * dW (fun x => chainB (setEntry h i j x) t q m) w) := by
      rw [FCc_dW_sum Finset.univ (fun q x => (∑ s, a.1 k s * Gm x s q) *
        chainB (setEntry h i j x) t q m) (fun q _ => ((hP q) w).mul ((ht q m).1 w))]
      exact Finset.sum_congr rfl fun q _ => (dW_mul (hP q w) ((ht q m).1 w)).1
    have hP1 : ∀ q, dW (fun x => ∑ s, a.1 k s * Gm x s q) w =
        ∑ s, a.1 k s * (c * (Gm w s i * Gm w j q)) := by
      intro q
      rw [FCc_dW_sum Finset.univ (fun s x => a.1 k s * Gm x s q)
        (fun s _ => ((hG s q) w).const_mul _)]
      exact Finset.sum_congr rfl fun s _ => by
        rw [FCc_dW_const_mul (F := fun x => Gm x s q) _ (hG s q w), hGd]
    have hC : ∀ q, dW (fun x => chainB (setEntry h i j x) t q m) w =
        c * ∑ r : Fin t.length, chainB (setEntry h i j w) (t.take (r + 1)) q i *
          (res (Matrix.of (setEntry h i j w) + (t.get r).2.1) (t.get r).2.2 *
            chainB (setEntry h i j w) (t.drop (r + 1))) j m := fun q => congrFun (ht q m).2 w
    rw [hdw]
    simp only [hP1, hC]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.length_cons, List.get_eq_getElem,
      List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ, List.getElem_cons_zero,
      List.take_zero, List.drop_zero]
    have hnil : chainB (setEntry h i j w) [] = 1 := by simp [chainB]
    have h1 : chainB (setEntry h i j w) [a] = a.1 * Gm w := by
      rw [hcons w [], hnil, mul_one]
    have e2 : ∀ (X : Idx D N → Fin t.length → ℂ) (Y : Fin t.length → ℂ) (P : Idx D N → ℂ),
        ∑ x, P x * (c * ∑ r, X x r * Y r) = c * ∑ r, (∑ x, P x * X x r) * Y r := by
      intro X Y P
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun x _ => by ring
    rw [Finset.sum_add_distrib, mul_add]
    congr 1
    · rw [h1]
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => by ring
    · refine (e2 _ _ _).trans ?_
      congr 1

private theorem FCc_dWbar_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) {w : ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) w) :
    dWbar (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, dWbar (F a) w := by
  have e : fderiv ℝ (fun x => ∑ a ∈ s, F a x) w = ∑ a ∈ s, fderiv ℝ (F a) w := fderiv_fun_sum hF
  simp only [dWbar, e, _root_.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]

private theorem FCc_dWbar_const_mul {F : ℂ → ℂ} {w : ℂ} (c : ℂ) (hF : DifferentiableAt ℝ F w) :
    dWbar (fun x => c * F x) w = c * dWbar F w := by
  have e : fderiv ℝ (fun x => c * F x) w = c • fderiv ℝ F w := fderiv_const_mul hF c
  simp only [dWbar, e, _root_.smul_apply, smul_eq_mul]; ring

private theorem FCc_wd_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) {w : ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) w) (b : Bool) :
    (if b then dWbar else dW) (fun x => ∑ a ∈ s, F a x) w =
      ∑ a ∈ s, (if b then dWbar else dW) (F a) w := by
  cases b
  · exact FCc_dW_sum s F hF
  · exact FCc_dWbar_sum s F hF

abbrev FC_Ch (D N : ℕ) :=
  List (Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ × ℂ)

abbrev FC_Seg := ℕ × ℕ × Bool × Bool

private abbrev FC_Fac := FC_Seg × Bool × Bool

private abbrev FC_Mono := List FC_Fac

private abbrev FC_Poly := List FC_Mono

private def FC_dFac (w : Bool) (f : FC_Fac) : FC_Poly :=
  (List.range (f.1.2.1 - f.1.1)).map fun k =>
    [((f.1.1, f.1.1 + k + 1, f.1.2.2.1, false), f.2.1, w),
      ((f.1.1 + k, f.1.2.1, true, f.1.2.2.2), !w, f.2.2)]

private def FC_dMono (w : Bool) : FC_Mono → FC_Poly
  | [] => []
  | f :: m => (FC_dFac w f).map (· ++ m) ++ (FC_dMono w m).map (f :: ·)

private def FC_dPoly (w : Bool) (P : FC_Poly) : FC_Poly := P.flatMap (FC_dMono w)

def FC_mod {D N : ℕ} (o : Bool) : FC_Ch D N → FC_Ch D N
  | [] => []
  | f :: t => (if o then ((1 : Matrix (Idx D N) (Idx D N) ℂ), f.2) else f) :: t

def FC_segList {D N : ℕ} (ch : FC_Ch D N) (a b : ℕ) (o : Bool) : FC_Ch D N :=
  FC_mod o ((ch.drop a).take (b - a))

def FC_evalSeg {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (ch : FC_Ch D N)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (s : FC_Seg) : Matrix (Idx D N) (Idx D N) ℂ :=
  chainB h (FC_segList ch s.1 s.2.1 s.2.2.1) * (if s.2.2.2 then X else 1)

private def FC_idx {D N : ℕ} (i j : Idx D N) (u : Bool) : Idx D N := if u then j else i

private def FC_evalFac {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (ch : FC_Ch D N)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) (f : FC_Fac) : ℂ :=
  FC_evalSeg h ch X f.1 (FC_idx i j f.2.1) (FC_idx i j f.2.2)

private def FC_evalMono {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (ch : FC_Ch D N)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) (m : FC_Mono) : ℂ :=
  (m.map (FC_evalFac h ch X i j)).prod

private def FC_evalPoly {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (ch : FC_Ch D N)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) (P : FC_Poly) : ℂ :=
  (P.map (FC_evalMono h ch X i j)).sum

private def FC_wd (b : Bool) : (ℂ → ℂ) → ℂ → ℂ := if b then dWbar else dW

private def FC_validF (n : ℕ) (f : FC_Fac) : Prop := f.1.1 < f.1.2.1 ∧ f.1.2.1 ≤ n

private theorem FC_range_sum (n : ℕ) (F : ℕ → ℂ) :
    ((List.range n).map F).sum = ∑ r ∈ Finset.range n, F r := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

private theorem FC_mod_take {D N : ℕ} (o : Bool) (l : FC_Ch D N) (r : ℕ) :
    (FC_mod o l).take (r + 1) = FC_mod o (l.take (r + 1)) := by
  cases l <;> simp [FC_mod]

private theorem FC_mod_drop {D N : ℕ} (o : Bool) (l : FC_Ch D N) (r : ℕ) :
    (FC_mod o l).drop (r + 1) = l.drop (r + 1) := by
  cases l <;> simp [FC_mod]

private theorem FC_mod_length {D N : ℕ} (o : Bool) (l : FC_Ch D N) : (FC_mod o l).length = l.length := by
  cases l <;> simp [FC_mod]

private theorem FC_mod_get2 {D N : ℕ} (o : Bool) (l : FC_Ch D N) (r : ℕ) (hr : r < (FC_mod o l).length)
    (hr' : r < l.length) : ((FC_mod o l)[r]'hr).2 = (l[r]'hr').2 := by
  cases l with
  | nil => simp at hr'
  | cons f t =>
    cases r with
    | zero => cases o <;> simp [FC_mod]
    | succ r => simp [FC_mod]

private theorem FC_mod_mem {D N : ℕ} (o : Bool) (l : FC_Ch D N) (P : _ → Prop)
    (hP : ∀ f ∈ l, P f.2) : ∀ f ∈ FC_mod o l, P f.2 := by
  cases l with
  | nil => simp [FC_mod]
  | cons g t =>
    intro f hf
    simp only [FC_mod, List.mem_cons] at hf
    rcases hf with rfl | hf
    · cases o
      · exact hP g (by simp)
      · exact hP g (by simp)
    · exact hP f (by simp [hf])

private theorem FC_segList_valid {D N : ℕ} (ch : FC_Ch D N)
    (hch : ∀ f ∈ ch, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (a b : ℕ) (o : Bool) :
    ∀ f ∈ FC_segList ch a b o, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
  refine FC_mod_mem o _ (fun g => g.1.IsHermitian ∧ g.2.im ≠ 0) fun f hf => hch f ?_
  exact List.mem_of_mem_drop (List.mem_of_mem_take hf)

private theorem FC_segList_length {D N : ℕ} (ch : FC_Ch D N) (a b : ℕ) (o : Bool) (hb : b ≤ ch.length) :
    (FC_segList ch a b o).length = b - a := by
  unfold FC_segList
  rw [FC_mod_length, List.length_take, List.length_drop]
  omega

private theorem FC_chainB_one_cons {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (g : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (t : FC_Ch D N) :
    chainB h ((1, g) :: t) = res (Matrix.of h + g.1) g.2 * chainB h t := by
  simp [chainB]

private theorem FC_segList_split {D N : ℕ} (ch : FC_Ch D N) (a b : ℕ) (o : Bool) (hb : b ≤ ch.length)
    (r : ℕ) (hr : r < (FC_segList ch a b o).length) (h : Idx D N → Idx D N → ℂ) :
    (FC_segList ch a b o).take (r + 1) = FC_segList ch a (a + r + 1) o ∧
      res (Matrix.of h + ((FC_segList ch a b o)[r]'hr).2.1) ((FC_segList ch a b o)[r]'hr).2.2 *
        chainB h ((FC_segList ch a b o).drop (r + 1)) =
        chainB h (FC_segList ch (a + r) b true) := by
  have hlen := FC_segList_length ch a b o hb
  set l := (ch.drop a).take (b - a) with hl
  have hr' : r < l.length := by
    have := FC_mod_length o l
    have h2 : (FC_segList ch a b o).length = (FC_mod o l).length := rfl
    omega
  constructor
  · unfold FC_segList
    rw [FC_mod_take, List.take_take]
    congr 2
    omega
  · have hget := FC_mod_get2 o l r hr hr'
    have e1 : (FC_segList ch a b o)[r]'hr = (FC_mod o l)[r]'hr := rfl
    rw [e1]
    have e2 : (FC_segList ch a b o).drop (r + 1) = l.drop (r + 1) := FC_mod_drop o l r
    rw [e2, ← FC_chainB_one_cons, hget]
    have e3 : l.drop r = l[r]'hr' :: l.drop (r + 1) := List.drop_eq_getElem_cons hr'
    have e4 : ((1 : Matrix (Idx D N) (Idx D N) ℂ), (l[r]'hr').2) :: l.drop (r + 1) =
        FC_mod true (l.drop r) := by rw [e3]; simp [FC_mod]
    rw [e4]
    unfold FC_segList
    congr 2
    rw [hl, List.drop_take, List.drop_drop]
    congr 1
    omega

private theorem FC_chain_wd {D N : ℕ} (l : FC_Ch D N) (hl : ∀ f ∈ l, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j k m : Idx D N) (b : Bool) :
    FC_wd b (fun w => chainB (setEntry h i j w) l k m) = fun w =>
      -(if i = j then 1 / 2 else 1) * ∑ r : Fin l.length,
        chainB (setEntry h i j w) (l.take (r + 1)) k (FC_idx i j b) *
          (res (Matrix.of (setEntry h i j w) + (l.get r).2.1) (l.get r).2.2 *
            chainB (setEntry h i j w) (l.drop (r + 1))) (FC_idx i j (!b)) m := by
  cases b
  · exact chainB_dW l hl h hh i j k m
  · exact chainB_dWbar l hl h hh i j k m

private theorem FC_wd_const_mul {F : ℂ → ℂ} {w : ℂ} (c : ℂ) (hF : DifferentiableAt ℝ F w) (b : Bool) :
    FC_wd b (fun x => c * F x) w = c * FC_wd b F w := by
  cases b
  · exact FCc_dW_const_mul c hF
  · exact FCc_dWbar_const_mul c hF

private theorem FC_wd_mul {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w)
    (hg : DifferentiableAt ℝ g w) (b : Bool) :
    FC_wd b (fun x => f x * g x) w = FC_wd b f w * g w + f w * FC_wd b g w := by
  cases b
  · exact (dW_mul hf hg).1
  · exact (dW_mul hf hg).2

private theorem FC_wd_add {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w)
    (hg : DifferentiableAt ℝ g w) (b : Bool) :
    FC_wd b (fun x => f x + g x) w = FC_wd b f w + FC_wd b g w := by
  have e : fderiv ℝ (fun x => f x + g x) w = fderiv ℝ f w + fderiv ℝ g w := fderiv_add hf hg
  cases b
  · simp only [FC_wd, Bool.false_eq_true, ↓reduceIte, dW, e, ContinuousLinearMap.add_apply]
    ring
  · simp only [FC_wd, ↓reduceIte, dWbar, e, ContinuousLinearMap.add_apply]
    ring

private theorem FC_wd_const (c : ℂ) (b : Bool) : FC_wd b (fun _ => c) = fun _ => 0 := by
  funext w
  cases b <;> simp [FC_wd, dW, dWbar]

private theorem FC_fac_d {D N : ℕ} (ch : FC_Ch D N) (hch : ∀ f ∈ ch, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (f : FC_Fac)
    (hf : FC_validF ch.length f) :
    Differentiable ℝ (fun w => FC_evalFac (setEntry h i j w) ch X i j f) ∧
      ∀ b : Bool, FC_wd b (fun w => FC_evalFac (setEntry h i j w) ch X i j f) = fun w =>
        -(if i = j then 1 / 2 else 1) * FC_evalPoly (setEntry h i j w) ch X i j (FC_dFac b f) := by
  obtain ⟨⟨a, b', o, x⟩, u, v⟩ := f
  obtain ⟨hab, hb'⟩ := hf
  simp only at hab hb'
  set L := FC_segList ch a b' o with hL
  have hLv := FC_segList_valid ch hch a b' o
  have hlen : L.length = b' - a := FC_segList_length ch a b' o hb'
  set Y : Matrix (Idx D N) (Idx D N) ℂ := if x then X else 1 with hY
  have hE : (fun w => FC_evalFac (setEntry h i j w) ch X i j ((a, b', o, x), u, v)) = fun w =>
      ∑ γ, Y γ (FC_idx i j v) * chainB (setEntry h i j w) L (FC_idx i j u) γ := by
    funext w
    simp only [FC_evalFac, FC_evalSeg, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun γ _ => by rw [mul_comm]
  have hdiff : ∀ γ, Differentiable ℝ (fun w => chainB (setEntry h i j w) L (FC_idx i j u) γ) :=
    fun γ => (FCc_dW_aux h hh i j L hLv (FC_idx i j u) γ).1
  rw [hE]
  refine ⟨Differentiable.fun_sum fun γ _ => (hdiff γ).const_mul _, fun b => ?_⟩
  funext w
  unfold FC_wd
  rw [FCc_wd_sum Finset.univ _ (fun γ _ => ((hdiff γ) w).const_mul _) b]
  have hT : ∀ γ, (if b then dWbar else dW)
      (fun w' => Y γ (FC_idx i j v) * chainB (setEntry h i j w') L (FC_idx i j u) γ) w =
      Y γ (FC_idx i j v) * (-(if i = j then 1 / 2 else 1) * ∑ r : Fin L.length,
        chainB (setEntry h i j w) (L.take (r + 1)) (FC_idx i j u) (FC_idx i j b) *
          (res (Matrix.of (setEntry h i j w) + (L.get r).2.1) (L.get r).2.2 *
            chainB (setEntry h i j w) (L.drop (r + 1))) (FC_idx i j (!b)) γ) := by
    intro γ
    have := FC_wd_const_mul (Y γ (FC_idx i j v)) ((hdiff γ) w) b
    simp only [FC_wd] at this
    rw [this]
    congr 1
    have h2 := congrFun (FC_chain_wd L hLv h hh i j (FC_idx i j u) γ b) w
    simp only [FC_wd] at h2
    exact h2
  simp only [hT]
  have hsplit := fun (r : Fin L.length) => FC_segList_split ch a b' o hb' r r.2 (setEntry h i j w)
  have hR : FC_evalPoly (setEntry h i j w) ch X i j (FC_dFac b ((a, b', o, x), u, v)) =
      ∑ r ∈ Finset.range (b' - a),
        chainB (setEntry h i j w) (FC_segList ch a (a + r + 1) o) (FC_idx i j u) (FC_idx i j b) *
          (chainB (setEntry h i j w) (FC_segList ch (a + r) b' true) * Y)
            (FC_idx i j (!b)) (FC_idx i j v) := by
    unfold FC_evalPoly FC_dFac
    rw [List.map_map, ← FC_range_sum]
    congr 1
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp, FC_evalMono, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, FC_evalFac, FC_evalSeg, Bool.false_eq_true, ↓reduceIte, hY]
  rw [hR]
  have hL2 : ∀ r : Fin L.length, chainB (setEntry h i j w) (L.take (r + 1)) (FC_idx i j u)
      (FC_idx i j b) = chainB (setEntry h i j w) (FC_segList ch a (a + r + 1) o) (FC_idx i j u)
      (FC_idx i j b) := fun r => by rw [(hsplit r).1]
  have hL3 : ∀ (r : Fin L.length) (γ : Idx D N),
      (res (Matrix.of (setEntry h i j w) + (L.get r).2.1) (L.get r).2.2 *
        chainB (setEntry h i j w) (L.drop (r + 1))) (FC_idx i j (!b)) γ =
      chainB (setEntry h i j w) (FC_segList ch (a + r) b' true) (FC_idx i j (!b)) γ := by
    intro r γ
    have := (hsplit r).2
    rw [List.get_eq_getElem, this]
  simp only [hL2, hL3]
  rw [← hlen, ← Fin.sum_univ_eq_sum_range (fun r => chainB (setEntry h i j w)
    (FC_segList ch a (a + r + 1) o) (FC_idx i j u) (FC_idx i j b) *
      (chainB (setEntry h i j w) (FC_segList ch (a + r) b' true) * Y)
        (FC_idx i j (!b)) (FC_idx i j v))]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun γ _ => ?_
  ring

section FC_eval
variable {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (ch : FC_Ch D N) (X : Matrix (Idx D N) (Idx D N) ℂ)
  (i j : Idx D N)

private theorem FC_evalPoly_append (P Q : FC_Poly) :
    FC_evalPoly h ch X i j (P ++ Q) = FC_evalPoly h ch X i j P + FC_evalPoly h ch X i j Q := by
  simp [FC_evalPoly]

private theorem FC_evalPoly_map_append (P : FC_Poly) (m : FC_Mono) :
    FC_evalPoly h ch X i j (P.map (· ++ m)) =
      FC_evalPoly h ch X i j P * FC_evalMono h ch X i j m := by
  induction P with
  | nil => simp [FC_evalPoly]
  | cons t P ih =>
    simp only [FC_evalPoly, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, add_mul]
    simp [FC_evalMono, List.prod_append]

private theorem FC_evalPoly_map_cons (P : FC_Poly) (f : FC_Fac) :
    FC_evalPoly h ch X i j (P.map (f :: ·)) =
      FC_evalFac h ch X i j f * FC_evalPoly h ch X i j P := by
  induction P with
  | nil => simp [FC_evalPoly]
  | cons t P ih =>
    simp only [FC_evalPoly, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    simp [FC_evalMono]

private theorem FC_evalMono_cons (f : FC_Fac) (m : FC_Mono) :
    FC_evalMono h ch X i j (f :: m) = FC_evalFac h ch X i j f * FC_evalMono h ch X i j m := by
  simp [FC_evalMono]

private theorem FC_evalPoly_cons (m : FC_Mono) (P : FC_Poly) :
    FC_evalPoly h ch X i j (m :: P) = FC_evalMono h ch X i j m + FC_evalPoly h ch X i j P := by
  simp [FC_evalPoly]

end FC_eval

private theorem FC_dFac_valid (n : ℕ) (b : Bool) (f : FC_Fac) (hf : FC_validF n f) :
    ∀ t ∈ FC_dFac b f, ∀ g ∈ t, FC_validF n g := by
  intro t ht g hg
  simp only [FC_dFac, List.mem_map, List.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  obtain ⟨h1, h2⟩ := hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨by simp, by simp; omega⟩
  · exact ⟨by simp; omega, by simpa using h2⟩

private theorem FC_dMono_valid (n : ℕ) (b : Bool) (m : FC_Mono) (hm : ∀ f ∈ m, FC_validF n f) :
    ∀ t ∈ FC_dMono b m, ∀ g ∈ t, FC_validF n g := by
  induction m with
  | nil => simp [FC_dMono]
  | cons f m ih =>
    intro t ht g hg
    simp only [FC_dMono, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩
    · rcases List.mem_append.1 hg with hg | hg
      · exact FC_dFac_valid n b f (hm f (by simp)) t' ht' g hg
      · exact hm g (by simp [hg])
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact hm _ (by simp)
      · exact ih (fun f' hf' => hm f' (by simp [hf'])) t' ht' g hg

private theorem FC_dPoly_valid (n : ℕ) (b : Bool) (P : FC_Poly) (hP : ∀ m ∈ P, ∀ f ∈ m, FC_validF n f) :
    ∀ t ∈ FC_dPoly b P, ∀ g ∈ t, FC_validF n g := by
  intro t ht
  simp only [FC_dPoly, List.mem_flatMap] at ht
  obtain ⟨m, hm, ht⟩ := ht
  exact FC_dMono_valid n b m (hP m hm) t ht

private theorem FC_iter_valid (n : ℕ) (b : Bool) (P : FC_Poly) (hP : ∀ m ∈ P, ∀ f ∈ m, FC_validF n f)
    (k : ℕ) : ∀ t ∈ (FC_dPoly b)^[k] P, ∀ g ∈ t, FC_validF n g := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact FC_dPoly_valid n b _ ih

section FC_deriv
variable {D N : ℕ} (ch : FC_Ch D N) (hch : ∀ f ∈ ch, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
  (X : Matrix (Idx D N) (Idx D N) ℂ) (h : Idx D N → Idx D N → ℂ)
  (hh : (Matrix.of h).IsHermitian) (i j : Idx D N)
include hch hh

private theorem FC_mono_d (m : FC_Mono) (hm : ∀ f ∈ m, FC_validF ch.length f) :
    Differentiable ℝ (fun w => FC_evalMono (setEntry h i j w) ch X i j m) ∧
      ∀ b : Bool, FC_wd b (fun w => FC_evalMono (setEntry h i j w) ch X i j m) = fun w =>
        -(if i = j then 1 / 2 else 1) * FC_evalPoly (setEntry h i j w) ch X i j (FC_dMono b m) := by
  induction m with
  | nil =>
    refine ⟨by simp [FC_evalMono], fun b => ?_⟩
    simp only [FC_evalMono, List.map_nil, List.prod_nil, FC_dMono]
    rw [FC_wd_const]
    funext w
    simp [FC_evalPoly]
  | cons f m ih =>
    have hf := FC_fac_d ch hch X h hh i j f (hm f (by simp))
    have ih' := ih fun f' hf' => hm f' (by simp [hf'])
    have e : (fun w => FC_evalMono (setEntry h i j w) ch X i j (f :: m)) = fun w =>
        FC_evalFac (setEntry h i j w) ch X i j f * FC_evalMono (setEntry h i j w) ch X i j m := by
      funext w; exact FC_evalMono_cons _ _ _ _ _ _ _
    rw [e]
    refine ⟨hf.1.mul ih'.1, fun b => ?_⟩
    funext w
    rw [FC_wd_mul (hf.1 w) (ih'.1 w) b, congrFun (hf.2 b) w, congrFun (ih'.2 b) w]
    simp only [FC_dMono, FC_evalPoly_append, FC_evalPoly_map_append, FC_evalPoly_map_cons]
    ring

private theorem FC_poly_d (P : FC_Poly) (hP : ∀ m ∈ P, ∀ f ∈ m, FC_validF ch.length f) :
    Differentiable ℝ (fun w => FC_evalPoly (setEntry h i j w) ch X i j P) ∧
      ∀ b : Bool, FC_wd b (fun w => FC_evalPoly (setEntry h i j w) ch X i j P) = fun w =>
        -(if i = j then 1 / 2 else 1) * FC_evalPoly (setEntry h i j w) ch X i j (FC_dPoly b P) := by
  induction P with
  | nil =>
    refine ⟨by simp [FC_evalPoly], fun b => ?_⟩
    simp only [FC_evalPoly, List.map_nil, List.sum_nil, FC_dPoly, List.flatMap_nil]
    rw [FC_wd_const]
    funext w
    simp
  | cons m P ih =>
    have hm := FC_mono_d ch hch X h hh i j m (hP m (by simp))
    have ih' := ih fun m' hm' => hP m' (by simp [hm'])
    have e : (fun w => FC_evalPoly (setEntry h i j w) ch X i j (m :: P)) = fun w =>
        FC_evalMono (setEntry h i j w) ch X i j m + FC_evalPoly (setEntry h i j w) ch X i j P := by
      funext w; exact FC_evalPoly_cons _ _ _ _ _ _ _
    rw [e]
    refine ⟨hm.1.add ih'.1, fun b => ?_⟩
    funext w
    rw [FC_wd_add (hm.1 w) (ih'.1 w) b, congrFun (hm.2 b) w, congrFun (ih'.2 b) w]
    simp only [FC_dPoly, List.flatMap_cons, FC_evalPoly_append]
    ring

private theorem FC_wirt_eq (P : FC_Poly) (hP : ∀ m ∈ P, ∀ f ∈ m, FC_validF ch.length f) (p q : ℕ) :
    wirt p q (fun w => FC_evalPoly (setEntry h i j w) ch X i j P) = fun w =>
      (-(if i = j then 1 / 2 else 1)) ^ (p + q) *
        FC_evalPoly (setEntry h i j w) ch X i j ((FC_dPoly false)^[p] ((FC_dPoly true)^[q] P)) := by
  set c : ℂ := -(if i = j then 1 / 2 else 1) with hc
  have step : ∀ (b : Bool) (Q : FC_Poly), (∀ m ∈ Q, ∀ f ∈ m, FC_validF ch.length f) →
      ∀ k : ℂ, FC_wd b (fun w => k * FC_evalPoly (setEntry h i j w) ch X i j Q) = fun w =>
        k * c * FC_evalPoly (setEntry h i j w) ch X i j (FC_dPoly b Q) := by
    intro b Q hQ k
    have hd := FC_poly_d ch hch X h hh i j Q hQ
    funext w
    rw [FC_wd_const_mul k (hd.1 w) b, congrFun (hd.2 b) w]
    ring
  have hb : ∀ n : ℕ, dWbar^[n] (fun w => FC_evalPoly (setEntry h i j w) ch X i j P) = fun w =>
      c ^ n * FC_evalPoly (setEntry h i j w) ch X i j ((FC_dPoly true)^[n] P) := by
    intro n
    induction n with
    | zero => funext w; simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      have := step true _ (FC_iter_valid ch.length true P hP n) (c ^ n)
      simp only [FC_wd, ↓reduceIte] at this
      rw [this]
      funext w
      ring
  have ha : ∀ n : ℕ, dW^[n] (fun w => c ^ q *
      FC_evalPoly (setEntry h i j w) ch X i j ((FC_dPoly true)^[q] P)) = fun w =>
      c ^ (n + q) * FC_evalPoly (setEntry h i j w) ch X i j
        ((FC_dPoly false)^[n] ((FC_dPoly true)^[q] P)) := by
    intro n
    induction n with
    | zero => funext w; simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      have := step false _ (FC_iter_valid ch.length false _
        (FC_iter_valid ch.length true P hP q) n) (c ^ (n + q))
      simp only [FC_wd, Bool.false_eq_true, ↓reduceIte] at this
      rw [this]
      funext w
      ring
  unfold wirt
  rw [hb q, ha p]

end FC_deriv

end

section

private def FClPair : ℝ × ℝ →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I

private theorem FClPair_apply (p : ℝ × ℝ) : FClPair p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
  simp [FClPair, Complex.real_smul]

private theorem FCl_cGauss_eq : (cGauss : Measure ℂ) =
    ((gaussianReal 0 (1 / 2 : ℝ≥0)).prod (gaussianReal 0 (1 / 2 : ℝ≥0))).map FClPair := by
  have : (FClPair : ℝ × ℝ → ℂ) = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    funext p; exact FClPair_apply p
  rw [this]
  rfl

private instance FCl_cGauss_isGaussian : IsGaussian (cGauss : Measure ℂ) := by
  rw [FCl_cGauss_eq]
  infer_instance

private theorem FCl_cGauss_int (p : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ p) (cGauss : Measure ℂ) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · exact (IsGaussian.memLp_id (cGauss : Measure ℂ) (p : ENNReal) (by simp)).integrable_norm_pow
      hp.ne'

private theorem FCl_ccum_map_conj (ρ : Measure ℂ) (p q : ℕ) :
    ccum (ρ.map (starRingEnd ℂ)) p q = starRingEnd ℂ (ccum ρ p q) := by
  unfold ccum jointCum
  rw [map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hB : ∀ B ∈ π.parts, ∫ z, ∏ i ∈ B, (fun i : Fin (p + q) =>
      if (i : ℕ) < p then (fun z : ℂ => z) else (fun z => starRingEnd ℂ z)) i z
        ∂(ρ.map (starRingEnd ℂ)) = starRingEnd ℂ (∫ z, ∏ i ∈ B, (fun i : Fin (p + q) =>
      if (i : ℕ) < p then (fun z : ℂ => z) else (fun z => starRingEnd ℂ z)) i z ∂ρ) := by
    intro B _
    have hc : Continuous (fun z : ℂ => ∏ i ∈ B, (fun i : Fin (p + q) =>
        if (i : ℕ) < p then (fun z : ℂ => z) else (fun z => starRingEnd ℂ z)) i z) := by
      refine continuous_finsetProd _ fun i _ => ?_
      by_cases h : (i : ℕ) < p
      · simp only [h, ite_true]; exact continuous_id
      · simp only [h, ite_false]; exact Complex.continuous_conj
    rw [integral_map Complex.continuous_conj.aemeasurable hc.aestronglyMeasurable,
      ← integral_conj]
    congr 1
    funext z
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) < p <;> simp [h]
  rw [Finset.prod_congr rfl hB, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast,
    map_prod]

private theorem FCl_sum_law {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P : Measure Ω₁) (Q : Measure Ω₂) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω₁ → ℂ) (g : Ω₂ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfi : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) (P.map f))
    (hgi : ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) (Q.map g)) (a b : ℝ) (p q : ℕ)
    (hpq : 1 ≤ p + q) :
    ccum ((P.prod Q).map fun ω => (a : ℂ) * f ω.1 + (b : ℂ) * g ω.2) p q =
      (a : ℂ) ^ (p + q) * ccum (P.map f) p q + (b : ℂ) ^ (p + q) * ccum (Q.map g) p q := by
  have hsc : ∀ (ρ : Measure ℂ) (c : ℝ), (∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) ρ) →
      ∀ k : ℕ, Integrable (fun z : ℂ => ‖z‖ ^ k) (ρ.map fun z => (c : ℂ) * z) := by
    intro ρ c hρ k
    have hc : Continuous (fun z : ℂ => ‖z‖ ^ k) := by fun_prop
    have hm : Measurable (fun z : ℂ => (c : ℂ) * z) := measurable_id.const_mul _
    rw [integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable]
    simpa [Function.comp_def, norm_mul, mul_pow] using (hρ k).const_mul (|c| ^ k)
  have hmap : (P.prod Q).map (fun ω => (a : ℂ) * f ω.1 + (b : ℂ) * g ω.2) =
      ((P.map f).map fun z => (a : ℂ) * z).conv ((Q.map g).map fun z => (b : ℂ) * z) := by
    have hma : Measurable (fun z : ℂ => (a : ℂ) * z) := measurable_id.const_mul _
    have hmb : Measurable (fun z : ℂ => (b : ℂ) * z) := measurable_id.const_mul _
    have h1 : (P.map f).map (fun z => (a : ℂ) * z) = P.map (fun x => (a : ℂ) * f x) :=
      Measure.map_map hma hf
    have h2 : (Q.map g).map (fun z => (b : ℂ) * z) = Q.map (fun x => (b : ℂ) * g x) :=
      Measure.map_map hmb hg
    rw [h1, h2, Measure.conv, Measure.map_prod_map _ _ (hf.const_mul (a : ℂ))
      (hg.const_mul (b : ℂ)), Measure.map_map (g := fun x : ℂ × ℂ => x.1 + x.2)
      (measurable_fst.add measurable_snd)
      ((hf.const_mul (a : ℂ)).prodMap (hg.const_mul (b : ℂ)))]
    rfl
  rw [hmap, ccum_conv _ _ (hsc _ a hfi) (hsc _ b hgi) p q hpq, ccum_map_smul, ccum_map_smul]

private theorem FCl_meas_wig (n : ℕ) (i j : Fin n) :
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

private theorem FCl_meas_blockEmb (D N : ℕ) : Measurable (blockEmb D N) := by
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

private theorem FCl_meas_phi (D N : ℕ) (t : ℝ) :
    Measurable fun p : (Fin D → Coords N) × Coords (D * N) =>
      Real.exp (-t / 2) • blockEmb D N p.1 + Real.sqrt (1 - Real.exp (-t)) • p.2 :=
  (((FCl_meas_blockEmb D N).comp measurable_fst).const_smul (Real.exp (-t / 2))).add
    (measurable_snd.const_smul (Real.sqrt (1 - Real.exp (-t))))

private theorem FCl_meas_psi (D N : ℕ) :
    Measurable fun c : Coords (D * N) => Matrix.of.symm
      ((wig (D * N) c).submatrix finProdFinEquiv finProdFinEquiv) :=
  measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q =>
    FCl_meas_wig (D * N) (finProdFinEquiv p) (finProdFinEquiv q)

private theorem FCl_entry_law (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (i j : Idx D N) :
    (ouMatLaw D N L t).map (fun h => h i j) =
      ((blockLaw D N L).prod (gueLaw (D * N))).map fun ω =>
        ((Real.exp (-t / 2) : ℝ) : ℂ) * blockH D N ω.1 i j +
          ((Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ) *
            wig (D * N) ω.2 (finProdFinEquiv i) (finProdFinEquiv j) := by
  have hev : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  unfold ouMatLaw ouLaw
  rw [Measure.map_map (FCl_meas_psi D N) (FCl_meas_phi D N t),
    Measure.map_map hev ((FCl_meas_psi D N).comp (FCl_meas_phi D N t))]
  congr 1
  funext ω
  change wig (D * N) (Real.exp (-t / 2) • blockEmb D N ω.1 + Real.sqrt (1 - Real.exp (-t)) • ω.2)
      (finProdFinEquiv i) (finProdFinEquiv j) = _
  rw [wig_add, wig_smul, wig_smul]
  have h := congrFun (congrFun (wig_blockEmb D N ω.1) i) j
  simp only [Matrix.submatrix_apply] at h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h]

private theorem FCl_mp_gue (n : ℕ) (k l : Fin n) :
    MeasurePreserving (fun W : Coords n => W.2 k l) (gueLaw n) (cGauss : Measure ℂ) := by
  unfold gueLaw
  have h4 : MeasurePreserving (fun z : Fin n → ℂ => z l)
      (Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)) (cGauss : Measure ℂ) :=
    measurePreserving_eval (fun _ : Fin n => (cGauss : Measure ℂ)) l
  have h3 : MeasurePreserving (fun z : Fin n → Fin n → ℂ => z k)
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ))
      (Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)) :=
    measurePreserving_eval (fun _ : Fin n => Measure.pi fun _ : Fin n => (cGauss : Measure ℂ)) k
  exact h4.comp (h3.comp measurePreserving_snd)

private theorem FCl_mp_block (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (c : Fin D) (k l : Fin N) :
    MeasurePreserving (fun w : Fin D → Coords N => (w c).2 k l) (blockLaw D N L)
      (L.νo : Measure ℂ) := by
  have h1 : MeasurePreserving (fun w : Fin D → Coords N => w c) (blockLaw D N L)
      (coordLaw N L) := by
    unfold blockLaw
    have : IsProbabilityMeasure (coordLaw N L) := by unfold coordLaw; infer_instance
    exact measurePreserving_eval (fun _ : Fin D => coordLaw N L) c
  have h2 : MeasurePreserving (Prod.snd : Coords N → Fin N → Fin N → ℂ) (coordLaw N L)
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) := by
    unfold coordLaw
    exact measurePreserving_snd
  have h3 := measurePreserving_eval
    (fun _ : Fin N => Measure.pi fun _ : Fin N => (L.νo : Measure ℂ)) k
  have h4 := measurePreserving_eval (fun _ : Fin N => (L.νo : Measure ℂ)) l
  exact h4.comp (h3.comp (h2.comp h1))

private theorem FCl_wig_upper (n : ℕ) (c : Coords n) (k l : Fin n) (h : k < l) :
    wig n c k l = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * c.2 k l := by
  simp [wig, h.ne, h]

private def FClA (D N : ℕ) (t : ℝ) (i j : Idx D N) : ℝ :=
  if i.1 = j.1 then Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) else 0

private def FClB (D N : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (1 - Real.exp (-t)) * ((D * N : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

private def FClF (D N : ℕ) (t : ℝ) (i j : Idx D N)
    (ω : (Fin D → Coords N) × Coords (D * N)) : ℂ :=
  ((FClA D N t i j : ℝ) : ℂ) * (ω.1 i.1).2 i.2 j.2 +
    ((FClB D N t : ℝ) : ℂ) * ω.2.2 (finProdFinEquiv i) (finProdFinEquiv j)

private theorem FCl_meas_F (D N : ℕ) (t : ℝ) (i j : Idx D N) : Measurable (FClF D N t i j) := by
  unfold FClF
  refine (Measurable.const_mul ?_ _).add (Measurable.const_mul ?_ _)
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)))
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (measurable_snd.comp measurable_snd))

private theorem FCl_E_upper (D N : ℕ) (t : ℝ) (i j : Idx D N)
    (hkl : finProdFinEquiv i < finProdFinEquiv j) (ω : (Fin D → Coords N) × Coords (D * N)) :
    ((Real.exp (-t / 2) : ℝ) : ℂ) * blockH D N ω.1 i j +
      ((Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ) *
        wig (D * N) ω.2 (finProdFinEquiv i) (finProdFinEquiv j) = FClF D N t i j ω := by
  rw [FCl_wig_upper _ _ _ _ hkl]
  unfold FClF FClA FClB
  by_cases h : i.1 = j.1
  · have hij : i.2 < j.2 := by
      have h1 : (i.1 : ℕ) = j.1 := by rw [h]
      have h2 : (finProdFinEquiv i : ℕ) < finProdFinEquiv j := hkl
      simp only [finProdFinEquiv_apply_val] at h2
      rw [h1] at h2
      omega
    simp only [blockH, h, ite_true]
    rw [FCl_wig_upper _ _ _ _ hij]
    push_cast
    ring
  · simp [blockH, h]
    ring

private theorem FCl_entry_upper (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (i j : Idx D N)
    (hkl : finProdFinEquiv i < finProdFinEquiv j) :
    (ouMatLaw D N L t).map (fun h => h i j) =
      ((blockLaw D N L).prod (gueLaw (D * N))).map (FClF D N t i j) := by
  rw [FCl_entry_law]
  congr 1
  funext ω
  exact FCl_E_upper D N t i j hkl ω

private theorem FCl_wig_star (n : ℕ) (c : Coords n) (k l : Fin n) :
    star (wig n c l k) = wig n c k l := by
  simp only [wig, star_mul', Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy k l with h | h | h
  · simp [h, h.ne, h.not_gt, h.ne']
  · subst h
    simp
  · simp [h, h.ne, h.not_gt, h.ne']

private theorem FCl_blockH_star (D N : ℕ) (w : Fin D → Coords N) (i j : Idx D N) :
    star (blockH D N w j i) = blockH D N w i j := by
  by_cases h : i.1 = j.1
  · have h' : j.1 = i.1 := h.symm
    simp only [blockH, h', ↓reduceIte]
    exact FCl_wig_star N (w i.1) i.2 j.2
  · have h' : ¬ j.1 = i.1 := fun e => h e.symm
    simp [blockH, h, h']

private theorem FCl_entry_lower (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (i j : Idx D N)
    (hlk : finProdFinEquiv j < finProdFinEquiv i) :
    (ouMatLaw D N L t).map (fun h => h i j) =
      ((ouMatLaw D N L t).map (fun h => h j i)).map (starRingEnd ℂ) := by
  rw [FCl_entry_upper D N L t j i hlk, FCl_entry_law,
    Measure.map_map Complex.continuous_conj.measurable (FCl_meas_F D N t j i)]
  congr 1
  funext ω
  rw [Function.comp_apply, ← FCl_E_upper D N t j i hlk ω]
  simp only [map_add, map_mul, Complex.conj_ofReal]
  have h1 := FCl_blockH_star D N ω.1 i j
  have h2 := FCl_wig_star (D * N) ω.2 (finProdFinEquiv i) (finProdFinEquiv j)
  simp only [Complex.star_def] at h1 h2
  rw [h1, h2]

private theorem FCl_ccum_upper (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (i j : Idx D N)
    (hkl : finProdFinEquiv i < finProdFinEquiv j) (p q : ℕ) (hpq : 1 ≤ p + q) :
    ccum ((ouMatLaw D N L t).map fun h => h i j) p q =
      ((FClA D N t i j : ℝ) : ℂ) ^ (p + q) * ccum (L.νo : Measure ℂ) p q +
        ((FClB D N t : ℝ) : ℂ) ^ (p + q) * ccum (cGauss : Measure ℂ) p q := by
  have := blockLaw_isProbabilityMeasure D N L
  have := gueLaw_isProbabilityMeasure (D * N)
  rw [FCl_entry_upper D N L t i j hkl]
  have e1 := (FCl_mp_block D N L i.1 i.2 j.2).map_eq
  have e2 := (FCl_mp_gue (D * N) (finProdFinEquiv i) (finProdFinEquiv j)).map_eq
  have hf : Measurable fun w : Fin D → Coords N => (w i.1).2 i.2 j.2 :=
    (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (measurable_snd.comp (measurable_pi_apply _)))
  have hg : Measurable fun W : Coords (D * N) => W.2 (finProdFinEquiv i) (finProdFinEquiv j) :=
    (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd)
  have := FCl_sum_law (blockLaw D N L) (gueLaw (D * N)) _ _ hf hg
    (fun k => by rw [e1]; exact L.into k) (fun k => by rw [e2]; exact FCl_cGauss_int k)
    (FClA D N t i j) (FClB D N t) p q hpq
  rw [e1, e2] at this
  exact this

section FC_bil
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem FC_form_le (T : Matrix ι ι ℂ) (x y : ι → ℂ) :
    ‖star x ⬝ᵥ (T *ᵥ y)‖ ≤ opNorm T * Real.sqrt (∑ k, ‖x k‖ ^ 2) *
      Real.sqrt (∑ k, ‖y k‖ ^ 2) := by
  have e : star x ⬝ᵥ (T *ᵥ y) =
      inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanLin T (WithLp.toLp 2 y)) := by
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
  have hx' : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = Real.sqrt (∑ k, ‖x k‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
  have hy' : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ = Real.sqrt (∑ k, ‖y k‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
  have h1 : Matrix.toEuclideanLin T (WithLp.toLp 2 y) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y) := rfl
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y)‖ ≤
      opNorm T * Real.sqrt (∑ k, ‖y k‖ ^ 2) := by
    rw [← hy']; exact ContinuousLinearMap.le_opNorm _ _
  rw [e, h1]
  calc ‖inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y))‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y)‖ := norm_inner_le_norm _ _
    _ ≤ Real.sqrt (∑ k, ‖x k‖ ^ 2) * (opNorm T * Real.sqrt (∑ k, ‖y k‖ ^ 2)) := by
        rw [hx']; exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = _ := by ring

private theorem FC_mulVec_sq_le (T : Matrix ι ι ℂ) (y : ι → ℂ) :
    ∑ k, ‖(T *ᵥ y) k‖ ^ 2 ≤ opNorm T ^ 2 * ∑ k, ‖y k‖ ^ 2 := by
  have hy' : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ = Real.sqrt (∑ k, ‖y k‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
  have hT : ‖(WithLp.toLp 2 (T *ᵥ y) : EuclideanSpace ℂ ι)‖ =
      Real.sqrt (∑ k, ‖(T *ᵥ y) k‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y)‖ ≤
      opNorm T * Real.sqrt (∑ k, ‖y k‖ ^ 2) := by
    rw [← hy']; exact ContinuousLinearMap.le_opNorm _ _
  rw [Matrix.toEuclideanCLM_toLp, hT] at h2
  have h0 : 0 ≤ opNorm T := by unfold opNorm; exact norm_nonneg _
  have hs1 := Real.sq_sqrt (Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) =>
    sq_nonneg ‖(T *ᵥ y) k‖)
  have hs2 := Real.sq_sqrt (Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => sq_nonneg ‖y k‖)
  have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  rw [mul_pow, hs1, hs2] at h3
  exact h3

private theorem FC_bil_le (T : Matrix ι ι ℂ) (x y : ι → ℂ) :
    ‖∑ a, ∑ b, x a * T a b * y b‖ ≤ opNorm T * Real.sqrt (∑ k, ‖x k‖ ^ 2) *
      Real.sqrt (∑ k, ‖y k‖ ^ 2) := by
  have e : ∑ a, ∑ b, x a * T a b * y b = star (star x) ⬝ᵥ (T *ᵥ y) := by
    simp only [star_star, dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hn : ∑ k, ‖(star x) k‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := by simp
  rw [e]
  refine (FC_form_le T (star x) y).trans (le_of_eq ?_)
  rw [hn]

private theorem FC_cs2 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt a * Real.sqrt c + Real.sqrt b * Real.sqrt d ≤
      Real.sqrt (a + b) * Real.sqrt (c + d) := by
  set x := Real.sqrt a; set y := Real.sqrt b; set u := Real.sqrt c; set v := Real.sqrt d
  have hx : x ^ 2 = a := Real.sq_sqrt ha
  have hy : y ^ 2 = b := Real.sq_sqrt hb
  have hu : u ^ 2 = c := Real.sq_sqrt hc
  have hv : v ^ 2 = d := Real.sq_sqrt hd
  have hx0 : 0 ≤ x := Real.sqrt_nonneg a
  have hy0 : 0 ≤ y := Real.sqrt_nonneg b
  have hu0 : 0 ≤ u := Real.sqrt_nonneg c
  have hv0 : 0 ≤ v := Real.sqrt_nonneg d
  rw [← Real.sqrt_mul (show (0 : ℝ) ≤ a + b by linarith) (c + d)]
  apply Real.le_sqrt_of_sq_le
  rw [← hx, ← hy, ← hu, ← hv]
  nlinarith [sq_nonneg (x * v - y * u)]

private def FC_nI (ord : ι → ℕ) (u : ι → ℂ) (lo hi : ℕ) : ℝ :=
  ∑ x, if lo ≤ ord x ∧ ord x < hi then ‖u x‖ ^ 2 else 0

private theorem FC_nI_nonneg (ord : ι → ℕ) (u : ι → ℂ) (lo hi : ℕ) : 0 ≤ FC_nI ord u lo hi :=
  Finset.sum_nonneg fun x _ => by split_ifs <;> positivity

private theorem FC_nI_split (ord : ι → ℕ) (u : ι → ℂ) (lo mid hi : ℕ) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    FC_nI ord u lo hi = FC_nI ord u lo mid + FC_nI ord u mid hi := by
  unfold FC_nI
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases ha : ord x < mid
  · by_cases hb : lo ≤ ord x
    · simp [hb, ha, show ord x < hi by omega, show ¬ mid ≤ ord x by omega]
    · simp [hb, show ¬ mid ≤ ord x by omega]
  · by_cases hb : ord x < hi
    · simp [ha, hb, show lo ≤ ord x by omega, show mid ≤ ord x by omega]
    · simp [ha, hb]

private theorem FC_bil_restr (T : Matrix ι ι ℂ) (ord : ι → ℕ) (u v : ι → ℂ) (lo₁ hi₁ lo₂ hi₂ : ℕ) :
    ‖∑ a, ∑ b, (if (lo₁ ≤ ord a ∧ ord a < hi₁) ∧ (lo₂ ≤ ord b ∧ ord b < hi₂) then
      u a * T a b * v b else 0)‖ ≤
      opNorm T * Real.sqrt (FC_nI ord u lo₁ hi₁) * Real.sqrt (FC_nI ord v lo₂ hi₂) := by
  set x : ι → ℂ := fun a => if lo₁ ≤ ord a ∧ ord a < hi₁ then u a else 0
  set y : ι → ℂ := fun b => if lo₂ ≤ ord b ∧ ord b < hi₂ then v b else 0
  have e : ∑ a, ∑ b, (if (lo₁ ≤ ord a ∧ ord a < hi₁) ∧ (lo₂ ≤ ord b ∧ ord b < hi₂) then
      u a * T a b * v b else 0) = ∑ a, ∑ b, x a * T a b * y b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [x, y]
    split_ifs <;> simp_all
  have hx : ∑ k, ‖x k‖ ^ 2 = FC_nI ord u lo₁ hi₁ := by
    unfold FC_nI; refine Finset.sum_congr rfl fun k _ => ?_; simp only [x]; split_ifs <;> simp
  have hy : ∑ k, ‖y k‖ ^ 2 = FC_nI ord v lo₂ hi₂ := by
    unfold FC_nI; refine Finset.sum_congr rfl fun k _ => ?_; simp only [y]; split_ifs <;> simp
  rw [e, ← hx, ← hy]
  exact FC_bil_le T x y

private theorem FC_tri (T : Matrix ι ι ℂ) (ord : ι → ℕ) (hord : Function.Injective ord) (u v : ι → ℂ) :
    ∀ k lo : ℕ, ‖∑ a, ∑ b, (if ord a < ord b ∧ lo ≤ ord a ∧ ord b < lo + 2 ^ k then
      u a * T a b * v b else 0)‖ ≤
      k * opNorm T * Real.sqrt (FC_nI ord u lo (lo + 2 ^ k)) *
        Real.sqrt (FC_nI ord v lo (lo + 2 ^ k)) := by
  have hT0 : 0 ≤ opNorm T := by unfold opNorm; exact norm_nonneg _
  intro k
  induction k with
  | zero =>
    intro lo
    have e : ∀ a b, ¬ (ord a < ord b ∧ lo ≤ ord a ∧ ord b < lo + 2 ^ 0) := by
      intro a b ⟨h1, h2, h3⟩; simp at h3; omega
    have : (∑ a, ∑ b, (if ord a < ord b ∧ lo ≤ ord a ∧ ord b < lo + 2 ^ 0 then
        u a * T a b * v b else 0)) = 0 :=
      Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => if_neg (e a b)
    rw [this]
    simp
  | succ k ih =>
    intro lo
    have hhi : lo + 2 ^ (k + 1) = lo + 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    have e : ∀ a b, (if ord a < ord b ∧ lo ≤ ord a ∧ ord b < lo + 2 ^ (k + 1) then
        u a * T a b * v b else 0) =
        (if ord a < ord b ∧ lo ≤ ord a ∧ ord b < lo + 2 ^ k then u a * T a b * v b else 0) +
        (if ord a < ord b ∧ lo + 2 ^ k ≤ ord a ∧ ord b < lo + 2 ^ k + 2 ^ k then
          u a * T a b * v b else 0) +
        (if (lo ≤ ord a ∧ ord a < lo + 2 ^ k) ∧ (lo + 2 ^ k ≤ ord b ∧ ord b < lo + 2 ^ k + 2 ^ k)
          then u a * T a b * v b else 0) := by
      intro a b
      rw [hhi]
      by_cases h1 : ord a < ord b
      · by_cases h2 : ord b < lo + 2 ^ k
        · by_cases h3 : lo ≤ ord a
          · rw [if_pos ⟨h1, h3, by omega⟩, if_pos ⟨h1, h3, h2⟩, if_neg (by omega),
              if_neg (by omega)]
            ring
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            ring
        · by_cases h3 : lo + 2 ^ k ≤ ord a
          · by_cases h4 : ord b < lo + 2 ^ k + 2 ^ k
            · rw [if_pos ⟨h1, by omega, h4⟩, if_neg (by omega), if_pos ⟨h1, h3, h4⟩,
                if_neg (by omega)]
              ring
            · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
              ring
          · by_cases h4 : lo ≤ ord a ∧ ord b < lo + 2 ^ k + 2 ^ k
            · rw [if_pos ⟨h1, h4.1, h4.2⟩, if_neg (by omega), if_neg (by omega),
                if_pos ⟨⟨h4.1, by omega⟩, ⟨by omega, h4.2⟩⟩]
              ring
            · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
              ring
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        ring
    simp only [e, Finset.sum_add_distrib]
    have i1 := ih lo
    have i2 := ih (lo + 2 ^ k)
    have i3 := FC_bil_restr T ord u v lo (lo + 2 ^ k) (lo + 2 ^ k) (lo + 2 ^ k + 2 ^ k)
    have su := FC_nI_split ord u lo (lo + 2 ^ k) (lo + 2 ^ k + 2 ^ k) (Nat.le_add_right _ _)
      (Nat.le_add_right _ _)
    have sv := FC_nI_split ord v lo (lo + 2 ^ k) (lo + 2 ^ k + 2 ^ k) (Nat.le_add_right _ _)
      (Nat.le_add_right _ _)
    rw [hhi, su, sv]
    have ha1 := FC_nI_nonneg ord u lo (lo + 2 ^ k)
    have ha2 := FC_nI_nonneg ord u (lo + 2 ^ k) (lo + 2 ^ k + 2 ^ k)
    have hb1 := FC_nI_nonneg ord v lo (lo + 2 ^ k)
    have hb2 := FC_nI_nonneg ord v (lo + 2 ^ k) (lo + 2 ^ k + 2 ^ k)
    set a1 := FC_nI ord u lo (lo + 2 ^ k)
    set a2 := FC_nI ord u (lo + 2 ^ k) (lo + 2 ^ k + 2 ^ k)
    set b1 := FC_nI ord v lo (lo + 2 ^ k)
    set b2 := FC_nI ord v (lo + 2 ^ k) (lo + 2 ^ k + 2 ^ k)
    have cs := FC_cs2 a1 a2 b1 b2 ha1 ha2 hb1 hb2
    have c1 : Real.sqrt a1 ≤ Real.sqrt (a1 + a2) := Real.sqrt_le_sqrt (by linarith)
    have c2 : Real.sqrt b2 ≤ Real.sqrt (b1 + b2) := Real.sqrt_le_sqrt (by linarith)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have p2 := Real.sqrt_nonneg b2
    have m2 : Real.sqrt a1 * Real.sqrt b2 ≤ Real.sqrt (a1 + a2) * Real.sqrt (b1 + b2) :=
      mul_le_mul c1 c2 p2 (Real.sqrt_nonneg _)
    have m3 : k * opNorm T * (Real.sqrt a1 * Real.sqrt b1 + Real.sqrt a2 * Real.sqrt b2) ≤
        k * opNorm T * (Real.sqrt (a1 + a2) * Real.sqrt (b1 + b2)) :=
      mul_le_mul_of_nonneg_left cs (mul_nonneg hk hT0)
    have m4 := mul_le_mul_of_nonneg_left m2 hT0
    refine (norm_add₃_le).trans ?_
    push_cast
    nlinarith [i1, i2, i3]

end FC_bil

private def FC_ord {D N : ℕ} (i : Idx D N) : ℕ := (finProdFinEquiv i : ℕ)

private theorem FC_ord_inj (D N : ℕ) : Function.Injective (FC_ord (D := D) (N := N)) := fun a b h =>
  finProdFinEquiv.injective (Fin.ext h)

private theorem FC_ord_lt {D N : ℕ} (i : Idx D N) : FC_ord i < D * N := (finProdFinEquiv i).2

private theorem FC_ccum_orient (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (p q : ℕ)
    (hpq : 1 ≤ p + q) : ∀ i j : Idx D N, i.1 = j.1 → i ≠ j →
      ccum ((ouMatLaw D N L t).map fun h => h i j) p q =
        if FC_ord i < FC_ord j then
          ((Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ (p + q) *
            ccum (L.νo : Measure ℂ) p q + ((FClB D N t : ℝ) : ℂ) ^ (p + q) *
              ccum (cGauss : Measure ℂ) p q
        else starRingEnd ℂ (((Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ (p + q) *
            ccum (L.νo : Measure ℂ) p q + ((FClB D N t : ℝ) : ℂ) ^ (p + q) *
              ccum (cGauss : Measure ℂ) p q) := by
  intro i j hb hij
  have hA : ∀ x y : Idx D N, x.1 = y.1 →
      FClA D N t x y = Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := fun x y h => by
    simp [FClA, h]
  have hne : FC_ord i ≠ FC_ord j := fun e => hij (FC_ord_inj D N e)
  by_cases hlt : FC_ord i < FC_ord j
  · rw [if_pos hlt, FCl_ccum_upper D N L t i j hlt p q hpq, hA i j hb]
  · have hgt : finProdFinEquiv j < finProdFinEquiv i := by
      have : FC_ord j < FC_ord i := by omega
      exact this
    rw [if_neg hlt, FCl_entry_lower D N L t i j hgt, FCl_ccum_map_conj,
      FCl_ccum_upper D N L t j i hgt p q hpq, hA j i hb.symm]

private def FC_blk {D N : ℕ} (a : Idx D N → ℂ) (c : Fin D) : Idx D N → ℂ :=
  fun i => if i.1 = c then a i else 0

private theorem FC_blk_norm {D N : ℕ} (a : Idx D N → ℂ) :
    ∑ c, ∑ i, ‖FC_blk a c i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i.1]
  · simp [FC_blk]
  · intro c _ hc; simp [FC_blk, Ne.symm hc]
  · simp

private theorem FC_blk_cs {D N : ℕ} (a b : Idx D N → ℂ) :
    ∑ c, Real.sqrt (∑ i, ‖FC_blk a c i‖ ^ 2) * Real.sqrt (∑ i, ‖FC_blk b c i‖ ^ 2) ≤
      Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans (le_of_eq ?_)
  simp only [Real.sq_sqrt (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
    sq_nonneg ‖FC_blk a _ i‖), Real.sq_sqrt (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
    sq_nonneg ‖FC_blk b _ i‖), FC_blk_norm]

private theorem FC_bil_block {D N : ℕ} (T : Matrix (Idx D N) (Idx D N) ℂ) (a b : Idx D N → ℂ) :
    ‖∑ i, ∑ j, (if i.1 = j.1 then a i * T i j * b j else 0)‖ ≤
      opNorm T * Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  have e : ∑ i, ∑ j, (if i.1 = j.1 then a i * T i j * b j else 0) =
      ∑ c, ∑ i, ∑ j, FC_blk a c i * T i j * FC_blk b c j := by
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single i.1]
    · by_cases h : i.1 = j.1
      · simp [FC_blk, h]
      · simp [FC_blk, h, Ne.symm h]
    · intro c _ hc; simp [FC_blk, Ne.symm hc]
    · simp
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  have hT0 : 0 ≤ opNorm T := by unfold opNorm; exact norm_nonneg _
  calc ∑ c, ‖∑ i, ∑ j, FC_blk a c i * T i j * FC_blk b c j‖
      ≤ ∑ c, opNorm T * Real.sqrt (∑ i, ‖FC_blk a c i‖ ^ 2) *
          Real.sqrt (∑ i, ‖FC_blk b c i‖ ^ 2) :=
        Finset.sum_le_sum fun c _ => FC_bil_le T _ _
    _ = opNorm T * ∑ c, Real.sqrt (∑ i, ‖FC_blk a c i‖ ^ 2) *
          Real.sqrt (∑ i, ‖FC_blk b c i‖ ^ 2) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    _ ≤ opNorm T * (Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (FC_blk_cs a b) hT0
    _ = _ := by ring

private theorem FC_tri_block {D N : ℕ} (T : Matrix (Idx D N) (Idx D N) ℂ) (a b : Idx D N → ℂ) (k : ℕ)
    (hk : D * N ≤ 2 ^ k) :
    ‖∑ i, ∑ j, (if i.1 = j.1 ∧ FC_ord i < FC_ord j then a i * T i j * b j else 0)‖ ≤
      k * opNorm T * Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  have hord : ∀ i : Idx D N, 0 ≤ FC_ord i ∧ FC_ord i < 0 + 2 ^ k := fun i =>
    ⟨Nat.zero_le _, by have := FC_ord_lt i; omega⟩
  have e : ∑ i, ∑ j, (if i.1 = j.1 ∧ FC_ord i < FC_ord j then a i * T i j * b j else 0) =
      ∑ c, ∑ i, ∑ j, (if FC_ord i < FC_ord j ∧ 0 ≤ FC_ord i ∧ FC_ord j < 0 + 2 ^ k then
        FC_blk a c i * T i j * FC_blk b c j else 0) := by
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single i.1]
    · by_cases h : i.1 = j.1
      · by_cases h2 : FC_ord i < FC_ord j
        · have h3 : FC_ord j < 2 ^ k := by have := (hord j).2; omega
          simp [FC_blk, h, h2, h3]
        · simp [h2]
      · by_cases h2 : FC_ord i < FC_ord j
        · simp [FC_blk, h, Ne.symm h, h2]
        · simp [h2]
    · intro c _ hc; simp [FC_blk, Ne.symm hc]
    · simp
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  have hT0 : 0 ≤ opNorm T := by unfold opNorm; exact norm_nonneg _
  have hnI : ∀ (u : Idx D N → ℂ), FC_nI FC_ord u 0 (0 + 2 ^ k) = ∑ i, ‖u i‖ ^ 2 := by
    intro u
    unfold FC_nI
    exact Finset.sum_congr rfl fun i _ => by rw [ite_eq_left_iff.2 fun h => absurd (hord i) h]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc ∑ c, ‖∑ i, ∑ j, (if FC_ord i < FC_ord j ∧ 0 ≤ FC_ord i ∧ FC_ord j < 0 + 2 ^ k then
        FC_blk a c i * T i j * FC_blk b c j else 0)‖
      ≤ ∑ c, k * opNorm T * Real.sqrt (∑ i, ‖FC_blk a c i‖ ^ 2) *
          Real.sqrt (∑ i, ‖FC_blk b c i‖ ^ 2) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have := FC_tri T FC_ord (FC_ord_inj D N) (FC_blk a c) (FC_blk b c) k 0
        rw [hnI, hnI] at this
        exact this
    _ = k * opNorm T * ∑ c, Real.sqrt (∑ i, ‖FC_blk a c i‖ ^ 2) *
          Real.sqrt (∑ i, ‖FC_blk b c i‖ ^ 2) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    _ ≤ k * opNorm T * (Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (FC_blk_cs a b) (mul_nonneg hk0 hT0)
    _ = _ := by ring

end

section

private def FC_off (f : FC_Fac) : Bool := f.2.1 != f.2.2

private def FC_offc (m : FC_Mono) : ℕ := (m.filter FC_off).length

private theorem FC_tri_block_low {D N : ℕ} (T : Matrix (Idx D N) (Idx D N) ℂ) (a b : Idx D N → ℂ) (k : ℕ)
    (hk : D * N ≤ 2 ^ k) :
    ‖∑ i, ∑ j, (if i.1 = j.1 ∧ FC_ord j < FC_ord i then a i * T i j * b j else 0)‖ ≤
      (k + 2) * opNorm T * Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  have e : ∑ i, ∑ j, (if i.1 = j.1 ∧ FC_ord j < FC_ord i then a i * T i j * b j else 0) =
      (∑ i, (∑ j, (if i.1 = j.1 then a i * T i j * b j else 0))) -
        (∑ i, (∑ j, (if i.1 = j.1 ∧ FC_ord i < FC_ord j then a i * T i j * b j else 0))) -
        ∑ i, a i * T i i * b i := by
    have e2 : ∑ i, a i * T i i * b i = ∑ i, ∑ j, (if i = j then a i * T i j * b j else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_ite_eq]; simp
    rw [e2, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · have hne : FC_ord i ≠ FC_ord j := fun e => hij (FC_ord_inj D N e)
      by_cases hb : i.1 = j.1
      · by_cases hlt : FC_ord i < FC_ord j
        · simp [hb, hlt, hij, show ¬ FC_ord j < FC_ord i by omega]
        · simp [hb, hlt, hij, show FC_ord j < FC_ord i by omega]
      · simp [hb, hij]
  rw [e]
  have hT0 : 0 ≤ opNorm T := by unfold opNorm; exact norm_nonneg _
  have h1 := FC_bil_block T a b
  have h2 := FC_tri_block T a b k hk
  have h3 : ‖∑ i, a i * T i i * b i‖ ≤
      opNorm T * Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖a i * T i i * b i‖ ≤ ∑ i, opNorm T * (‖a i‖ * ‖b i‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, norm_mul]
          have := norm_apply_le_opNorm T i i
          nlinarith [norm_nonneg (a i), norm_nonneg (b i), mul_nonneg (norm_nonneg (a i))
            (norm_nonneg (b i))]
      _ = opNorm T * ∑ i, ‖a i‖ * ‖b i‖ := by rw [Finset.mul_sum]
      _ ≤ opNorm T * (Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hT0
      _ = _ := by ring
  have hs := mul_nonneg (Real.sqrt_nonneg (∑ i, ‖a i‖ ^ 2)) (Real.sqrt_nonneg (∑ i, ‖b i‖ ^ 2))
  calc _ ≤ ‖∑ i, ∑ j, (if i.1 = j.1 then a i * T i j * b j else 0)‖ +
        ‖∑ i, ∑ j, (if i.1 = j.1 ∧ FC_ord i < FC_ord j then a i * T i j * b j else 0)‖ +
        ‖∑ i, a i * T i i * b i‖ := by
        refine (norm_sub_le _ _).trans ?_
        exact add_le_add_left (norm_sub_le _ _) _ |>.trans (by linarith)
    _ ≤ _ := by nlinarith

private def FC_cw {D N : ℕ} (κ κ' : ℂ) (i j : Idx D N) : ℂ :=
  if i.1 = j.1 ∧ i ≠ j then (if FC_ord i < FC_ord j then κ else κ') else 0

private theorem FC_cw_sum {D N : ℕ} (T : Matrix (Idx D N) (Idx D N) ℂ) (a b : Idx D N → ℂ) (k : ℕ)
    (hk : D * N ≤ 2 ^ k) (κ κ' : ℂ) :
    ‖∑ i, ∑ j, FC_cw κ κ' i j * (a i * T i j * b j)‖ ≤
      (‖κ‖ + ‖κ'‖) * (k + 2) * opNorm T * Real.sqrt (∑ i, ‖a i‖ ^ 2) *
        Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  have e : ∑ i, ∑ j, FC_cw κ κ' i j * (a i * T i j * b j) =
      κ * (∑ i, (∑ j, (if i.1 = j.1 ∧ FC_ord i < FC_ord j then a i * T i j * b j else 0))) +
        κ' * ∑ i, ∑ j, (if i.1 = j.1 ∧ FC_ord j < FC_ord i then a i * T i j * b j else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    unfold FC_cw
    by_cases hij : i = j
    · subst hij; simp
    · have hne : FC_ord i ≠ FC_ord j := fun e => hij (FC_ord_inj D N e)
      by_cases hb : i.1 = j.1
      · by_cases hlt : FC_ord i < FC_ord j
        · simp [hb, hlt, hij, show ¬ FC_ord j < FC_ord i by omega]
        · simp [hb, hlt, hij, show FC_ord j < FC_ord i by omega]
      · simp [hb]
  rw [e]
  have hT0 : 0 ≤ opNorm T := by unfold opNorm; exact norm_nonneg _
  have h2 := FC_tri_block T a b k hk
  have h3 := FC_tri_block_low T a b k hk
  have hs := mul_nonneg (Real.sqrt_nonneg (∑ i, ‖a i‖ ^ 2)) (Real.sqrt_nonneg (∑ i, ‖b i‖ ^ 2))
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have c1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg κ)
  have c2 := mul_le_mul_of_nonneg_left h3 (norm_nonneg κ')
  have c3 : ‖κ‖ * (k * opNorm T * Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) ≤
      ‖κ‖ * ((k + 2) * opNorm T * Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg κ)
    have : k * opNorm T * Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) =
        k * (opNorm T * (Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2))) := by ring
    have h' : (k + 2) * opNorm T * Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) =
        (k + 2) * (opNorm T * (Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2))) := by
      ring
    rw [this, h']
    exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hT0 hs)
  nlinarith

section FC_mono_bounds
variable {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (ch : FC_Ch D N) (X : Matrix (Idx D N) (Idx D N) ℂ)
  (SL : FC_Seg → Prop) (Wt : FC_Seg → ℝ) (K Kh Ko : ℝ)

private def FC_wprod (Wt : FC_Seg → ℝ) (m : FC_Mono) : ℝ := (m.map fun f => Wt f.1).prod

private theorem FC_wprod_perm (Wt : FC_Seg → ℝ) {m m' : FC_Mono} (hp : m.Perm m') :
    FC_wprod Wt m = FC_wprod Wt m' := (hp.map _).prod_eq

private theorem FC_evalMono_perm (i j : Idx D N) {m m' : FC_Mono} (hp : m.Perm m') :
    FC_evalMono h ch X i j m = FC_evalMono h ch X i j m' := (hp.map _).prod_eq

private theorem FC_wprod_nonneg (hW : ∀ s, 0 ≤ Wt s) (m : FC_Mono) : 0 ≤ FC_wprod Wt m := by
  unfold FC_wprod
  induction m with
  | nil => simp
  | cons f m ih => simp only [List.map_cons, List.prod_cons]; exact mul_nonneg (hW _) ih

private theorem FC_wprod_cons (f : FC_Fac) (m : FC_Mono) :
    FC_wprod Wt (f :: m) = Wt f.1 * FC_wprod Wt m := by simp [FC_wprod]

private theorem FC_mono_sup (hK : 0 ≤ K) (hW : ∀ s, 0 ≤ Wt s)
    (hsup : ∀ s, SL s → ∀ x y, ‖FC_evalSeg h ch X s x y‖ ≤ K * Wt s) (i j : Idx D N) :
    ∀ m : FC_Mono, (∀ f ∈ m, SL f.1) →
      ‖FC_evalMono h ch X i j m‖ ≤ K ^ m.length * FC_wprod Wt m := by
  intro m
  induction m with
  | nil => intro _; simp [FC_evalMono, FC_wprod]
  | cons f m ih =>
    intro hm
    rw [FC_evalMono_cons, norm_mul, FC_wprod_cons, List.length_cons, pow_succ]
    have h1 : ‖FC_evalFac h ch X i j f‖ ≤ K * Wt f.1 := hsup f.1 (hm f (by simp)) _ _
    have h2 := ih fun f' hf' => hm f' (by simp [hf'])
    have := FC_wprod_nonneg Wt hW m
    calc ‖FC_evalFac h ch X i j f‖ * ‖FC_evalMono h ch X i j m‖
        ≤ (K * Wt f.1) * (K ^ m.length * FC_wprod Wt m) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hK (hW _))
      _ = _ := by ring

private theorem FC_off_sq (f : FC_Fac) (hf : FC_off f = true) :
    ∑ i, ∑ j, ‖FC_evalFac h ch X i j f‖ ^ 2 =
      ∑ x, ∑ y, ‖FC_evalSeg h ch X f.1 x y‖ ^ 2 := by
  obtain ⟨s, u, v⟩ := f
  simp only [FC_off, bne_iff_ne, ne_eq] at hf
  cases u <;> cases v
  · simp at hf
  · simp [FC_evalFac, FC_idx]
  · simp only [FC_evalFac, FC_idx, ↓reduceIte, Bool.false_eq_true]
    exact Finset.sum_comm
  · simp at hf

private theorem FC_sum_mul_le (A B : Idx D N → Idx D N → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hB : ∀ i j, 0 ≤ B i j) :
    ∑ i, ∑ j, A i j * B i j ≤
      Real.sqrt (∑ i, ∑ j, A i j ^ 2) * Real.sqrt (∑ i, ∑ j, B i j ^ 2) := by
  have e1 : ∀ F : Idx D N → Idx D N → ℝ, ∑ i, ∑ j, F i j = ∑ p : Idx D N × Idx D N, F p.1 p.2 :=
    fun F => (Fintype.sum_prod_type' F).symm
  rw [e1, e1, e1]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

private theorem FC_mono_two (hK : 0 ≤ K) (hKh : 0 ≤ Kh) (hW : ∀ s, 0 ≤ Wt s)
    (hsup : ∀ s, SL s → ∀ x y, ‖FC_evalSeg h ch X s x y‖ ≤ K * Wt s)
    (hHS : ∀ s, SL s → ∑ x, ∑ y, ‖FC_evalSeg h ch X s x y‖ ^ 2 ≤ (Kh * Wt s) ^ 2)
    (m : FC_Mono) (hm : ∀ f ∈ m, SL f.1) (h2 : 2 ≤ FC_offc m) :
    ∑ i, ∑ j, ‖FC_evalMono h ch X i j m‖ ≤ K ^ (m.length - 2) * Kh ^ 2 * FC_wprod Wt m := by
  obtain ⟨f1, f2, t, ht⟩ : ∃ f1 f2 t, m.filter FC_off = f1 :: f2 :: t := by
    unfold FC_offc at h2
    match hq : m.filter FC_off with
    | [] => rw [hq] at h2; simp at h2
    | [_] => rw [hq] at h2; simp at h2
    | f1 :: f2 :: t => exact ⟨f1, f2, t, rfl⟩
  have hp : (f1 :: f2 :: (t ++ m.filter fun x => !FC_off x)).Perm m := by
    have := List.filter_append_perm FC_off m
    rw [ht] at this
    simpa using this
  have hf1 : f1 ∈ m.filter FC_off := by rw [ht]; simp
  have hf2 : f2 ∈ m.filter FC_off := by rw [ht]; simp
  have ho1 : FC_off f1 = true := (List.mem_filter.1 hf1).2
  have ho2 : FC_off f2 = true := (List.mem_filter.1 hf2).2
  set r := t ++ m.filter fun x => !FC_off x with hr
  have hmr : ∀ f ∈ r, SL f.1 := fun f hf => hm f (hp.subset (by simp [hf]))
  have hs1 : SL f1.1 := hm f1 (hp.subset (by simp))
  have hs2 : SL f2.1 := hm f2 (hp.subset (by simp))
  have hlen : m.length = r.length + 2 := by rw [← hp.length_eq]; simp
  have hwp : FC_wprod Wt m = Wt f1.1 * Wt f2.1 * FC_wprod Wt r := by
    rw [← FC_wprod_perm Wt hp, FC_wprod_cons, FC_wprod_cons]; ring
  have hev : ∀ i j, FC_evalMono h ch X i j m = FC_evalFac h ch X i j f1 *
      FC_evalFac h ch X i j f2 * FC_evalMono h ch X i j r := by
    intro i j
    rw [← FC_evalMono_perm h ch X i j hp, FC_evalMono_cons, FC_evalMono_cons]; ring
  have hR : ∀ i j, ‖FC_evalMono h ch X i j r‖ ≤ K ^ r.length * FC_wprod Wt r :=
    fun i j => FC_mono_sup h ch X SL Wt K hK hW hsup i j r hmr
  have hRn : 0 ≤ K ^ r.length * FC_wprod Wt r := mul_nonneg (pow_nonneg hK _)
    (FC_wprod_nonneg Wt hW r)
  have hcs := FC_sum_mul_le (fun i j => ‖FC_evalFac h ch X i j f1‖)
    (fun i j => ‖FC_evalFac h ch X i j f2‖) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
  rw [FC_off_sq h ch X f1 ho1, FC_off_sq h ch X f2 ho2] at hcs
  have hq1 := Real.sqrt_le_sqrt (hHS f1.1 hs1)
  have hq2 := Real.sqrt_le_sqrt (hHS f2.1 hs2)
  rw [Real.sqrt_sq (mul_nonneg hKh (hW _))] at hq1 hq2
  calc ∑ i, ∑ j, ‖FC_evalMono h ch X i j m‖
      ≤ ∑ i, ∑ j, ‖FC_evalFac h ch X i j f1‖ * ‖FC_evalFac h ch X i j f2‖ *
          (K ^ r.length * FC_wprod Wt r) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [hev, norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (hR i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ i, ∑ j, ‖FC_evalFac h ch X i j f1‖ * ‖FC_evalFac h ch X i j f2‖) *
          (K ^ r.length * FC_wprod Wt r) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    _ ≤ (Kh * Wt f1.1) * (Kh * Wt f2.1) * (K ^ r.length * FC_wprod Wt r) := by
        refine mul_le_mul_of_nonneg_right (hcs.trans ?_) hRn
        exact mul_le_mul hq1 hq2 (Real.sqrt_nonneg _) (mul_nonneg hKh (hW _))
    _ = _ := by rw [hlen, hwp, Nat.add_sub_cancel]; ring

private theorem FC_cw_swap (κ κ' : ℂ) (i j : Idx D N) : FC_cw κ κ' i j = FC_cw κ' κ j i := by
  unfold FC_cw
  by_cases hij : i = j
  · subst hij; simp
  · have hne : FC_ord i ≠ FC_ord j := fun e => hij (FC_ord_inj D N e)
    by_cases hb : i.1 = j.1
    · by_cases hlt : FC_ord i < FC_ord j
      · simp [hb, hlt, hij, Ne.symm hij, show ¬ FC_ord j < FC_ord i by omega]
      · simp [hb, hlt, hij, Ne.symm hij, show FC_ord j < FC_ord i by omega]
    · simp [hb, Ne.symm hb]

private def FC_dprod (b : Bool) (m : FC_Mono) (x : Idx D N) : ℂ :=
  (m.map fun f => if f.2.1 = b then FC_evalSeg h ch X f.1 x x else 1).prod

private theorem FC_dprod_le (hK : 0 ≤ K) (hW : ∀ s, 0 ≤ Wt s)
    (hsup : ∀ s, SL s → ∀ x y, ‖FC_evalSeg h ch X s x y‖ ≤ K * Wt s) (b : Bool) (x : Idx D N) :
    ∀ m : FC_Mono, (∀ f ∈ m, SL f.1) →
      ‖FC_dprod h ch X b m x‖ ≤ (m.map fun f => if f.2.1 = b then K * Wt f.1 else 1).prod := by
  intro m
  induction m with
  | nil => intro _; simp [FC_dprod]
  | cons f m ih =>
    intro hm
    simp only [FC_dprod, List.map_cons, List.prod_cons] at ih ⊢
    rw [norm_mul]
    have h2 := ih fun f' hf' => hm f' (by simp [hf'])
    have hpos : 0 ≤ (m.map fun f => if f.2.1 = b then K * Wt f.1 else 1).prod := by
      clear ih h2 hm
      induction m with
      | nil => simp
      | cons g m ih' =>
        simp only [List.map_cons, List.prod_cons]
        refine mul_nonneg ?_ ih'
        split_ifs
        · exact mul_nonneg hK (hW _)
        · exact zero_le_one
    refine mul_le_mul ?_ h2 (norm_nonneg _) (by split_ifs <;> [exact mul_nonneg hK (hW _); norm_num])
    split_ifs
    · exact hsup f.1 (hm f (by simp)) x x
    · simp

private theorem FC_dprod_prod (hK : 0 ≤ K) (m : FC_Mono) :
    (m.map fun f => if f.2.1 = false then K * Wt f.1 else 1).prod *
      (m.map fun f => if f.2.1 = true then K * Wt f.1 else 1).prod =
        K ^ m.length * FC_wprod Wt m := by
  induction m with
  | nil => simp [FC_wprod]
  | cons f m ih =>
    obtain ⟨s', u, v⟩ := f
    simp only [List.map_cons, List.prod_cons, FC_wprod_cons, List.length_cons, pow_succ]
    cases u
    · simp only [↓reduceIte, Bool.false_eq_true]
      linear_combination (K * Wt s') * ih
    · simp only [↓reduceIte, Bool.true_eq_false]
      linear_combination (K * Wt s') * ih

private theorem FC_diag_eval (i j : Idx D N) (m : FC_Mono) (hm : ∀ f ∈ m, FC_off f = false) :
    FC_evalMono h ch X i j m = FC_dprod h ch X false m i * FC_dprod h ch X true m j := by
  induction m with
  | nil => simp [FC_evalMono, FC_dprod]
  | cons f m ih =>
    have hf := hm f (by simp)
    have ih' := ih fun f' hf' => hm f' (by simp [hf'])
    rw [FC_evalMono_cons, ih']
    simp only [FC_dprod, List.map_cons, List.prod_cons]
    obtain ⟨s, u, v⟩ := f
    simp only [FC_off, bne_eq_false_iff_eq] at hf
    subst hf
    cases u <;> simp [FC_evalFac, FC_idx] <;> ring

private theorem FC_mono_one (hK : 0 ≤ K) (hW : ∀ s, 0 ≤ Wt s)
    (hsup : ∀ s, SL s → ∀ x y, ‖FC_evalSeg h ch X s x y‖ ≤ K * Wt s)
    (hop : ∀ s, SL s → opNorm (FC_evalSeg h ch X s) ≤ Ko * Wt s)
    (k : ℕ) (hk : D * N ≤ 2 ^ k) (κ κ' : ℂ)
    (m : FC_Mono) (hm : ∀ f ∈ m, SL f.1) (h1 : FC_offc m = 1) :
    ‖∑ i, ∑ j, FC_cw κ κ' i j * FC_evalMono h ch X i j m‖ ≤
      (‖κ‖ + ‖κ'‖) * (k + 2) * Ko * K ^ (m.length - 1) * (D * N) * FC_wprod Wt m := by
  obtain ⟨f0, ht⟩ : ∃ f0, m.filter FC_off = [f0] := by
    unfold FC_offc at h1
    match hq : m.filter FC_off with
    | [] => rw [hq] at h1; simp at h1
    | [f0] => exact ⟨f0, rfl⟩
    | _ :: _ :: _ => rw [hq] at h1; simp at h1
  set r := m.filter fun x => !FC_off x with hr
  have hp : (f0 :: r).Perm m := by
    have := List.filter_append_perm FC_off m
    rw [ht] at this
    simpa using this
  have hf0 : FC_off f0 = true := (List.mem_filter.1 (by rw [ht]; simp : f0 ∈ m.filter FC_off)).2
  have hrd : ∀ f ∈ r, FC_off f = false := fun f hf => by
    have := (List.mem_filter.1 hf).2; simpa using this
  have hmr : ∀ f ∈ r, SL f.1 := fun f hf => hm f (hp.subset (by simp [hf]))
  have hs0 : SL f0.1 := hm f0 (hp.subset (by simp))
  have hlen : m.length = r.length + 1 := by rw [← hp.length_eq]; simp
  have hwp : FC_wprod Wt m = Wt f0.1 * FC_wprod Wt r := by
    rw [← FC_wprod_perm Wt hp, FC_wprod_cons]
  set a := FC_dprod h ch X false r with ha
  set b := FC_dprod h ch X true r with hb
  set S0 := FC_evalSeg h ch X f0.1 with hS0
  have hev : ∀ i j, FC_evalMono h ch X i j m = FC_evalFac h ch X i j f0 * (a i * b j) := by
    intro i j
    rw [← FC_evalMono_perm h ch X i j hp, FC_evalMono_cons, FC_diag_eval h ch X i j r hrd]
  set A := (r.map fun f => if f.2.1 = false then K * Wt f.1 else 1).prod
  set B := (r.map fun f => if f.2.1 = true then K * Wt f.1 else 1).prod
  have hA : ∀ x, ‖a x‖ ≤ A := fun x => FC_dprod_le h ch X SL Wt K hK hW hsup false x r hmr
  have hB : ∀ x, ‖b x‖ ≤ B := fun x => FC_dprod_le h ch X SL Wt K hK hW hsup true x r hmr
  have hAB : A * B = K ^ r.length * FC_wprod Wt r := FC_dprod_prod Wt K hK r
  have hpn : ∀ (c : Bool) (l : FC_Mono),
      0 ≤ (l.map fun f => if f.2.1 = c then K * Wt f.1 else 1).prod := by
    intro c l
    induction l with
    | nil => simp
    | cons g l ih' =>
      simp only [List.map_cons, List.prod_cons]
      refine mul_nonneg ?_ ih'
      split_ifs
      · exact mul_nonneg hK (hW _)
      · exact zero_le_one
  have hA0 : 0 ≤ A := hpn false r
  have hB0 : 0 ≤ B := hpn true r
  have hcard : (Fintype.card (Idx D N) : ℝ) = D * N := by simp
  have hna : Real.sqrt (∑ i, ‖a i‖ ^ 2) ≤ Real.sqrt (D * N) * A := by
    rw [← Real.sqrt_sq hA0, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖a i‖ ^ 2 ≤ ∑ _i : Idx D N, A ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hA i) 2
      _ = D * N * A ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hnb : Real.sqrt (∑ i, ‖b i‖ ^ 2) ≤ Real.sqrt (D * N) * B := by
    rw [← Real.sqrt_sq hB0, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖b i‖ ^ 2 ≤ ∑ _i : Idx D N, B ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hB i) 2
      _ = D * N * B ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hsq : Real.sqrt (D * N) * Real.sqrt (D * N) = D * N := Real.mul_self_sqrt (by positivity)
  have hκ0 : 0 ≤ (‖κ‖ + ‖κ'‖) * (k + 2) := by positivity
  have hS0 : 0 ≤ opNorm S0 := by unfold opNorm; exact norm_nonneg _
  have hW0 := hW f0.1
  have hfin : ∀ (a' b' : Idx D N → ℂ) (κ₁ κ₂ : ℂ), ‖κ₁‖ + ‖κ₂‖ = ‖κ‖ + ‖κ'‖ →
      Real.sqrt (∑ i, ‖a' i‖ ^ 2) * Real.sqrt (∑ i, ‖b' i‖ ^ 2) ≤ D * N * (A * B) →
      ‖∑ i, ∑ j, FC_cw κ₁ κ₂ i j * (a' i * S0 i j * b' j)‖ ≤
        (‖κ‖ + ‖κ'‖) * (k + 2) * Ko * K ^ (m.length - 1) * (D * N) * FC_wprod Wt m := by
    intro a' b' κ₁ κ₂ hκ hab
    refine (FC_cw_sum S0 a' b' k hk κ₁ κ₂).trans ?_
    rw [hκ, hlen, Nat.add_sub_cancel, hwp]
    have hop0 := hop f0.1 hs0
    calc (‖κ‖ + ‖κ'‖) * (k + 2) * opNorm S0 * Real.sqrt (∑ i, ‖a' i‖ ^ 2) *
          Real.sqrt (∑ i, ‖b' i‖ ^ 2)
        = ((‖κ‖ + ‖κ'‖) * (k + 2)) * opNorm S0 *
            (Real.sqrt (∑ i, ‖a' i‖ ^ 2) * Real.sqrt (∑ i, ‖b' i‖ ^ 2)) := by ring
      _ ≤ ((‖κ‖ + ‖κ'‖) * (k + 2)) * (Ko * Wt f0.1) * (D * N * (A * B)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hop0 hκ0) hab
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (mul_nonneg hκ0 (hS0.trans hop0))
      _ = _ := by rw [hAB]; ring
  have hab1 : Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) ≤ D * N * (A * B) := by
    calc _ ≤ (Real.sqrt (D * N) * A) * (Real.sqrt (D * N) * B) :=
          mul_le_mul hna hnb (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA0)
      _ = _ := by rw [show (Real.sqrt (D * N) * A) * (Real.sqrt (D * N) * B) =
            (Real.sqrt (D * N) * Real.sqrt (D * N)) * (A * B) by ring, hsq]
  obtain ⟨s0, u0, v0⟩ := f0
  simp only [FC_off, bne_iff_ne, ne_eq] at hf0
  cases u0 <;> cases v0
  · simp at hf0
  · -- `(u, v) = (i, j)`
    have e : ∑ i, ∑ j, FC_cw κ κ' i j * FC_evalMono h ch X i j m =
        ∑ i, ∑ j, FC_cw κ κ' i j * (a i * S0 i j * b j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hev]; simp only [FC_evalFac, FC_idx, Bool.false_eq_true, ↓reduceIte]; ring
    rw [e]
    exact hfin a b κ κ' rfl hab1
  · -- `(u, v) = (j, i)`
    have e : ∑ i, ∑ j, FC_cw κ κ' i j * FC_evalMono h ch X i j m =
        ∑ i, ∑ j, FC_cw κ' κ i j * (b i * S0 i j * a j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hev, FC_cw_swap κ κ' j i]
      simp only [FC_evalFac, FC_idx, Bool.false_eq_true, ↓reduceIte]; ring
    rw [e]
    exact hfin b a κ' κ (add_comm _ _)
      (by rw [mul_comm]; exact hab1)
  · simp at hf0

end FC_mono_bounds

end

section

private theorem FCe_setEntry_self {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) : setEntry h i j (h i j) = h := by
  funext k l
  have h1 : ∀ k l, starRingEnd ℂ (h l k) = h k l := fun k l => by
    simpa [Complex.star_def] using hh.apply k l
  by_cases hd : i = j
  · subst hd
    by_cases hkl : k = i ∧ l = i
    · obtain ⟨hk, hl⟩ := hkl
      rw [hk, hl]
      have hre : (((h i i).re : ℝ) : ℂ) = h i i := Complex.conj_eq_iff_re.mp (h1 i i)
      simp [setEntry, hre]
    · simp [setEntry, hkl]
  · by_cases h1' : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1'
      simp [setEntry, hd]
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp [setEntry, hd, Ne.symm hd, h1 k l]
      · simp [setEntry, hd, h1', h2]

private theorem FCe_jointCum_conj {n : ℕ} (ρ : Measure ℂ) (X : Fin n → ℂ → ℂ) :
    jointCum ρ (fun i z => starRingEnd ℂ (X i z)) = starRingEnd ℂ (jointCum ρ X) := by
  unfold jointCum
  rw [map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hB : ∀ B ∈ π.parts, ∫ z, ∏ i ∈ B, starRingEnd ℂ (X i z) ∂ρ =
      starRingEnd ℂ (∫ z, ∏ i ∈ B, X i z ∂ρ) := by
    intro B _
    rw [← integral_conj]
    simp only [map_prod]
  rw [Finset.prod_congr rfl hB, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast,
    map_prod]

private theorem FCe_jointCum_cast (ρ : Measure ℂ) {n m : ℕ} (h : n = m) (f : ℂ → ℂ) :
    jointCum ρ (fun _ : Fin n => f) = jointCum ρ (fun _ : Fin m => f) := by
  subst h
  rfl

private theorem FCe_ccum_swap (ρ : Measure ℂ) (p : ℕ) :
    ccum ρ p 0 = starRingEnd ℂ (ccum ρ 0 p) := by
  have h1 : ccum ρ p 0 = jointCum ρ (fun (_ : Fin (p + 0)) (z : ℂ) =>
      starRingEnd ℂ (starRingEnd ℂ z)) := by
    unfold ccum
    congr 1
    funext i z
    simp
  have h2 : ccum ρ 0 p = jointCum ρ (fun (_ : Fin (0 + p)) (z : ℂ) => starRingEnd ℂ z) := by
    unfold ccum
    congr 1
  rw [h1, h2, FCe_jointCum_conj ρ (fun (_ : Fin (p + 0)) (z : ℂ) => starRingEnd ℂ z),
    FCe_jointCum_cast ρ (Nat.add_zero p) (starRingEnd ℂ), FCe_jointCum_cast ρ (Nat.zero_add p)
      (starRingEnd ℂ)]

private theorem FCe_ccum01 {D N : ℕ} {C : ℕ → ℝ} {θ : ℝ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμ : LLClass D N C θ μ) (i j : Idx D N) : ccum (μ.map fun h => h i j) 0 1 = 0 := by
  have h1 := (llClass_ccum_low D N C θ μ hμ i j).1
  rw [FCe_ccum_swap] at h1
  simpa using h1

private def FC_P0 (n : ℕ) : FC_Poly := [[((0, n, false, true), false, true)]]

private def FC_Dpq (n p q : ℕ) : FC_Poly := (FC_dPoly false)^[p] ((FC_dPoly true)^[q] (FC_P0 n))

private theorem FC_mod_false {D N : ℕ} (l : FC_Ch D N) : FC_mod false l = l := by
  cases l <;> simp [FC_mod]

private theorem FC_eval_P0 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (ch : FC_Ch D N)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) :
    FC_evalPoly h ch X i j (FC_P0 ch.length) = (chainB h ch * X) i j := by
  simp [FC_evalPoly, FC_P0, FC_evalMono, FC_evalFac, FC_evalSeg, FC_segList, FC_mod_false,
    FC_idx]

private theorem FC_P0_valid (n : ℕ) (hn : 1 ≤ n) : ∀ m ∈ FC_P0 n, ∀ f ∈ m, FC_validF n f := by
  intro m hm f hf
  simp only [FC_P0, List.mem_cons, List.not_mem_nil, or_false] at hm
  subst hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact ⟨by simp; omega, le_rfl⟩

private theorem FC_wirt_point {D N : ℕ} (ch : FC_Ch D N)
    (hch : ∀ f ∈ ch, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (hn : 1 ≤ ch.length)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (p q : ℕ) :
    wirt p q (fun w => (chainB (setEntry h i j w) ch * X) i j) (h i j) =
      (-(if i = j then 1 / 2 else 1)) ^ (p + q) *
        FC_evalPoly h ch X i j (FC_Dpq ch.length p q) := by
  have e : (fun w => (chainB (setEntry h i j w) ch * X) i j) =
      fun w => FC_evalPoly (setEntry h i j w) ch X i j (FC_P0 ch.length) := by
    funext w; rw [FC_eval_P0]
  rw [e, FC_wirt_eq ch hch X h hh i j _ (FC_P0_valid _ hn) p q]
  simp only [FCe_setEntry_self h hh i j]
  rfl

private theorem FC_prod_le_one {α : Type*} (l : List α) (g : α → ℝ) (h0 : ∀ a ∈ l, 0 ≤ g a)
    (h1 : ∀ a ∈ l, g a ≤ 1) : (l.map g).prod ≤ 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha0 := h0 a (by simp)
    have ha1 := h1 a (by simp)
    have ht := ih (fun b hb => h0 b (by simp [hb])) (fun b hb => h1 b (by simp [hb]))
    have ht0 : 0 ≤ (t.map g).prod := List.prod_nonneg fun b hb => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb; exact h0 c (by simp [hc])
    nlinarith

private theorem FC_col_le {D N : ℕ} (X : Matrix (Idx D N) (Idx D N) ℂ) (j : Idx D N) :
    ∑ γ, ‖X γ j‖ ^ 2 ≤ opNorm X ^ 2 := by
  have h := FC_mulVec_sq_le X (Pi.single j 1)
  have e1 : ∀ γ, (X *ᵥ Pi.single j 1) γ = X γ j := fun γ => by simp [Matrix.mulVec_single]
  have e2 : ∑ k, ‖(Pi.single j (1 : ℂ) : Idx D N → ℂ) k‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  simp only [e1, e2, mul_one] at h
  exact h

private theorem FC_single_norm {D N : ℕ} (i : Idx D N) :
    ∑ k, ‖(Pi.single i (1 : ℂ) : Idx D N → ℂ) k‖ ^ 2 ≤ 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

set_option maxHeartbeats 1000000 in
private theorem FC_expand (l k : ℕ) (C' : ℕ → ℝ) : ∃ Kr : ℝ, 0 ≤ Kr ∧
    ∀ (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)), LLClass D N C' θ μ →
    ∀ (Λ : Matrix (Idx D N) (Idx D N) ℂ), Λ.IsHermitian → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
    ∀ ch : FC_Ch D N, (∀ g ∈ ch, g.2.1 = Λ ∧ (g.2.2 = z ∨ g.2.2 = star z) ∧ opNorm g.1 ≤ 1) →
    1 ≤ ch.length → ch.length ≤ 2 →
    ∀ Xs : Matrix (Idx D N) (Idx D N) ℂ, opNorm Xs ≤ 1 → ∀ i j : Idx D N,
      ‖(∫ h, (chainB h ch * Xs) i j * starRingEnd ℂ (h i j) ∂μ) -
          ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
            ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
              ((-(if i = j then 1 / 2 else 1)) ^ (p + q) *
                ∫ h, FC_evalPoly h ch Xs i j (FC_Dpq ch.length p q) ∂μ)‖ ≤
        Kr * ((D : ℝ) * N) ^ (ch.length - 1) *
          ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * (z.im)⁻¹) ^ (2 + l + 1) +
            (1 + (z.im)⁻¹) ^ (2 + l + 1) *
              Real.sqrt (0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (z.im / 24)) ^ (-(k : ℝ)))) := by
  obtain ⟨K, hK0, hK⟩ := expansion_hp l 2 k C'
  refine ⟨K, hK0, ?_⟩
  intro D N θ μ hμ Λ hΛ z hz hz1 ch hch hn1 hn2 Xs hXs i j
  have hchv : ∀ f ∈ ch, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
    intro f hf
    obtain ⟨h1, h2, -⟩ := hch f hf
    refine ⟨h1 ▸ hΛ, ?_⟩
    rcases h2 with h2 | h2 <;> rw [h2]
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  set x : Idx D N → ℂ := Pi.single i 1
  set y : Idx D N → ℂ := fun γ => Xs γ j
  have hx : ∑ r, ‖x r‖ ^ 2 ≤ 1 := FC_single_norm i
  have hy : ∑ r, ‖y r‖ ^ 2 ≤ 1 := by
    have h1 := FC_col_le Xs j
    have h0 : 0 ≤ opNorm Xs := by unfold opNorm; exact norm_nonneg _
    nlinarith
  obtain ⟨V, P, -, hVn, hP1, hP2, hP3⟩ := chainB_resPoly ch hn1 x y hx hy
  have hPF : ∀ h : Idx D N → Idx D N → ℂ, resPolyEval P h = (chainB h ch * Xs) i j := by
    intro h
    rw [hP3]
    simp only [x, y, Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  set V' := insert (Pi.single i (1 : ℂ)) (insert (Pi.single j (1 : ℂ)) V)
  have hV'n : ∀ v ∈ V', ∑ r, ‖v r‖ ^ 2 ≤ 1 := by
    intro v hv
    simp only [V', Finset.mem_insert] at hv
    rcases hv with rfl | rfl | hv
    · exact FC_single_norm i
    · exact FC_single_norm j
    · exact hVn v hv
  set Ξ : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ) := {(Λ, z)}
  have hΞ : ∀ p ∈ Ξ, p.1.IsHermitian ∧ z.im ≤ p.2.im := by
    intro p hp; simp only [Ξ, Finset.mem_singleton] at hp; subst hp; exact ⟨hΛ, le_rfl⟩
  have hPc : ∀ t ∈ P, t.2.length ≤ 2 ∧ ∀ f ∈ t.2, f.1 ∈ V' ∧ f.2.1 ∈ V' ∧
      ∃ p ∈ Ξ, f.2.2 = p ∨ f.2.2 = (p.1, starRingEnd ℂ p.2) := by
    intro t ht
    obtain ⟨hl, hf⟩ := hP1 t ht
    refine ⟨hl ▸ hn2, fun f hfm => ?_⟩
    obtain ⟨h1, h2, g, hg, hfg⟩ := hf f hfm
    refine ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h1),
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h2), (Λ, z), Finset.mem_singleton_self _,
      ?_⟩
    obtain ⟨g1, g2, -⟩ := hch g hg
    rw [hfg]
    rcases g2 with g2 | g2
    · left; rw [Prod.ext_iff]; exact ⟨g1, g2⟩
    · right; rw [Prod.ext_iff]; exact ⟨g1, by simpa using g2⟩
  have hΓ : 1 ≤ (z.im)⁻¹ := one_le_inv₀ hz |>.2 hz1
  have hM : 0 < z.im / 24 := by positivity
  have hMΓ : 24 * (z.im / 24) * (z.im)⁻¹ ≤ 1 := by
    rw [show 24 * (z.im / 24) * (z.im)⁻¹ = z.im * (z.im)⁻¹ by ring, mul_inv_cancel₀ hz.ne']
  have hbad : μ {h | ∃ p ∈ Ξ, ∃ x ∈ V', ∃ y ∈ V',
      (z.im)⁻¹ < ‖resFactorEval (x, y, p.1, p.2) (symArr h)‖} ≤ ENNReal.ofReal 0 := by
    have e : {h : Idx D N → Idx D N → ℂ | ∃ p ∈ Ξ, ∃ x ∈ V', ∃ y ∈ V',
        (z.im)⁻¹ < ‖resFactorEval (x, y, p.1, p.2) (symArr h)‖} = ∅ := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_lt]
      intro p hp x' hx' y' hy'
      simp only [Ξ, Finset.mem_singleton] at hp
      subst hp
      have hH : (Matrix.of (symArr h) + Λ).IsHermitian := (symArr_isHermitian h).add hΛ
      have h1 := FC_form_le (res (Matrix.of (symArr h) + Λ) z) x' y'
      have h2 := opNorm_res_le _ hH z hz
      have h3 : Real.sqrt (∑ k, ‖x' k‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (hV'n x' hx')
      have h4 : Real.sqrt (∑ k, ‖y' k‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (hV'n y' hy')
      have h0 : 0 ≤ opNorm (res (Matrix.of (symArr h) + Λ) z) := by
        unfold opNorm; exact norm_nonneg _
      unfold resFactorEval
      calc _ ≤ _ := h1
        _ ≤ opNorm (res (Matrix.of (symArr h) + Λ) z) * 1 * 1 := by
            gcongr
        _ ≤ _ := by linarith
    rw [e]; simp
  have hexp := hK D N θ μ hμ Ξ z.im hz hΞ i j V' (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hV'n P hPc (z.im)⁻¹ (z.im / 24) 0
    hΓ hM hMΓ le_rfl hbad
  have hint : ∀ p q : ℕ, ∫ h, wirt p q (fun w => resPolyEval P (setEntry h i j w)) (h i j) ∂μ =
      (-(if i = j then 1 / 2 else 1)) ^ (p + q) *
        ∫ h, FC_evalPoly h ch Xs i j (FC_Dpq ch.length p q) ∂μ := by
    intro p q
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    have e : (fun w => resPolyEval P (setEntry h i j w)) =
        fun w => (chainB (setEntry h i j w) ch * Xs) i j := by funext w; exact hPF _
    rw [e]
    exact FC_wirt_point ch hchv hn1 Xs h hh i j p q
  simp only [hint] at hexp
  simp only [hPF] at hexp
  have hc : (P.map fun t => ‖t.1‖).sum ≤ ((D : ℝ) * N) ^ (ch.length - 1) := by
    refine hP2.trans ?_
    have : (ch.map fun f => opNorm f.1).prod ≤ 1 :=
      FC_prod_le_one ch (fun f => opNorm f.1) (fun f _ => by unfold opNorm; exact norm_nonneg _)
        (fun f hf => (hch f hf).2.2)
    have hp : 0 ≤ ((D : ℝ) * N) ^ (ch.length - 1) := by positivity
    nlinarith
  have hR0 : 0 ≤ (N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * (z.im)⁻¹) ^ (2 + l + 1) +
      (1 + (z.im)⁻¹) ^ (2 + l + 1) *
        Real.sqrt (0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (z.im / 24)) ^ (-(k : ℝ))) := by positivity
  exact hexp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hK0) hR0)

end

section

def FC_segOK (n : ℕ) (s : FC_Seg) : Prop :=
  s.1 < s.2.1 ∧ s.2.1 ≤ n ∧ (s.2.2.2 = true → s.2.1 = n) ∧ (0 < s.1 → s.2.2.1 = true)

private instance (n : ℕ) (s : FC_Seg) : Decidable (FC_segOK n s) := by unfold FC_segOK; infer_instance

private def FC_excess (m : FC_Mono) : ℕ := (m.map fun f => f.1.2.1 - f.1.1 - 1).sum

private def FC_tot (m : FC_Mono) : ℕ := (m.map fun f => f.1.2.1 - f.1.1).sum

private theorem FC_dFac_inv (n : ℕ) (b : Bool) (f : FC_Fac) (hf : FC_segOK n f.1) :
    ∀ t ∈ FC_dFac b f, (∀ g ∈ t, FC_segOK n g.1) ∧ t.length = 2 ∧
      FC_excess t = f.1.2.1 - f.1.1 - 1 := by
  intro t ht
  simp only [FC_dFac, List.mem_map, List.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  obtain ⟨h1, h2, h3, h4⟩ := hf
  refine ⟨fun g hg => ?_, by simp, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · refine ⟨by simp, by simp; omega, by simp, fun h => h4 h⟩
    · refine ⟨by simp; omega, h2, fun h => h3 h, fun _ => rfl⟩
  · simp only [FC_excess, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

private theorem FC_dFac_length (b : Bool) (f : FC_Fac) :
    (FC_dFac b f).length = f.1.2.1 - f.1.1 := by simp [FC_dFac]

private theorem FC_dMono_inv (n : ℕ) (b : Bool) (m : FC_Mono) (hm : ∀ f ∈ m, FC_segOK n f.1) :
    (∀ t ∈ FC_dMono b m, (∀ g ∈ t, FC_segOK n g.1) ∧ t.length = m.length + 1 ∧
      FC_excess t = FC_excess m) ∧ (FC_dMono b m).length = FC_tot m := by
  induction m with
  | nil => simp [FC_dMono, FC_tot]
  | cons f m ih =>
    have hf := hm f (by simp)
    obtain ⟨ih1, ih2⟩ := ih fun g hg => hm g (by simp [hg])
    refine ⟨fun t ht => ?_, ?_⟩
    · simp only [FC_dMono, List.mem_append, List.mem_map] at ht
      rcases ht with ⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩
      · obtain ⟨a1, a2, a3⟩ := FC_dFac_inv n b f hf t' ht'
        refine ⟨fun g hg => ?_, by simp [a2]; omega, ?_⟩
        · rcases List.mem_append.1 hg with hg | hg
          · exact a1 g hg
          · exact hm g (by simp [hg])
        · simp only [FC_excess, List.map_append, List.sum_append] at a3 ⊢
          simp only [List.map_cons, List.sum_cons]
          rw [a3]
      · obtain ⟨a1, a2, a3⟩ := ih1 t' ht'
        refine ⟨fun g hg => ?_, by simp [a2], ?_⟩
        · rcases List.mem_cons.1 hg with rfl | hg
          · exact hf
          · exact a1 g hg
        · simp only [FC_excess, List.map_cons, List.sum_cons] at a3 ⊢
          rw [a3]
    · simp only [FC_dMono, List.length_append, List.length_map, FC_dFac_length, ih2, FC_tot,
        List.map_cons, List.sum_cons]

private theorem FC_tot_eq (n : ℕ) (m : FC_Mono) (hm : ∀ f ∈ m, FC_segOK n f.1) :
    FC_tot m = FC_excess m + m.length := by
  induction m with
  | nil => simp [FC_tot, FC_excess]
  | cons f m ih =>
    have hf := (hm f (by simp)).1
    have ih' := ih fun g hg => hm g (by simp [hg])
    simp only [FC_tot, FC_excess, List.map_cons, List.sum_cons, List.length_cons] at ih' ⊢
    omega

private theorem FC_dPoly_inv (n d : ℕ) (b : Bool) (P : FC_Poly)
    (hP : ∀ m ∈ P, (∀ f ∈ m, FC_segOK n f.1) ∧ m.length = d + 1 ∧ FC_excess m = n - 1) :
    (∀ m ∈ FC_dPoly b P, (∀ f ∈ m, FC_segOK n f.1) ∧ m.length = d + 1 + 1 ∧
      FC_excess m = n - 1) ∧ (FC_dPoly b P).length = P.length * (n - 1 + (d + 1)) := by
  refine ⟨fun m hm => ?_, ?_⟩
  · simp only [FC_dPoly, List.mem_flatMap] at hm
    obtain ⟨m', hm', hm⟩ := hm
    obtain ⟨a1, a2, a3⟩ := hP m' hm'
    obtain ⟨b1, b2, b3⟩ := (FC_dMono_inv n b m' a1).1 m hm
    exact ⟨b1, by rw [b2, a2], by rw [b3, a3]⟩
  · simp only [FC_dPoly]
    induction P with
    | nil => simp
    | cons m P ih =>
      have ih' := ih fun m' hm' => hP m' (by simp [hm'])
      obtain ⟨a1, a2, a3⟩ := hP m (by simp)
      rw [List.flatMap_cons, List.length_append, ih', (FC_dMono_inv n b m a1).2,
        FC_tot_eq n m a1, a2, a3, List.length_cons]
      ring

private theorem FC_iter_inv (n : ℕ) (hn : 1 ≤ n) (b : Bool) (P : FC_Poly) (d : ℕ)
    (hP : ∀ m ∈ P, (∀ f ∈ m, FC_segOK n f.1) ∧ m.length = d + 1 ∧ FC_excess m = n - 1)
    (k : ℕ) :
    (∀ m ∈ (FC_dPoly b)^[k] P, (∀ f ∈ m, FC_segOK n f.1) ∧ m.length = d + k + 1 ∧
      FC_excess m = n - 1) ∧ ((FC_dPoly b)^[k] P).length ≤ P.length * (n + d + k) ^ k := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨i1, i2⟩ := ih
    obtain ⟨j1, j2⟩ := FC_dPoly_inv n (d + k) b _ i1
    refine ⟨fun m hm => ?_, ?_⟩
    · obtain ⟨a1, a2, a3⟩ := j1 m hm
      exact ⟨a1, by rw [a2]; ring, a3⟩
    · rw [j2]
      have e : n - 1 + (d + k + 1) = n + d + k := by omega
      rw [e]
      calc ((FC_dPoly b)^[k] P).length * (n + d + k) ≤
          P.length * (n + d + k) ^ k * (n + d + k) := Nat.mul_le_mul_right _ i2
        _ ≤ P.length * (n + d + (k + 1)) ^ (k + 1) := by
          rw [mul_assoc, ← pow_succ]
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

private theorem FC_P0_inv (n : ℕ) (hn : 1 ≤ n) :
    ∀ m ∈ FC_P0 n, (∀ f ∈ m, FC_segOK n f.1) ∧ m.length = 0 + 1 ∧ FC_excess m = n - 1 := by
  intro m hm
  simp only [FC_P0, List.mem_cons, List.not_mem_nil, or_false] at hm
  subst hm
  refine ⟨fun f hf => ?_, by simp, by simp [FC_excess]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact ⟨by simp; omega, le_rfl, fun _ => rfl, fun h => absurd h (lt_irrefl 0)⟩

private theorem FC_Dpq_inv (n : ℕ) (hn : 1 ≤ n) (p q : ℕ) :
    (∀ m ∈ FC_Dpq n p q, (∀ f ∈ m, FC_segOK n f.1) ∧ m.length = p + q + 1 ∧
      FC_excess m = n - 1) ∧ (FC_Dpq n p q).length ≤ (n + p + q) ^ (p + q) := by
  obtain ⟨a1, a2⟩ := FC_iter_inv n hn true (FC_P0 n) 0 (FC_P0_inv n hn) q
  obtain ⟨b1, b2⟩ := FC_iter_inv n hn false _ q (fun m hm => by
    obtain ⟨x1, x2, x3⟩ := a1 m hm; exact ⟨x1, by rw [x2]; ring, x3⟩) p
  refine ⟨fun m hm => ?_, ?_⟩
  · obtain ⟨x1, x2, x3⟩ := b1 m hm
    exact ⟨x1, by rw [x2]; ring, x3⟩
  · unfold FC_Dpq
    refine b2.trans ?_
    have h1 : ((FC_dPoly true)^[q] (FC_P0 n)).length ≤ (n + q) ^ q := by
      have hl : (FC_P0 n).length = 1 := rfl
      rw [hl, one_mul, add_zero] at a2
      exact a2
    calc ((FC_dPoly true)^[q] (FC_P0 n)).length * (n + q + p) ^ p
        ≤ (n + q) ^ q * (n + q + p) ^ p := Nat.mul_le_mul_right _ h1
      _ ≤ (n + p + q) ^ q * (n + p + q) ^ p :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) q) (Nat.pow_le_pow_left (by omega) p)
      _ = (n + p + q) ^ (p + q) := by rw [← pow_add]; ring_nf

private theorem FC_mono_sup' {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (ch : FC_Ch D N)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (n : ℕ) (w K : ℝ) (hw : 0 ≤ w) (hK : 0 ≤ K)
    (hsup : ∀ s, FC_segOK n s → ∀ x y, ‖FC_evalSeg h ch X s x y‖ ≤ K * w ^ (s.2.1 - s.1 - 1))
    (i j : Idx D N) : ∀ m : FC_Mono, (∀ f ∈ m, FC_segOK n f.1) →
      ‖FC_evalMono h ch X i j m‖ ≤ K ^ m.length * w ^ FC_excess m := by
  intro m
  induction m with
  | nil => intro _; simp [FC_evalMono, FC_excess]
  | cons f m ih =>
    intro hm
    rw [FC_evalMono_cons, norm_mul, List.length_cons, pow_succ]
    have h1 : ‖FC_evalFac h ch X i j f‖ ≤ K * w ^ (f.1.2.1 - f.1.1 - 1) :=
      hsup f.1 (hm f (by simp)) _ _
    have h2 := ih fun f' hf' => hm f' (by simp [hf'])
    have e : FC_excess (f :: m) = (f.1.2.1 - f.1.1 - 1) + FC_excess m := by
      simp [FC_excess]
    rw [e, pow_add]
    calc ‖FC_evalFac h ch X i j f‖ * ‖FC_evalMono h ch X i j m‖
        ≤ (K * w ^ (f.1.2.1 - f.1.1 - 1)) * (K ^ m.length * w ^ FC_excess m) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hK (pow_nonneg hw _))
      _ = _ := by ring

private theorem FC_list_sum_le {α : Type*} (l : List α) (g : α → ℂ) (B : ℝ) (hb : ∀ a ∈ l, ‖g a‖ ≤ B) :
    ‖(l.map g).sum‖ ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := hb a (by simp)
    have h2 := ih fun b hb' => hb b (by simp [hb'])
    push_cast
    calc ‖g a + (t.map g).sum‖ ≤ ‖g a‖ + ‖(t.map g).sum‖ := norm_add_le _ _
      _ ≤ B + t.length * B := add_le_add h1 h2
      _ = _ := by ring

private theorem FC_poly_sup {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (ch : FC_Ch D N)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (hn : 1 ≤ ch.length) (w K : ℝ) (hw : 0 ≤ w)
    (hK : 0 ≤ K) (hsup : ∀ s, FC_segOK ch.length s → ∀ x y,
      ‖FC_evalSeg h ch X s x y‖ ≤ K * w ^ (s.2.1 - s.1 - 1)) (p q : ℕ) (i j : Idx D N) :
    ‖FC_evalPoly h ch X i j (FC_Dpq ch.length p q)‖ ≤
      ((ch.length + p + q) ^ (p + q) : ℕ) * (K ^ (p + q + 1) * w ^ (ch.length - 1)) := by
  obtain ⟨hinv, hlen⟩ := FC_Dpq_inv ch.length hn p q
  unfold FC_evalPoly
  have hb : ∀ m ∈ FC_Dpq ch.length p q,
      ‖FC_evalMono h ch X i j m‖ ≤ K ^ (p + q + 1) * w ^ (ch.length - 1) := by
    intro m hm
    obtain ⟨a1, a2, a3⟩ := hinv m hm
    have := FC_mono_sup' h ch X ch.length w K hw hK hsup i j m a1
    rwa [a2, a3] at this
  refine (FC_list_sum_le _ _ _ hb).trans ?_
  refine mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (mul_nonneg (pow_nonneg hK _)
    (pow_nonneg hw _))

private theorem FC_int_split {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : Ω → ℂ) (hf : AEStronglyMeasurable f μ) (S : Set Ω) (Bg Bc ε : ℝ) (hBg : 0 ≤ Bg)
    (hBc : 0 ≤ Bc) (hgood : ∀ᵐ x ∂μ, x ∈ S → ‖f x‖ ≤ Bg) (hcrude : ∀ᵐ x ∂μ, ‖f x‖ ≤ Bc)
    (hbad : μ Sᶜ ≤ ENNReal.ofReal ε) (hε : 0 ≤ ε) :
    ‖∫ x, f x ∂μ‖ ≤ Bg + Bc * ε := by
  set T := toMeasurable μ Sᶜ with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hμT : μ T ≤ ENNReal.ofReal ε := by rw [hT, measure_toMeasurable]; exact hbad
  have hfi : Integrable (fun x => ‖f x‖) μ :=
    (integrable_const Bc).mono' hf.norm (by
      filter_upwards [hcrude] with x hx; rw [norm_norm]; exact hx)
  have hgi : Integrable (fun x => Bg + T.indicator (fun _ => Bc) x) μ :=
    (integrable_const Bg).add ((integrable_const Bc).indicator hTm)
  have hle : ∀ᵐ x ∂μ, ‖f x‖ ≤ Bg + T.indicator (fun _ => Bc) x := by
    filter_upwards [hgood, hcrude] with x hg hc
    by_cases hx : x ∈ S
    · have := hg hx
      have : 0 ≤ T.indicator (fun _ => Bc) x := Set.indicator_nonneg (fun _ _ => hBc) x
      linarith
    · have hxT : x ∈ T := subset_toMeasurable μ Sᶜ hx
      rw [Set.indicator_of_mem hxT]
      linarith
  calc ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (Bg + T.indicator (fun _ => Bc) x) ∂μ := integral_mono_ae hfi hgi hle
    _ = Bg + Bc * (μ T).toReal := by
        rw [integral_add (integrable_const _) ((integrable_const Bc).indicator hTm),
          integral_const, integral_indicator hTm, setIntegral_const]
        simp [measureReal_def]
        ring
    _ ≤ Bg + Bc * ε := by
        have : (μ T).toReal ≤ ε := by
          have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hμT
          rwa [ENNReal.toReal_ofReal hε] at this
        nlinarith

end

section

section FC_util
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem FC_opNorm_nonneg (X : Matrix ι ι ℂ) : 0 ≤ opNorm X := by unfold opNorm; exact norm_nonneg _

private theorem FC_opNorm_conjTranspose (X : Matrix ι ι ℂ) : opNorm Xᴴ = opNorm X := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) X)

private theorem FC_opNorm_one : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

private theorem FC_opNorm_res (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (ξ : ℂ) (hξ : ξ = z ∨ ξ = star z) : opNorm (res X ξ) ≤ (z.im)⁻¹ := by
  rcases hξ with rfl | rfl
  · exact opNorm_res_le X hX ξ hz
  · rw [show star z = starRingEnd ℂ z from rfl, res_conj X hX z hz, FC_opNorm_conjTranspose]
    exact opNorm_res_le X hX z hz

end FC_util

private theorem FC_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

def FC_chOK {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (ch : FC_Ch D N) : Prop :=
  ∀ g ∈ ch, g.2.1 = Λ ∧ (g.2.2 = z ∨ g.2.2 = star z) ∧ opNorm g.1 ≤ 1

private theorem FC_chOK_valid {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) {ch : FC_Ch D N} (hch : FC_chOK Λ z ch) :
    ∀ f ∈ ch, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0 := by
  intro f hf
  obtain ⟨h1, h2, -⟩ := hch f hf
  refine ⟨h1 ▸ hΛ, ?_⟩
  rcases h2 with h2 | h2 <;> rw [h2]
  · exact hz.ne'
  · simp only [Complex.star_def, Complex.conj_im]; linarith

private theorem FC_chOK_sub {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} {z : ℂ} {ch : FC_Ch D N}
    (hch : FC_chOK Λ z ch) (a b : ℕ) (o : Bool) : FC_chOK Λ z (FC_segList ch a b o) := by
  intro g hg
  unfold FC_segList at hg
  set l := (ch.drop a).take (b - a)
  have hl : ∀ g ∈ l, g ∈ ch := fun g hg => List.mem_of_mem_drop (List.mem_of_mem_take hg)
  cases hq : l with
  | nil => rw [hq] at hg; simp [FC_mod] at hg
  | cons f t =>
    rw [hq] at hg
    simp only [FC_mod, List.mem_cons] at hg
    have hf := hch f (hl f (by rw [hq]; simp))
    rcases hg with rfl | hg
    · cases o
      · exact hf
      · exact ⟨hf.1, hf.2.1, FC_opNorm_one⟩
    · exact hch g (hl g (by rw [hq]; simp [hg]))

private theorem FC_chain_opNorm {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ∀ ch : FC_Ch D N, FC_chOK Λ z ch → opNorm (chainB h ch) ≤ (z.im)⁻¹ ^ ch.length := by
  intro ch
  induction ch with
  | nil => intro _; simpa [chainB] using FC_opNorm_one
  | cons g t ih =>
    intro hc
    have hg := hc g (by simp)
    have ht := ih fun g' hg' => hc g' (by simp [hg'])
    have e : chainB h (g :: t) = g.1 * res (Matrix.of h + g.2.1) g.2.2 * chainB h t := by
      simp [chainB]
    rw [e, List.length_cons, pow_succ]
    have hH : (Matrix.of h + g.2.1).IsHermitian := hg.1 ▸ hh.add hΛ
    have h1 := FC_opNorm_res _ hH z hz g.2.2 hg.2.1
    refine (opNorm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (FC_opNorm_nonneg _)).trans ?_
    have h0 := FC_opNorm_nonneg (res (Matrix.of h + g.2.1) g.2.2)
    have h2 := FC_opNorm_nonneg g.1
    have h3 := FC_opNorm_nonneg (chainB h t)
    have hi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
    calc opNorm g.1 * opNorm (res (Matrix.of h + g.2.1) g.2.2) * opNorm (chainB h t)
        ≤ 1 * (z.im)⁻¹ * (z.im)⁻¹ ^ t.length := by
          gcongr
          exact hg.2.2
      _ = _ := by ring

private theorem FC_seg_crude {D N : ℕ} {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (ch : FC_Ch D N) (hch : FC_chOK Λ z ch) (X : Matrix (Idx D N) (Idx D N) ℂ)
    (hX : opNorm X ≤ 1) (s : FC_Seg) (hs : FC_segOK ch.length s) (x y : Idx D N) :
    ‖FC_evalSeg h ch X s x y‖ ≤ (z.im)⁻¹ * (z.im)⁻¹ ^ (s.2.1 - s.1 - 1) := by
  have hlen := FC_segList_length ch s.1 s.2.1 s.2.2.1 hs.2.1
  have hc := FC_chain_opNorm hΛ hz h hh _ (FC_chOK_sub hch s.1 s.2.1 s.2.2.1)
  rw [hlen] at hc
  have hY : opNorm (if s.2.2.2 then X else 1) ≤ 1 := by
    split_ifs
    · exact hX
    · exact FC_opNorm_one
  refine (norm_apply_le_opNorm _ x y).trans ?_
  unfold FC_evalSeg
  refine (opNorm_mul_le _ _).trans ?_
  have e : (z.im)⁻¹ * (z.im)⁻¹ ^ (s.2.1 - s.1 - 1) = (z.im)⁻¹ ^ (s.2.1 - s.1) := by
    rw [← pow_succ']; congr 1; have := hs.1; omega
  rw [e]
  calc _ ≤ (z.im)⁻¹ ^ (s.2.1 - s.1) * 1 :=
        mul_le_mul hc hY (FC_opNorm_nonneg _) (pow_nonneg (inv_nonneg.2 hz.le) _)
    _ = _ := by ring

private theorem FC_cont_chain {D N : ℕ} (ch : FC_Ch D N) (hch : ∀ f ∈ ch, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
    (x y : Idx D N) : Continuous (fun h => chainB (symArr h) ch x y) := by
  rcases Nat.eq_zero_or_pos ch.length with h0 | h0
  · have : ch = [] := List.length_eq_zero_iff.1 h0
    subst this
    simp only [chainB, List.map_nil, List.prod_nil]
    exact continuous_const
  · obtain ⟨V, P, -, -, hP1, -, hP3⟩ := chainB_resPoly ch h0 (Pi.single x 1) (Pi.single y 1)
      (FC_single_norm x) (FC_single_norm y)
    have hPv : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
      intro t ht f hf
      obtain ⟨-, -, g, hg, hfg⟩ := (hP1 t ht).2 f hf
      rw [hfg]; exact hch g hg
    have e : (fun h => chainB (symArr h) ch x y) = fun h => resPolyEval P (symArr h) := by
      funext h
      rw [hP3]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.single_apply]
      rw [Finset.sum_eq_single x]
      · simp only [↓reduceIte, star_one, one_mul]
        rw [Finset.sum_eq_single y]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [e]
    exact (contDiff_resPoly_symArr P hPv 0).continuous

private theorem FC_cont_poly {D N : ℕ} (ch : FC_Ch D N) (hch : ∀ f ∈ ch, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) (P : FC_Poly) :
    Continuous (fun h => FC_evalPoly (symArr h) ch X i j P) := by
  have hseg : ∀ (s : FC_Seg) (x y : Idx D N),
      Continuous (fun h => FC_evalSeg (symArr h) ch X s x y) := by
    intro s x y
    unfold FC_evalSeg
    simp only [Matrix.mul_apply]
    exact continuous_finsetSum _ fun γ _ =>
      (FC_cont_chain _ (FC_segList_valid ch hch _ _ _) x γ).mul continuous_const
  have hmono : ∀ m : FC_Mono, Continuous (fun h => FC_evalMono (symArr h) ch X i j m) := by
    intro m
    induction m with
    | nil => simp only [FC_evalMono, List.map_nil, List.prod_nil]; exact continuous_const
    | cons f m ih =>
      simp only [FC_evalMono_cons]
      exact (hseg _ _ _).mul ih
  induction P with
  | nil => simp only [FC_evalPoly, List.map_nil, List.sum_nil]; exact continuous_const
  | cons m P ih =>
    simp only [FC_evalPoly_cons]
    exact (hmono m).add ih

private theorem FC_aesm_poly {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (ch : FC_Ch D N)
    (hch : ∀ f ∈ ch, f.2.1.IsHermitian ∧ f.2.2.im ≠ 0) (X : Matrix (Idx D N) (Idx D N) ℂ)
    (i j : Idx D N) (P : FC_Poly) :
    AEStronglyMeasurable (fun h => FC_evalPoly h ch X i j P) μ := by
  refine (FC_cont_poly ch hch X i j P).aestronglyMeasurable.congr ?_
  filter_upwards [hμh] with h hh
  rw [symArr_of_isHermitian h hh]

end

section

private theorem FC_struct2 (n : ℕ) (hn : n = 1 ∨ n = 2) (p q : ℕ) (hpq : p + q = 2) :
    ∀ m ∈ FC_Dpq n p q, FC_offc m = 1 ∨ 2 ≤ FC_offc m := by
  have hp : p ≤ 2 := by omega
  have hq : q ≤ 2 := by omega
  interval_cases p <;> interval_cases q <;> first | omega | (rcases hn with rfl | rfl <;> decide)

private theorem FC_struct3 (n : ℕ) (hn : n = 1 ∨ n = 2) (p q : ℕ) (hpq : p + q = 3)
    (hne : ¬ (p = 2 ∧ q = 1)) : ∀ m ∈ FC_Dpq n p q, 2 ≤ FC_offc m := by
  have hp : p ≤ 3 := by omega
  have hq : q ≤ 3 := by omega
  interval_cases p <;> interval_cases q <;> first | omega | (exact absurd ⟨rfl, rfl⟩ hne) |
    (rcases hn with rfl | rfl <;> decide)

private theorem FC_struct21 (n : ℕ) (hn : n = 1 ∨ n = 2) :
    ∀ m ∈ FC_Dpq n 2 1, FC_offc m = 0 ∨ 2 ≤ FC_offc m := by
  rcases hn with rfl | rfl <;> decide

private theorem FC_range_ite (m r : ℕ) (hr : r ≤ m) (g : ℕ → ℂ) :
    ∑ q ∈ Finset.range m, (if q < r then g q else 0) = ∑ q ∈ Finset.range r, g q := by
  rw [← Finset.sum_range_add_sum_Ico _ hr]
  have h1 : ∑ q ∈ Finset.range r, (if q < r then g q else 0) = ∑ q ∈ Finset.range r, g q :=
    Finset.sum_congr rfl fun q hq => if_pos (Finset.mem_range.1 hq)
  have h2 : ∑ q ∈ Finset.Ico r m, (if q < r then g q else 0) = 0 :=
    Finset.sum_eq_zero fun q hq => if_neg (by simp at hq; omega)
  rw [h1, h2, add_zero]

private theorem FC_split (l : ℕ) (hl : 3 ≤ l) (f : ℕ → ℕ → ℂ) :
    ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), f p q =
      f 0 0 + (f 1 0 + f 0 1) + (f 2 0 + f 1 1 + f 0 2) + (f 3 0 + f 2 1 + f 1 2 + f 0 3) +
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          (if 4 ≤ p + q then f p q else 0) := by
  have e1 : ∀ p q, f p q = (if p + q ≤ 3 then f p q else 0) + (if 4 ≤ p + q then f p q else 0) := by
    intro p q
    by_cases h : p + q ≤ 3
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have e2 : ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      (if p + q ≤ 3 then f p q else 0) =
      ∑ p ∈ Finset.range (l + 1), (if p < 4 then
        ∑ q ∈ Finset.range (4 - p), f p q else 0) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    by_cases h : p < 4
    · rw [if_pos h, ← FC_range_ite (l + 1 - p) (4 - p) (by simp at hp; omega)]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : q < 4 - p
      · rw [if_pos (by omega), if_pos hq]
      · rw [if_neg (by omega), if_neg hq]
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun q _ => if_neg (by omega)
  have e3 : ∑ p ∈ Finset.range (l + 1), (if p < 4 then
      ∑ q ∈ Finset.range (4 - p), f p q else 0) =
      ∑ p ∈ Finset.range 4, ∑ q ∈ Finset.range (4 - p), f p q :=
    FC_range_ite (l + 1) 4 (by omega) _
  conv_lhs => enter [2, p, 2, q]; rw [e1 p q]
  simp only [Finset.sum_add_distrib]
  rw [e2, e3]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

private theorem FC_ccum_cw (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) (ht : 0 ≤ t) (p q : ℕ)
    (hpq : 3 ≤ p + q) : ∃ κ : ℂ, ‖κ‖ ≤ ‖ccum (L.νo : Measure ℂ) p q‖ *
      ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ (p + q) ∧ ∀ i j : Idx D N, i ≠ j →
        ccum ((ouMatLaw D N L t).map fun h => h i j) p q = FC_cw κ (starRingEnd ℂ κ) i j := by
  have hG : ccum (cGauss : Measure ℂ) p q = 0 := by
    rw [ccum_cGauss p q (by omega), if_neg (by omega)]
  refine ⟨((Real.exp (-t / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ (p + q) *
      ccum (L.νo : Measure ℂ) p q, ?_, fun i j hij => ?_⟩
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    gcongr
    have h1 : 0 ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
    have h2 : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h3 : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [abs_of_nonneg (mul_nonneg h1 h3)]
    nlinarith
  · by_cases hb : i.1 = j.1
    · rw [FC_ccum_orient D N L t p q (by omega) i j hb hij, hG]
      simp only [mul_zero, add_zero, FC_cw, hb, hij, ne_eq, not_false_eq_true, and_self,
        ↓reduceIte]
    · rw [(ouMatLaw_ccum D N L t i j).1 hb p q hpq]
      simp [FC_cw, hb]

end

section

section FC_wpoly
variable {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (ch : FC_Ch D N) (X : Matrix (Idx D N) (Idx D N) ℂ)

private theorem FC_wprod_pow (w : ℝ) (m : FC_Mono) :
    FC_wprod (fun s => w ^ (s.2.1 - s.1 - 1)) m = w ^ FC_excess m := by
  induction m with
  | nil => simp [FC_wprod, FC_excess]
  | cons f m ih =>
    rw [FC_wprod_cons, ih]
    simp only [FC_excess, List.map_cons, List.sum_cons, pow_add]

private theorem FC_wsum (c : Idx D N → Idx D N → ℂ) (P : FC_Poly) :
    ∑ i, ∑ j, c i j * FC_evalPoly h ch X i j P =
      (P.map fun m => ∑ i, ∑ j, c i j * FC_evalMono h ch X i j m).sum := by
  induction P with
  | nil => simp [FC_evalPoly]
  | cons m P ih =>
    simp only [FC_evalPoly_cons, mul_add, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [ih]

private theorem FC_wpoly_two (Q : FC_Seg → Prop) (w K Kh : ℝ) (hw : 0 ≤ w) (hK : 0 ≤ K) (hKh : 0 ≤ Kh)
    (hsup : ∀ s, Q s → ∀ x y, ‖FC_evalSeg h ch X s x y‖ ≤ K * w ^ (s.2.1 - s.1 - 1))
    (hHS : ∀ s, Q s → ∑ x, ∑ y, ‖FC_evalSeg h ch X s x y‖ ^ 2 ≤
      (Kh * w ^ (s.2.1 - s.1 - 1)) ^ 2)
    (L e : ℕ) (P : FC_Poly)
    (hP : ∀ m ∈ P, (∀ f ∈ m, Q f.1) ∧ 2 ≤ FC_offc m ∧ m.length = L ∧ FC_excess m = e)
    (c : Idx D N → Idx D N → ℂ) (κm : ℝ) (hκ : 0 ≤ κm) (hc : ∀ i j, ‖c i j‖ ≤ κm) :
    ‖∑ i, ∑ j, c i j * FC_evalPoly h ch X i j P‖ ≤
      P.length * (κm * (K ^ (L - 2) * Kh ^ 2 * w ^ e)) := by
  rw [FC_wsum]
  refine FC_list_sum_le _ _ _ fun m hm => ?_
  obtain ⟨a1, a2, a3, a4⟩ := hP m hm
  have hb := FC_mono_two h ch X Q (fun s => w ^ (s.2.1 - s.1 - 1)) K Kh hK hKh
    (fun s => pow_nonneg hw _) hsup hHS m a1 a2
  rw [FC_wprod_pow, a3, a4] at hb
  calc ‖∑ i, ∑ j, c i j * FC_evalMono h ch X i j m‖
      ≤ ∑ i, ∑ j, κm * ‖FC_evalMono h ch X i j m‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hc i j) (norm_nonneg _)
    _ = κm * ∑ i, ∑ j, ‖FC_evalMono h ch X i j m‖ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hκ

private theorem FC_wpoly_struct (Q : FC_Seg → Prop) (w K Kh Ko : ℝ) (hw : 0 ≤ w) (hK : 0 ≤ K)
    (hKh : 0 ≤ Kh) (hKo : 0 ≤ Ko)
    (hsup : ∀ s, Q s → ∀ x y, ‖FC_evalSeg h ch X s x y‖ ≤ K * w ^ (s.2.1 - s.1 - 1))
    (hHS : ∀ s, Q s → ∑ x, ∑ y, ‖FC_evalSeg h ch X s x y‖ ^ 2 ≤
      (Kh * w ^ (s.2.1 - s.1 - 1)) ^ 2)
    (hop : ∀ s, Q s → opNorm (FC_evalSeg h ch X s) ≤ Ko * w ^ (s.2.1 - s.1 - 1))
    (kk : ℕ) (hkk : D * N ≤ 2 ^ kk) (κ κ' : ℂ) (L e : ℕ) (P : FC_Poly)
    (hP : ∀ m ∈ P, (∀ f ∈ m, Q f.1) ∧ (FC_offc m = 1 ∨ 2 ≤ FC_offc m) ∧ m.length = L ∧
      FC_excess m = e) :
    ‖∑ i, ∑ j, FC_cw κ κ' i j * FC_evalPoly h ch X i j P‖ ≤
      P.length * ((‖κ‖ + ‖κ'‖) * ((kk + 2) * Ko * K ^ (L - 1) * (D * N) +
        K ^ (L - 2) * Kh ^ 2) * w ^ e) := by
  rw [FC_wsum]
  refine FC_list_sum_le _ _ _ fun m hm => ?_
  obtain ⟨a1, a2, a3, a4⟩ := hP m hm
  have hκ0 : 0 ≤ ‖κ‖ + ‖κ'‖ := by positivity
  have hcw : ∀ i j : Idx D N, ‖FC_cw κ κ' i j‖ ≤ ‖κ‖ + ‖κ'‖ := by
    intro i j; unfold FC_cw
    split_ifs
    · have := norm_nonneg κ'; linarith
    · have := norm_nonneg κ; linarith
    · simp only [norm_zero]; exact hκ0
  have hwe : 0 ≤ w ^ e := pow_nonneg hw _
  rcases a2 with a2 | a2
  · have hb := FC_mono_one h ch X Q (fun s => w ^ (s.2.1 - s.1 - 1)) K Ko hK
      (fun s => pow_nonneg hw _) hsup hop kk hkk κ κ' m a1 a2
    rw [FC_wprod_pow, a3, a4] at hb
    refine hb.trans ?_
    have h2 : 0 ≤ K ^ (L - 2) * Kh ^ 2 := by positivity
    nlinarith [mul_nonneg hκ0 (mul_nonneg h2 hwe)]
  · have hb := FC_mono_two h ch X Q (fun s => w ^ (s.2.1 - s.1 - 1)) K Kh hK hKh
      (fun s => pow_nonneg hw _) hsup hHS m a1 a2
    rw [FC_wprod_pow, a3, a4] at hb
    have h1 : ‖∑ i, ∑ j, FC_cw κ κ' i j * FC_evalMono h ch X i j m‖ ≤
        (‖κ‖ + ‖κ'‖) * (K ^ (L - 2) * Kh ^ 2 * w ^ e) := by
      calc ‖∑ i, ∑ j, FC_cw κ κ' i j * FC_evalMono h ch X i j m‖
          ≤ ∑ i, ∑ j, (‖κ‖ + ‖κ'‖) * ‖FC_evalMono h ch X i j m‖ := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hcw i j) (norm_nonneg _)
        _ = (‖κ‖ + ‖κ'‖) * ∑ i, ∑ j, ‖FC_evalMono h ch X i j m‖ := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hb hκ0
    refine h1.trans ?_
    have h3 : 0 ≤ (kk + 2) * Ko * K ^ (L - 1) * (D * N) := by positivity
    nlinarith [mul_nonneg hκ0 (mul_nonneg h3 hwe)]

private theorem FC_wpoly_sup (Q : FC_Seg → Prop) (w K : ℝ) (hw : 0 ≤ w) (hK : 0 ≤ K)
    (hsup : ∀ s, Q s → ∀ x y, ‖FC_evalSeg h ch X s x y‖ ≤ K * w ^ (s.2.1 - s.1 - 1))
    (L e : ℕ) (P : FC_Poly)
    (hP : ∀ m ∈ P, (∀ f ∈ m, Q f.1) ∧ m.length = L ∧ FC_excess m = e)
    (c : Idx D N → Idx D N → ℂ) (κm : ℝ) (hκ : 0 ≤ κm) (hc : ∀ i j, ‖c i j‖ ≤ κm) :
    ‖∑ i, ∑ j, c i j * FC_evalPoly h ch X i j P‖ ≤
      ((D : ℝ) * N) ^ 2 * (P.length * (κm * (K ^ L * w ^ e))) := by
  rw [FC_wsum]
  have hb : ∀ m ∈ P, ‖∑ i, ∑ j, c i j * FC_evalMono h ch X i j m‖ ≤
      ((D : ℝ) * N) ^ 2 * (κm * (K ^ L * w ^ e)) := by
    intro m hm
    obtain ⟨a1, a2, a3⟩ := hP m hm
    have hs : ∀ i j, ‖FC_evalMono h ch X i j m‖ ≤ K ^ L * w ^ e := by
      intro i j
      have := FC_mono_sup h ch X Q (fun s => w ^ (s.2.1 - s.1 - 1)) K hK
        (fun s => pow_nonneg hw _) hsup i j m a1
      rwa [FC_wprod_pow, a2, a3] at this
    calc ‖∑ i, ∑ j, c i j * FC_evalMono h ch X i j m‖
        ≤ ∑ _i : Idx D N, ∑ _j : Idx D N, κm * (K ^ L * w ^ e) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul]
          exact mul_le_mul (hc i j) (hs i j) (norm_nonneg _) hκ
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
  refine (FC_list_sum_le _ _ _ hb).trans (le_of_eq ?_)
  ring

end FC_wpoly

private theorem FC_int_wpoly {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) {Λ : Matrix (Idx D N) (Idx D N) ℂ}
    (hΛ : Λ.IsHermitian) {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) (ch : FC_Ch D N)
    (hch : FC_chOK Λ z ch) (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : opNorm X ≤ 1)
    (L e : ℕ) (P : FC_Poly)
    (hP : ∀ m ∈ P, (∀ f ∈ m, FC_segOK ch.length f.1) ∧ m.length = L ∧ FC_excess m = e)
    (c : Idx D N → Idx D N → ℂ) (κm : ℝ) (hκ : 0 ≤ κm) (hc : ∀ i j, ‖c i j‖ ≤ κm)
    (S : Set (Idx D N → Idx D N → ℂ)) (ε : ℝ) (hε : 0 ≤ ε) (hSc : μ Sᶜ ≤ ENNReal.ofReal ε)
    (Bg : ℝ) (hBg : 0 ≤ Bg)
    (hgood : ∀ h ∈ S, (Matrix.of h).IsHermitian →
      ‖∑ i, ∑ j, c i j * FC_evalPoly h ch X i j P‖ ≤ Bg) :
    ‖∑ i, ∑ j, c i j * ∫ h, FC_evalPoly h ch X i j P ∂μ‖ ≤
      Bg + ((D : ℝ) * N) ^ 2 * (P.length * (κm * ((z.im)⁻¹ ^ L * (z.im)⁻¹ ^ e))) * ε := by
  have hchv := FC_chOK_valid hΛ hz hch
  have hm : ∀ i j, AEStronglyMeasurable (fun h => FC_evalPoly h ch X i j P) μ :=
    fun i j => FC_aesm_poly hμh ch hchv X i j P
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  set Bc := ((D : ℝ) * N) ^ 2 * (P.length * (κm * ((z.im)⁻¹ ^ L * (z.im)⁻¹ ^ e))) with hBc
  have hcrude : ∀ h, (Matrix.of h).IsHermitian →
      ‖∑ i, ∑ j, c i j * FC_evalPoly h ch X i j P‖ ≤ Bc := by
    intro h hh
    have := FC_wpoly_sup h ch X (FC_segOK ch.length) (z.im)⁻¹ (z.im)⁻¹ hηi hηi
      (fun s hs x y => FC_seg_crude hΛ hz h hh ch hch X hX s hs x y) L e P hP c κm hκ hc
    exact this
  have hint : ∀ i j, Integrable (fun h => FC_evalPoly h ch X i j P) μ := by
    intro i j
    have hb : ∀ h, (Matrix.of h).IsHermitian → ‖FC_evalPoly h ch X i j P‖ ≤
        P.length * ((z.im)⁻¹ ^ L * (z.im)⁻¹ ^ e) := by
      intro h hh
      rw [FC_evalPoly]
      refine FC_list_sum_le _ _ _ fun m hm' => ?_
      obtain ⟨a1, a2, a3⟩ := hP m hm'
      have := FC_mono_sup h ch X (FC_segOK ch.length) (fun s => (z.im)⁻¹ ^ (s.2.1 - s.1 - 1))
        (z.im)⁻¹ hηi (fun s => pow_nonneg hηi _)
        (fun s hs x y => FC_seg_crude hΛ hz h hh ch hch X hX s hs x y) i j m a1
      rwa [FC_wprod_pow, a2, a3] at this
    exact (integrable_const _).mono' (hm i j) (by
      filter_upwards [hμh] with h hh; exact hb h hh)
  have e1 : ∑ i, ∑ j, c i j * ∫ h, FC_evalPoly h ch X i j P ∂μ =
      ∫ h, ∑ i, ∑ j, c i j * FC_evalPoly h ch X i j P ∂μ := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
  rw [e1]
  have hBc0 : 0 ≤ Bc := by positivity
  refine FC_int_split _ ?_ S Bg Bc ε hBg hBc0 ?_ ?_ hSc hε
  · exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hm i j).const_mul _
  · filter_upwards [hμh] with h hh hS; exact hgood h hS hh
  · filter_upwards [hμh] with h hh; exact hcrude h hh

end

section

private def FC_f {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) (ch : FC_Ch D N)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) (p q : ℕ) : ℂ :=
  ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
    ((-(if i = j then 1 / 2 else 1)) ^ (p + q) *
      ∫ h, FC_evalPoly h ch X i j (FC_Dpq ch.length p q) ∂μ)

structure FC_Good {D N : ℕ} (ch : FC_Ch D N) (X : Matrix (Idx D N) (Idx D N) ℂ)
    (S : Set (Idx D N → Idx D N → ℂ)) (η w : ℝ) : Prop where
  sup : ∀ h ∈ S, (Matrix.of h).IsHermitian → ∀ s, FC_segOK ch.length s → ∀ x y,
    ‖FC_evalSeg h ch X s x y‖ ≤ 3 * w ^ (s.2.1 - s.1 - 1)
  hs : ∀ h ∈ S, (Matrix.of h).IsHermitian → ∀ s, FC_segOK ch.length s →
    ∑ x, ∑ y, ‖FC_evalSeg h ch X s x y‖ ^ 2 ≤
      (Real.sqrt (3 * D * N / η) * w ^ (s.2.1 - s.1 - 1)) ^ 2
  op : ∀ h ∈ S, (Matrix.of h).IsHermitian → ∀ s, FC_segOK ch.length s →
    opNorm (FC_evalSeg h ch X s) ≤ 3 / η * w ^ (s.2.1 - s.1 - 1)

private theorem FC_rpow_half_pow (N : ℕ) (k : ℕ) :
    ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ k = (N : ℝ) ^ (-((k : ℝ) / 2)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; ring

private theorem FC_inv_pow_mono {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    η⁻¹ ^ a ≤ η⁻¹ ^ b := pow_le_pow_right₀ (one_le_inv₀ hη |>.2 hη1) hab

section FC_pieces
variable {D N : ℕ} {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) {C' : ℕ → ℝ}
  (hμ : LLClass D N C' (Real.exp (-t)) (ouMatLaw D N L t))
  {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1)
  (ch : FC_Ch D N) (hch : FC_chOK Λ z ch) (hn : ch.length = 1 ∨ ch.length = 2)
  (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : opNorm X ≤ 1)
  (S : Set (Idx D N → Idx D N → ℂ)) (ε : ℝ) (hε : 0 ≤ ε)
  (hSc : ouMatLaw D N L t Sᶜ ≤ ENNReal.ofReal ε) (w : ℝ) (hw : 1 ≤ w)
  (hG : FC_Good ch X S z.im w)
include hμ hΛ hz hz1 hch hn hX hε hSc hw hG

set_option maxHeartbeats 1000000 in
private theorem FC_piece_off2 (hN : 1 ≤ N) (ht : 0 ≤ t) (kk : ℕ) (hkk : D * N ≤ 2 ^ kk) (p q : ℕ) (hpq : p + q = 2)
    (Kν : ℝ) (hKν : ‖ccum (L.νo : Measure ℂ) p (q + 1)‖ ≤ Kν) :
    ‖∑ i, ∑ j, (if i ≠ j then FC_f (ouMatLaw D N L t) ch X i j p q else 0)‖ ≤
      16 * (2 * Kν) * (36 * ((kk + 2) * (D * N) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ *
        w ^ (ch.length - 1)) + ((D : ℝ) * N) ^ 2 * (z.im)⁻¹ ^ 4 * ε) := by
  have hprob := hμ.prob
  have hn1 : 1 ≤ ch.length := by omega
  obtain ⟨κ, hκb, hκ⟩ := FC_ccum_cw D N L t ht p (q + 1) (by omega)
  have hKν0 : 0 ≤ Kν := (norm_nonneg _).trans hKν
  have hN3 : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ (p + (q + 1)) = (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [FC_rpow_half_pow]; congr 1
    have : ((p + (q + 1) : ℕ) : ℝ) = 3 := by exact_mod_cast (by omega : p + (q + 1) = 3)
    rw [this]
  have hNp : 0 ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN1 : (N : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  rw [hN3] at hκb
  have hκ' : ‖κ‖ ≤ Kν * (N : ℝ) ^ (-(3 / 2 : ℝ)) :=
    hκb.trans (mul_le_mul_of_nonneg_right hKν hNp)
  set cw : Idx D N → Idx D N → ℂ := FC_cw κ (starRingEnd ℂ κ)
  set P := FC_Dpq ch.length p q
  have e : ∑ i, ∑ j, (if i ≠ j then FC_f (ouMatLaw D N L t) ch X i j p q else 0) =
      (1 / ((p.factorial * q.factorial : ℕ) : ℂ)) *
        ∑ i, ∑ j, cw i j * ∫ h, FC_evalPoly h ch X i j P ∂(ouMatLaw D N L t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp [cw, FC_cw]
    · rw [if_pos hij]
      unfold FC_f
      rw [hκ i j hij, if_neg hij, hpq]
      simp only [cw]
      ring
  rw [e, norm_mul]
  have hfac : ‖(1 / ((p.factorial * q.factorial : ℕ) : ℂ))‖ ≤ 1 := by
    rw [norm_div, norm_one, Complex.norm_natCast]
    have : (1 : ℝ) ≤ ((p.factorial * q.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero p)
        (Nat.factorial_ne_zero q))
    exact div_le_one_of_le₀ this (by positivity)
  obtain ⟨hinv, hlen⟩ := FC_Dpq_inv ch.length hn1 p q
  have hst := FC_struct2 ch.length hn p q hpq
  have hκm : ∀ i j, ‖cw i j‖ ≤ 2 * (Kν * (N : ℝ) ^ (-(3 / 2 : ℝ))) := by
    intro i j
    simp only [cw, FC_cw]
    split_ifs
    · linarith [norm_nonneg κ]
    · rw [Complex.norm_conj]; linarith [norm_nonneg κ]
    · simp only [norm_zero]; positivity
  have hη : 0 < z.im := hz
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  have hw0 : 0 ≤ w := by linarith
  set Bg : ℝ := P.length * ((‖κ‖ + ‖starRingEnd ℂ κ‖) * ((kk + 2) * (3 / z.im) * 3 ^ (3 - 1) *
    (D * N) + 3 ^ (3 - 2) * Real.sqrt (3 * D * N / z.im) ^ 2) * w ^ (ch.length - 1)) with hBg
  have hBg0 : 0 ≤ Bg := by positivity
  have hgood : ∀ h ∈ S, (Matrix.of h).IsHermitian →
      ‖∑ i, ∑ j, cw i j * FC_evalPoly h ch X i j P‖ ≤ Bg := by
    intro h hS hh
    exact FC_wpoly_struct h ch X (FC_segOK ch.length) w 3 (Real.sqrt (3 * D * N / z.im))
      (3 / z.im) hw0 (by norm_num) (Real.sqrt_nonneg _) (by positivity)
      (hG.sup h hS hh) (hG.hs h hS hh) (hG.op h hS hh) kk hkk κ (starRingEnd ℂ κ) 3
      (ch.length - 1) P (fun m hm => ⟨(hinv m hm).1, hst m hm, by rw [(hinv m hm).2.1, hpq],
        (hinv m hm).2.2⟩)
  have hint := FC_int_wpoly (ouMatLaw D N L t) hμ.herm hΛ hz hz1 ch hch X hX (p + q + 1)
    (ch.length - 1) P hinv cw _ (by positivity) hκm S ε hε hSc Bg hBg0 hgood
  have hPl : (P.length : ℝ) ≤ 16 := by
    have h1 : (ch.length + p + q) ^ (p + q) ≤ 16 := by
      rw [hpq]; rcases hn with h | h <;> rw [h] <;> nlinarith
    exact_mod_cast hlen.trans h1
  have hsq : Real.sqrt (3 * D * N / z.im) ^ 2 = 3 * D * N / z.im := Real.sq_sqrt (by positivity)
  have hcc : ‖κ‖ + ‖starRingEnd ℂ κ‖ ≤ 2 * (Kν * (N : ℝ) ^ (-(3 / 2 : ℝ))) := by
    rw [Complex.norm_conj]; linarith
  have hkk0 : (0 : ℝ) ≤ kk := Nat.cast_nonneg _
  have hBg' : Bg ≤ 16 * (2 * Kν) * (36 * ((kk + 2) * (D * N) * (N : ℝ) ^ (-(3 / 2 : ℝ)) *
      (z.im)⁻¹ * w ^ (ch.length - 1))) := by
    rw [hBg, hsq]
    have hin : (kk + 2) * (3 / z.im) * 3 ^ (3 - 1) * (D * N) + 3 ^ (3 - 2) * (3 * D * N / z.im) ≤
        36 * ((kk + 2) * (D * N) * (z.im)⁻¹) := by
      have hDN : (0 : ℝ) ≤ D * N := by positivity
      calc (kk + 2) * (3 / z.im) * 3 ^ (3 - 1) * (D * N) + 3 ^ (3 - 2) * (3 * D * N / z.im)
          = 27 * (kk + 2) * (D * N) * (z.im)⁻¹ + 9 * (D * N) * (z.im)⁻¹ := by
            norm_num; ring
        _ ≤ _ := by nlinarith [mul_nonneg hkk0 (mul_nonneg hDN hηi), mul_nonneg hDN hηi]
    have h0 : 0 ≤ (kk + 2) * (3 / z.im) * 3 ^ (3 - 1) * (D * N) + 3 ^ (3 - 2) *
        (3 * D * N / z.im) := by positivity
    have hwn : 0 ≤ w ^ (ch.length - 1) := pow_nonneg hw0 _
    calc (P.length : ℝ) * ((‖κ‖ + ‖starRingEnd ℂ κ‖) * ((kk + 2) * (3 / z.im) * 3 ^ (3 - 1) *
          (D * N) + 3 ^ (3 - 2) * (3 * D * N / z.im)) * w ^ (ch.length - 1))
        ≤ 16 * ((2 * (Kν * (N : ℝ) ^ (-(3 / 2 : ℝ)))) * (36 * ((kk + 2) * (D * N) * (z.im)⁻¹)) *
            w ^ (ch.length - 1)) := by
          gcongr
      _ = _ := by ring
  have hcr : ((D : ℝ) * N) ^ 2 * (P.length * (2 * (Kν * (N : ℝ) ^ (-(3 / 2 : ℝ))) *
      ((z.im)⁻¹ ^ (p + q + 1) * (z.im)⁻¹ ^ (ch.length - 1)))) * ε ≤
      16 * (2 * Kν) * (((D : ℝ) * N) ^ 2 * (z.im)⁻¹ ^ 4 * ε) := by
    have hpow : (z.im)⁻¹ ^ (p + q + 1) * (z.im)⁻¹ ^ (ch.length - 1) ≤ (z.im)⁻¹ ^ 4 := by
      rw [← pow_add]; exact FC_inv_pow_mono hz hz1 (by omega)
    have hK2 : 2 * (Kν * (N : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 2 * Kν := by nlinarith
    have hDN : (0 : ℝ) ≤ ((D : ℝ) * N) ^ 2 := by positivity
    have hp0 : 0 ≤ (z.im)⁻¹ ^ (p + q + 1) * (z.im)⁻¹ ^ (ch.length - 1) := by positivity
    calc ((D : ℝ) * N) ^ 2 * (P.length * (2 * (Kν * (N : ℝ) ^ (-(3 / 2 : ℝ))) *
          ((z.im)⁻¹ ^ (p + q + 1) * (z.im)⁻¹ ^ (ch.length - 1)))) * ε
        ≤ ((D : ℝ) * N) ^ 2 * (16 * (2 * Kν * (z.im)⁻¹ ^ 4)) * ε := by
          gcongr
      _ = _ := by ring
  calc ‖(1 / ((p.factorial * q.factorial : ℕ) : ℂ))‖ *
        ‖∑ i, ∑ j, cw i j * ∫ h, FC_evalPoly h ch X i j P ∂(ouMatLaw D N L t)‖
      ≤ 1 * (Bg + ((D : ℝ) * N) ^ 2 * (P.length * (2 * (Kν * (N : ℝ) ^ (-(3 / 2 : ℝ))) *
          ((z.im)⁻¹ ^ (p + q + 1) * (z.im)⁻¹ ^ (ch.length - 1)))) * ε) :=
        mul_le_mul hfac hint (norm_nonneg _) zero_le_one
    _ ≤ _ := by nlinarith [hBg', hcr]

private theorem FC_int_pair (p q : ℕ) (i j : Idx D N) :
    ‖∫ h, FC_evalPoly h ch X i j (FC_Dpq ch.length p q) ∂(ouMatLaw D N L t)‖ ≤
      ((ch.length + p + q) ^ (p + q) : ℕ) * (3 ^ (p + q + 1) * w ^ (ch.length - 1)) +
        ((ch.length + p + q) ^ (p + q) : ℕ) * ((z.im)⁻¹ ^ (p + q + 1) *
          (z.im)⁻¹ ^ (ch.length - 1)) * ε := by
  have hprob := hμ.prob
  have hn1 : 1 ≤ ch.length := by omega
  have hchv := FC_chOK_valid hΛ hz hch
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  have hw0 : 0 ≤ w := by linarith
  refine FC_int_split _ (FC_aesm_poly hμ.herm ch hchv X i j _) S _ _ ε (by positivity)
    (by positivity) ?_ ?_ hSc hε
  · filter_upwards [hμ.herm] with h hh hS
    exact FC_poly_sup h ch X hn1 w 3 hw0 (by norm_num) (hG.sup h hS hh) p q i j
  · filter_upwards [hμ.herm] with h hh
    exact FC_poly_sup h ch X hn1 (z.im)⁻¹ (z.im)⁻¹ hηi hηi
      (fun s hs x y => FC_seg_crude hΛ hz h hh ch hch X hX s hs x y) p q i j

private theorem FC_integrable_poly (P : FC_Poly) (L' e : ℕ)
    (hP : ∀ m ∈ P, (∀ f ∈ m, FC_segOK ch.length f.1) ∧ m.length = L' ∧ FC_excess m = e)
    (i j : Idx D N) :
    Integrable (fun h => FC_evalPoly h ch X i j P) (ouMatLaw D N L t) := by
  have hprob := hμ.prob
  have hchv := FC_chOK_valid hΛ hz hch
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  have hb : ∀ h, (Matrix.of h).IsHermitian → ‖FC_evalPoly h ch X i j P‖ ≤
      P.length * ((z.im)⁻¹ ^ L' * (z.im)⁻¹ ^ e) := by
    intro h hh
    rw [FC_evalPoly]
    refine FC_list_sum_le _ _ _ fun m hm' => ?_
    obtain ⟨a1, a2, a3⟩ := hP m hm'
    have := FC_mono_sup h ch X (FC_segOK ch.length) (fun s => (z.im)⁻¹ ^ (s.2.1 - s.1 - 1))
      (z.im)⁻¹ hηi (fun s => pow_nonneg hηi _)
      (fun s hs x y => FC_seg_crude hΛ hz h hh ch hch X hX s hs x y) i j m a1
    rwa [FC_wprod_pow, a2, a3] at this
  exact (integrable_const _).mono' (FC_aesm_poly hμ.herm ch hchv X i j P) (by
    filter_upwards [hμ.herm] with h hh; exact hb h hh)

private theorem FC_piece_off3 (hN : 1 ≤ N) (p q : ℕ) (hpq : p + q = 3) (P : FC_Poly)
    (hP : ∀ m ∈ P, (∀ f ∈ m, FC_segOK ch.length f.1) ∧ 2 ≤ FC_offc m ∧ m.length = 4 ∧
      FC_excess m = ch.length - 1) (hPl : P.length ≤ 125)
    (Kc : ℝ) (hKc0 : 0 ≤ Kc)
    (hKc : ∀ i j : Idx D N, ‖ccum ((ouMatLaw D N L t).map fun h => h i j) p (q + 1)‖ ≤
      Kc * (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2))) :
    ‖∑ i, ∑ j, (if i ≠ j then ccum ((ouMatLaw D N L t).map fun h => h i j) p (q + 1) /
        ((p.factorial * q.factorial : ℕ) : ℂ) * ((-1) ^ (p + q) *
          ∫ h, FC_evalPoly h ch X i j P ∂(ouMatLaw D N L t)) else 0)‖ ≤
      125 * Kc * (27 * ((D * N) * (N : ℝ) ^ (-(2 : ℝ)) * (z.im)⁻¹ * w ^ (ch.length - 1)) +
        ((D : ℝ) * N) ^ 2 * (z.im)⁻¹ ^ 5 * ε) := by
  have hprob := hμ.prob
  have hN4 : (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) = (N : ℝ) ^ (-(2 : ℝ)) := by
    congr 1
    have : ((p + (q + 1) : ℕ) : ℝ) = 4 := by exact_mod_cast (by omega : p + (q + 1) = 4)
    rw [this]; norm_num
  have hNp : 0 ≤ (N : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN1 : (N : ℝ) ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  set c : Idx D N → Idx D N → ℂ := fun i j =>
    if i ≠ j then ccum ((ouMatLaw D N L t).map fun h => h i j) p (q + 1) else 0 with hcdef
  have hc : ∀ i j, ‖c i j‖ ≤ Kc * (N : ℝ) ^ (-(2 : ℝ)) := by
    intro i j
    simp only [hcdef]
    split_ifs
    · rw [← hN4]; exact hKc i j
    · simp only [norm_zero]; positivity
  have e : ∑ i, ∑ j, (if i ≠ j then ccum ((ouMatLaw D N L t).map fun h => h i j) p (q + 1) /
        ((p.factorial * q.factorial : ℕ) : ℂ) * ((-1) ^ (p + q) *
          ∫ h, FC_evalPoly h ch X i j P ∂(ouMatLaw D N L t)) else 0) =
      ((-1) ^ (p + q) / ((p.factorial * q.factorial : ℕ) : ℂ)) *
        ∑ i, ∑ j, c i j * ∫ h, FC_evalPoly h ch X i j P ∂(ouMatLaw D N L t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hcdef]
    split_ifs
    · ring
    · ring
  rw [e, norm_mul]
  have hfac : ‖((-1) ^ (p + q) / ((p.factorial * q.factorial : ℕ) : ℂ))‖ ≤ 1 := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
    have : (1 : ℝ) ≤ ((p.factorial * q.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero p)
        (Nat.factorial_ne_zero q))
    exact div_le_one_of_le₀ this (by positivity)
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  have hw0 : 0 ≤ w := by linarith
  set Bg : ℝ := P.length * ((Kc * (N : ℝ) ^ (-(2 : ℝ))) * (3 ^ (4 - 2) *
    Real.sqrt (3 * D * N / z.im) ^ 2 * w ^ (ch.length - 1))) with hBg
  have hBg0 : 0 ≤ Bg := by positivity
  have hgood : ∀ h ∈ S, (Matrix.of h).IsHermitian →
      ‖∑ i, ∑ j, c i j * FC_evalPoly h ch X i j P‖ ≤ Bg := fun h hS hh =>
    FC_wpoly_two h ch X (FC_segOK ch.length) w 3 (Real.sqrt (3 * D * N / z.im)) hw0
      (by norm_num) (Real.sqrt_nonneg _) (hG.sup h hS hh) (hG.hs h hS hh) 4 (ch.length - 1) P hP
      c _ (by positivity) hc
  have hint := FC_int_wpoly (ouMatLaw D N L t) hμ.herm hΛ hz hz1 ch hch X hX 4
    (ch.length - 1) P (fun m hm => ⟨(hP m hm).1, (hP m hm).2.2⟩) c _ (by positivity) hc S ε hε
    hSc Bg hBg0 hgood
  have hsq : Real.sqrt (3 * D * N / z.im) ^ 2 = 3 * D * N / z.im := Real.sq_sqrt (by positivity)
  have hPl' : (P.length : ℝ) ≤ 125 := by exact_mod_cast hPl
  have hBg' : Bg ≤ 125 * Kc * (27 * ((D * N) * (N : ℝ) ^ (-(2 : ℝ)) * (z.im)⁻¹ *
      w ^ (ch.length - 1))) := by
    rw [hBg, hsq]
    have : (3 : ℝ) ^ (4 - 2) * (3 * D * N / z.im) = 27 * ((D * N) * (z.im)⁻¹) := by
      norm_num; ring
    rw [this]
    have h0 : 0 ≤ (Kc * (N : ℝ) ^ (-(2 : ℝ))) * (27 * ((D * N) * (z.im)⁻¹) *
        w ^ (ch.length - 1)) := by positivity
    calc (P.length : ℝ) * ((Kc * (N : ℝ) ^ (-(2 : ℝ))) * (27 * ((D * N) * (z.im)⁻¹) *
          w ^ (ch.length - 1))) ≤ 125 * ((Kc * (N : ℝ) ^ (-(2 : ℝ))) *
            (27 * ((D * N) * (z.im)⁻¹) * w ^ (ch.length - 1))) :=
          mul_le_mul_of_nonneg_right hPl' h0
      _ = _ := by ring
  have hcr : ((D : ℝ) * N) ^ 2 * (P.length * ((Kc * (N : ℝ) ^ (-(2 : ℝ))) *
      ((z.im)⁻¹ ^ 4 * (z.im)⁻¹ ^ (ch.length - 1)))) * ε ≤
      125 * Kc * (((D : ℝ) * N) ^ 2 * (z.im)⁻¹ ^ 5 * ε) := by
    have hpow : (z.im)⁻¹ ^ 4 * (z.im)⁻¹ ^ (ch.length - 1) ≤ (z.im)⁻¹ ^ 5 := by
      rw [← pow_add]; exact FC_inv_pow_mono hz hz1 (by omega)
    have hK2 : Kc * (N : ℝ) ^ (-(2 : ℝ)) ≤ Kc := by nlinarith
    have hp0 : 0 ≤ (z.im)⁻¹ ^ 4 * (z.im)⁻¹ ^ (ch.length - 1) := by positivity
    calc ((D : ℝ) * N) ^ 2 * (P.length * ((Kc * (N : ℝ) ^ (-(2 : ℝ))) *
          ((z.im)⁻¹ ^ 4 * (z.im)⁻¹ ^ (ch.length - 1)))) * ε
        ≤ ((D : ℝ) * N) ^ 2 * (125 * (Kc * (z.im)⁻¹ ^ 5)) * ε := by
          gcongr
      _ = _ := by ring
  calc ‖((-1) ^ (p + q) / ((p.factorial * q.factorial : ℕ) : ℂ))‖ *
        ‖∑ i, ∑ j, c i j * ∫ h, FC_evalPoly h ch X i j P ∂(ouMatLaw D N L t)‖
      ≤ 1 * (Bg + ((D : ℝ) * N) ^ 2 * (P.length * ((Kc * (N : ℝ) ^ (-(2 : ℝ))) *
          ((z.im)⁻¹ ^ 4 * (z.im)⁻¹ ^ (ch.length - 1)))) * ε) :=
        mul_le_mul hfac hint (norm_nonneg _) zero_le_one
    _ ≤ _ := by nlinarith [hBg', hcr]

end FC_pieces

end

section

private theorem FC_sum_diag_split {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ι → ℂ) :
    ∑ i, ∑ j, g i j = (∑ i, (∑ j, (if i ≠ j then g i j else 0))) + ∑ i, g i i := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : g i i = ∑ j, (if i = j then g i j else 0) := by
    rw [Finset.sum_ite_eq]; simp
  rw [e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = j
  · subst h; simp
  · simp [h]

private theorem FC_evalPoly_filter {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (ch : FC_Ch D N)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) (P : FC_Poly) (g : FC_Mono → Bool) :
    FC_evalPoly h ch X i j P =
      FC_evalPoly h ch X i j (P.filter g) + FC_evalPoly h ch X i j (P.filter fun m => !g m) := by
  rw [← FC_evalPoly_append]
  exact ((List.filter_append_perm g P).map _).sum_eq.symm

private def FC_err (D N : ℕ) (n l k kk : ℕ) (η w ε : ℝ) : ℝ :=
  (kk + 2) * (D * N) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ * w ^ (n - 1) +
    (D * N) * (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ * w ^ (n - 1) +
    (D * N) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * w ^ (n - 1) +
    ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(5 / 2 : ℝ)) * w ^ (n - 1) +
    ((D : ℝ) * N) ^ 2 * η⁻¹ ^ (l + 2) * ε +
    ((D : ℝ) * N) ^ 3 * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * η⁻¹) ^ (2 + l + 1) +
      (1 + η⁻¹) ^ (2 + l + 1) * Real.sqrt (0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (η / 24)) ^ (-(k : ℝ))))

private theorem FC_err_nonneg (D N : ℕ) (n l k kk : ℕ) (η w ε : ℝ) (hη : 0 < η) (hw : 0 ≤ w)
    (hε : 0 ≤ ε) : 0 ≤ FC_err D N n l k kk η w ε := by
  unfold FC_err; positivity

private def FC_lead {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ)) (ch : FC_Ch D N)
    (X : Matrix (Idx D N) (Idx D N) ℂ) : ℂ :=
  ∑ i, ∑ j, if i ≠ j then ccum (μ.map fun h => h i j) 2 (1 + 1) /
    ((Nat.factorial 2 * Nat.factorial 1 : ℕ) : ℂ) * ((-1) ^ (2 + 1) *
      ∫ h, FC_evalPoly h ch X i j ((FC_Dpq ch.length 2 1).filter fun m => FC_offc m == 0) ∂μ)
    else 0

private theorem FC_piece_diag {D N : ℕ} {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) {C' : ℕ → ℝ}
    (hμ : LLClass D N C' (Real.exp (-t)) (ouMatLaw D N L t))
    {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (hz1 : z.im ≤ 1) (ch : FC_Ch D N) (hch : FC_chOK Λ z ch) (hn : ch.length = 1 ∨ ch.length = 2)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : opNorm X ≤ 1)
    (S : Set (Idx D N → Idx D N → ℂ)) (ε : ℝ) (hε : 0 ≤ ε)
    (hSc : ouMatLaw D N L t Sᶜ ≤ ENNReal.ofReal ε) (w : ℝ) (hw : 1 ≤ w)
    (hG : FC_Good ch X S z.im w) (hN : 1 ≤ N) (p q : ℕ) (hd2 : 2 ≤ p + q) (hd3 : p + q ≤ 3)
    (Kc : ℝ) (hKc0 : 0 ≤ Kc)
    (hKc : ∀ i j : Idx D N, ‖ccum ((ouMatLaw D N L t).map fun h => h i j) p (q + 1)‖ ≤
      Kc * (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2))) :
    ‖∑ i, FC_f (ouMatLaw D N L t) ch X i i p q‖ ≤
      Kc * 125 * (81 * ((D * N) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * w ^ (ch.length - 1)) +
        (D * N) * (z.im)⁻¹ ^ 5 * ε) := by
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  have hw0 : 0 ≤ w := by linarith
  have hN32 : (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    have : (3 : ℝ) ≤ ((p + (q + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ p + (q + 1))
    linarith
  have hNp : 0 ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN1 : (N : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  have hb : ∀ i : Idx D N, ‖FC_f (ouMatLaw D N L t) ch X i i p q‖ ≤
      Kc * 125 * (81 * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * w ^ (ch.length - 1)) + (z.im)⁻¹ ^ 5 * ε) := by
    intro i
    unfold FC_f
    have h1 := FC_int_pair L t hμ hΛ hz hz1 ch hch hn X hX S ε hε hSc w hw hG p q i i
    rw [norm_mul, norm_mul, norm_div, norm_pow]
    have hfac : (1 : ℝ) ≤ ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero p)
        (Nat.factorial_ne_zero q))
    have hc : ‖-(if i = i then (1 / 2 : ℂ) else 1)‖ ^ (p + q) ≤ 1 := by
      simp only [↓reduceIte, norm_neg]
      exact pow_le_one₀ (norm_nonneg _) (by norm_num)
    have hcount : (((ch.length + p + q) ^ (p + q) : ℕ) : ℝ) ≤ 125 := by
      have : (ch.length + p + q) ^ (p + q) ≤ 125 := by
        calc (ch.length + p + q) ^ (p + q) ≤ 5 ^ (p + q) :=
              Nat.pow_le_pow_left (by omega) _
          _ ≤ 5 ^ 3 := Nat.pow_le_pow_right (by norm_num) hd3
          _ = 125 := by norm_num
      exact_mod_cast this
    have hp3 : (3 : ℝ) ^ (p + q + 1) ≤ 81 := by
      calc (3 : ℝ) ^ (p + q + 1) ≤ 3 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 81 := by norm_num
    have hpw : (z.im)⁻¹ ^ (p + q + 1) * (z.im)⁻¹ ^ (ch.length - 1) ≤ (z.im)⁻¹ ^ 5 := by
      rw [← pow_add]; exact FC_inv_pow_mono hz hz1 (by omega)
    have hI : ‖∫ h, FC_evalPoly h ch X i i (FC_Dpq ch.length p q) ∂(ouMatLaw D N L t)‖ ≤
        125 * (81 * w ^ (ch.length - 1)) + 125 * (z.im)⁻¹ ^ 5 * ε := by
      refine h1.trans ?_
      have hwn : 0 ≤ w ^ (ch.length - 1) := pow_nonneg hw0 _
      have hc0 : (0 : ℝ) ≤ (((ch.length + p + q) ^ (p + q) : ℕ) : ℝ) := Nat.cast_nonneg _
      gcongr
    have hK := (hKc i i).trans (mul_le_mul_of_nonneg_left hN32 hKc0)
    calc ‖ccum ((ouMatLaw D N L t).map fun h => h i i) p (q + 1)‖ /
          ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ *
          (‖-(if i = i then (1 / 2 : ℂ) else 1)‖ ^ (p + q) *
            ‖∫ h, FC_evalPoly h ch X i i (FC_Dpq ch.length p q) ∂(ouMatLaw D N L t)‖)
        ≤ (Kc * (N : ℝ) ^ (-(3 / 2 : ℝ))) / 1 *
          (1 * (125 * (81 * w ^ (ch.length - 1)) + 125 * (z.im)⁻¹ ^ 5 * ε)) := by
          gcongr
      _ ≤ _ := by
          rw [div_one, one_mul]
          have hwn : 0 ≤ w ^ (ch.length - 1) := pow_nonneg hw0 _
          nlinarith [mul_nonneg hKc0 (mul_nonneg (pow_nonneg hηi 5) hε),
            mul_le_mul_of_nonneg_left hN1 (mul_nonneg hKc0 (mul_nonneg (pow_nonneg hηi 5) hε))]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hb i).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

private theorem FC_piece_high {D N : ℕ} {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ) {C' : ℕ → ℝ}
    (hμ : LLClass D N C' (Real.exp (-t)) (ouMatLaw D N L t))
    {Λ : Matrix (Idx D N) (Idx D N) ℂ} (hΛ : Λ.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (hz1 : z.im ≤ 1) (ch : FC_Ch D N) (hch : FC_chOK Λ z ch) (hn : ch.length = 1 ∨ ch.length = 2)
    (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : opNorm X ≤ 1)
    (S : Set (Idx D N → Idx D N → ℂ)) (ε : ℝ) (hε : 0 ≤ ε)
    (hSc : ouMatLaw D N L t Sᶜ ≤ ENNReal.ofReal ε) (w : ℝ) (hw : 1 ≤ w)
    (hG : FC_Good ch X S z.im w) (hN : 1 ≤ N) (l : ℕ) (Kc : ℝ) (hKc0 : 0 ≤ Kc)
    (hKc : ∀ p q, p ≤ l → q ≤ l → ∀ i j : Idx D N,
      ‖ccum ((ouMatLaw D N L t).map fun h => h i j) p (q + 1)‖ ≤
        Kc * (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2))) :
    ‖∑ i, ∑ j, ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        (if 4 ≤ p + q then FC_f (ouMatLaw D N L t) ch X i j p q else 0)‖ ≤
      (l + 1) ^ 2 * Kc * (2 + l) ^ l * (3 ^ (l + 1) *
        (((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(5 / 2 : ℝ)) * w ^ (ch.length - 1)) +
        ((D : ℝ) * N) ^ 2 * (z.im)⁻¹ ^ (l + 2) * ε) := by
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  have hw0 : 0 ≤ w := by linarith
  have hNp : 0 ≤ (N : ℝ) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN1 : (N : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  set B : ℝ := Kc * (2 + l) ^ l * (3 ^ (l + 1) * ((N : ℝ) ^ (-(5 / 2 : ℝ)) *
    w ^ (ch.length - 1)) + (z.im)⁻¹ ^ (l + 2) * ε) with hB
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ (i j : Idx D N) (p q : ℕ), p < l + 1 → q < l + 1 - p →
      ‖(if 4 ≤ p + q then FC_f (ouMatLaw D N L t) ch X i j p q else 0)‖ ≤ B := by
    intro i j p q hp hq
    split_ifs with h4
    · unfold FC_f
      have h1 := FC_int_pair L t hμ hΛ hz hz1 ch hch hn X hX S ε hε hSc w hw hG p q i j
      rw [norm_mul, norm_mul, norm_div, norm_pow]
      have hfac : (1 : ℝ) ≤ ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ := by
        rw [Complex.norm_natCast]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero p)
          (Nat.factorial_ne_zero q))
      have hc : ‖-(if i = j then (1 / 2 : ℂ) else 1)‖ ^ (p + q) ≤ 1 := by
        rw [norm_neg]
        exact pow_le_one₀ (norm_nonneg _) (by split_ifs <;> norm_num)
      have hN52 : (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) ≤ (N : ℝ) ^ (-(5 / 2 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
        have : (5 : ℝ) ≤ ((p + (q + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 5 ≤ p + (q + 1))
        linarith
      have hK := (hKc p q (by omega) (by omega) i j).trans (mul_le_mul_of_nonneg_left hN52 hKc0)
      have hcount : (((ch.length + p + q) ^ (p + q) : ℕ) : ℝ) ≤ (2 + l) ^ l := by
        have : (ch.length + p + q) ^ (p + q) ≤ (2 + l) ^ l := by
          calc (ch.length + p + q) ^ (p + q) ≤ (2 + l) ^ (p + q) :=
                Nat.pow_le_pow_left (by omega) _
            _ ≤ (2 + l) ^ l := Nat.pow_le_pow_right (by omega) (by omega)
        exact_mod_cast this
      have hp3 : (3 : ℝ) ^ (p + q + 1) ≤ 3 ^ (l + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hpw : (z.im)⁻¹ ^ (p + q + 1) * (z.im)⁻¹ ^ (ch.length - 1) ≤ (z.im)⁻¹ ^ (l + 2) := by
        rw [← pow_add]; exact FC_inv_pow_mono hz hz1 (by omega)
      have hI : ‖∫ h, FC_evalPoly h ch X i j (FC_Dpq ch.length p q) ∂(ouMatLaw D N L t)‖ ≤
          (2 + l) ^ l * (3 ^ (l + 1) * w ^ (ch.length - 1)) + (2 + l) ^ l *
            (z.im)⁻¹ ^ (l + 2) * ε := by
        refine h1.trans ?_
        have hwn : 0 ≤ w ^ (ch.length - 1) := pow_nonneg hw0 _
        gcongr
      calc ‖ccum ((ouMatLaw D N L t).map fun h => h i j) p (q + 1)‖ /
            ‖((p.factorial * q.factorial : ℕ) : ℂ)‖ *
            (‖-(if i = j then (1 / 2 : ℂ) else 1)‖ ^ (p + q) *
              ‖∫ h, FC_evalPoly h ch X i j (FC_Dpq ch.length p q) ∂(ouMatLaw D N L t)‖)
          ≤ (Kc * (N : ℝ) ^ (-(5 / 2 : ℝ))) / 1 * (1 * ((2 + l) ^ l * (3 ^ (l + 1) *
              w ^ (ch.length - 1)) + (2 + l) ^ l * (z.im)⁻¹ ^ (l + 2) * ε)) := by
            gcongr
        _ ≤ B := by
            rw [div_one, one_mul, hB]
            have hwn : 0 ≤ w ^ (ch.length - 1) := pow_nonneg hw0 _
            have hl0 : (0 : ℝ) ≤ (2 + l) ^ l := by positivity
            nlinarith [mul_nonneg hKc0 (mul_nonneg hl0 (mul_nonneg (pow_nonneg hηi (l + 2)) hε)),
              mul_le_mul_of_nonneg_left hN1 (mul_nonneg hKc0 (mul_nonneg hl0
                (mul_nonneg (pow_nonneg hηi (l + 2)) hε)))]
    · rw [norm_zero]; exact hB0
  have hpq : ∀ (i j : Idx D N), ‖∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      (if 4 ≤ p + q then FC_f (ouMatLaw D N L t) ch X i j p q else 0)‖ ≤ (l + 1) ^ 2 * B := by
    intro i j
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p ∈ Finset.range (l + 1), ‖∑ q ∈ Finset.range (l + 1 - p),
          (if 4 ≤ p + q then FC_f (ouMatLaw D N L t) ch X i j p q else 0)‖
        ≤ ∑ _p ∈ Finset.range (l + 1), (l + 1) * B := by
          refine Finset.sum_le_sum fun p hp => (norm_sum_le _ _).trans ?_
          calc ∑ q ∈ Finset.range (l + 1 - p),
                ‖(if 4 ≤ p + q then FC_f (ouMatLaw D N L t) ch X i j p q else 0)‖
              ≤ ∑ _q ∈ Finset.range (l + 1 - p), B := Finset.sum_le_sum fun q hq =>
                hterm i j p q (Finset.mem_range.1 hp) (Finset.mem_range.1 hq)
            _ = (l + 1 - p : ℕ) * B := by simp
            _ ≤ (l + 1) * B := by
                gcongr
                have : ((l + 1 - p : ℕ) : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
                simpa using this
      _ = (l + 1) ^ 2 * B := by simp; ring
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖∑ j, ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        (if 4 ≤ p + q then FC_f (ouMatLaw D N L t) ch X i j p q else 0)‖
      ≤ ∑ _i : Idx D N, ∑ _j : Idx D N, (l + 1) ^ 2 * B :=
        Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hpq i j)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, hB]
        push_cast
        ring

end

section

private theorem FC_norm_add9 (a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℂ) :
    ‖a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9‖ ≤
      ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖a4‖ + ‖a5‖ + ‖a6‖ + ‖a7‖ + ‖a8‖ + ‖a9‖ := by
  calc ‖a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9‖
      ≤ ‖a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8‖ + ‖a9‖ := norm_add_le _ _
    _ ≤ ‖a1 + a2 + a3 + a4 + a5 + a6 + a7‖ + ‖a8‖ + ‖a9‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖a1 + a2 + a3 + a4 + a5 + a6‖ + ‖a7‖ + ‖a8‖ + ‖a9‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖a1 + a2 + a3 + a4 + a5‖ + ‖a6‖ + ‖a7‖ + ‖a8‖ + ‖a9‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖a1 + a2 + a3 + a4‖ + ‖a5‖ + ‖a6‖ + ‖a7‖ + ‖a8‖ + ‖a9‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖a1 + a2 + a3‖ + ‖a4‖ + ‖a5‖ + ‖a6‖ + ‖a7‖ + ‖a8‖ + ‖a9‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖a1 + a2‖ + ‖a3‖ + ‖a4‖ + ‖a5‖ + ‖a6‖ + ‖a7‖ + ‖a8‖ + ‖a9‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_add_le _ _

set_option maxHeartbeats 4000000 in
private theorem FC_core (D : ℕ) (C : ℕ → ℝ) (l k : ℕ) (hl : 3 ≤ l) : ∃ Kc : ℝ, 0 ≤ Kc ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t →
    ∀ (Λ : Matrix (Idx D N) (Idx D N) ℂ), Λ.IsHermitian → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
    ∀ ch : FC_Ch D N, FC_chOK Λ z ch → (ch.length = 1 ∨ ch.length = 2) →
    ∀ X : Matrix (Idx D N) (Idx D N) ℂ, opNorm X ≤ 1 →
    ∀ (S : Set (Idx D N → Idx D N → ℂ)) (ε : ℝ), 0 ≤ ε → ouMatLaw D N L t Sᶜ ≤ ENNReal.ofReal ε →
    ∀ w : ℝ, 1 ≤ w → FC_Good ch X S z.im w → ∀ kk : ℕ, D * N ≤ 2 ^ kk →
      ‖(∑ i, ∑ j, ∫ h, (chainB h ch * X) i j * starRingEnd ℂ (h i j) ∂(ouMatLaw D N L t)) -
          (∑ i, ∑ j, (FC_f (ouMatLaw D N L t) ch X i j 1 0 + FC_f (ouMatLaw D N L t) ch X i j 0 1))
          - FC_lead (ouMatLaw D N L t) ch X‖ ≤
        Kc * FC_err D N ch.length l k kk z.im w ε := by
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  obtain ⟨Kr, hKr0, hKr⟩ := FC_expand l k C'
  choose Kcc hKcc using fun p q => llClass_ccum_le C' p q
  choose Kν hKν using fun p q => ccum_entry_le C p q
  set Kmax : ℝ := ∑ p ∈ Finset.range (l + 3), ∑ q ∈ Finset.range (l + 3), |Kcc p q| with hKmax
  have hKmax0 : 0 ≤ Kmax := by positivity
  have hKmax : ∀ p q, p ≤ l + 2 → q ≤ l + 2 → Kcc p q ≤ Kmax := by
    intro p q hp hq
    have h1 : |Kcc p q| ≤ ∑ q' ∈ Finset.range (l + 3), |Kcc p q'| :=
      Finset.single_le_sum (f := fun q' => |Kcc p q'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have h2 : ∑ q' ∈ Finset.range (l + 3), |Kcc p q'| ≤ Kmax :=
      Finset.single_le_sum (f := fun p' => ∑ q' ∈ Finset.range (l + 3), |Kcc p' q'|)
        (fun _ _ => by positivity) (Finset.mem_range.2 (by omega))
    exact (le_abs_self _).trans (h1.trans h2)
  set K3 : ℝ := |Kν 2 1| + |Kν 1 2| + |Kν 0 3| with hK3
  have hK30 : 0 ≤ K3 := by positivity
  have hK3b : ∀ p q, p + q = 2 → ∀ L : EntryLaws C, ‖ccum (L.νo : Measure ℂ) p (q + 1)‖ ≤ K3 := by
    intro p q hpq L
    have hp : p ≤ 2 := by omega
    interval_cases p
    · obtain rfl : q = 2 := by omega
      exact ((hKν 0 3 L).1.trans (le_abs_self _)).trans (by
        have := abs_nonneg (Kν 2 1); have := abs_nonneg (Kν 1 2); linarith)
    · obtain rfl : q = 1 := by omega
      exact ((hKν 1 2 L).1.trans (le_abs_self _)).trans (by
        have := abs_nonneg (Kν 2 1); have := abs_nonneg (Kν 0 3); linarith)
    · obtain rfl : q = 0 := by omega
      exact ((hKν 2 1 L).1.trans (le_abs_self _)).trans (by
        have := abs_nonneg (Kν 1 2); have := abs_nonneg (Kν 0 3); linarith)
  refine ⟨3 * (16 * (2 * K3) * 36) + 4 * (125 * Kmax * 27) + 7 * (Kmax * 125 * 81) +
      (l + 1) ^ 2 * Kmax * (2 + l) ^ l * 3 ^ (l + 1) +
      (3 * (16 * (2 * K3)) + 4 * (125 * Kmax) + 7 * (Kmax * 125) +
        (l + 1) ^ 2 * Kmax * (2 + l) ^ l) + Kr, by positivity, ?_⟩
  intro N hN L t ht Λ hΛ z hz hz1 ch hch hn X hX S ε hε hSc w hw hG kk hkk
  have hμ := hC' N L t ht
  have hprob := hμ.prob
  set μ := ouMatLaw D N L t with hμdef
  set n := ch.length with hndef
  have hn1 : 1 ≤ n := by omega
  have hchv := FC_chOK_valid hΛ hz hch
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  have hη1 : 1 ≤ (z.im)⁻¹ := one_le_inv₀ hz |>.2 hz1
  have hw0 : 0 ≤ w := by linarith
  have hDN1 : (1 : ℝ) ≤ D * N ∨ D = 0 := by
    rcases Nat.eq_zero_or_pos D with h | h
    · right; exact h
    · left; have : 1 ≤ D * N := Nat.one_le_iff_ne_zero.2 (by positivity); exact_mod_cast this
  have hKc : ∀ p q, p ≤ l + 1 → q ≤ l + 1 → ∀ i j : Idx D N,
      ‖ccum (μ.map fun h => h i j) p (q + 1)‖ ≤
        Kmax * (N : ℝ) ^ (-(((p + (q + 1) : ℕ) : ℝ) / 2)) := by
    intro p q hp hq i j
    refine (hKcc p (q + 1) D N _ μ hμ i j).trans ?_
    exact mul_le_mul_of_nonneg_right (hKmax p (q + 1) (by omega) (by omega))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  set Rem : ℝ := (N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * (z.im)⁻¹) ^ (2 + l + 1) +
      (1 + (z.im)⁻¹) ^ (2 + l + 1) *
        Real.sqrt (0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (z.im / 24)) ^ (-(k : ℝ))) with hRem
  have hRem0 : 0 ≤ Rem := by positivity
  have hpair : ∀ i j : Idx D N,
      ‖(∫ h, (chainB h ch * X) i j * starRingEnd ℂ (h i j) ∂μ) -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), FC_f μ ch X i j p q‖ ≤
        Kr * ((D : ℝ) * N) ^ (n - 1) * Rem := fun i j =>
    hKr D N _ μ hμ Λ hΛ z hz hz1 ch hch hn1 (by omega) X hX i j
  have hdec : ∀ i j : Idx D N,
      ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), FC_f μ ch X i j p q =
        (FC_f μ ch X i j 1 0 + FC_f μ ch X i j 0 1) +
          (FC_f μ ch X i j 2 0 + FC_f μ ch X i j 1 1 + FC_f μ ch X i j 0 2) +
          (FC_f μ ch X i j 3 0 + FC_f μ ch X i j 2 1 + FC_f μ ch X i j 1 2 +
            FC_f μ ch X i j 0 3) +
          ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
            (if 4 ≤ p + q then FC_f μ ch X i j p q else 0) := by
    intro i j
    rw [FC_split l hl]
    have h0 : FC_f μ ch X i j 0 0 = 0 := by
      unfold FC_f; rw [FCe_ccum01 hμ i j]; simp
    rw [h0, zero_add]
  have hoff : ∀ (i j : Idx D N), i ≠ j → ∀ p q : ℕ, FC_f μ ch X i j p q =
      ccum (μ.map fun h => h i j) p (q + 1) / ((p.factorial * q.factorial : ℕ) : ℂ) *
        ((-1) ^ (p + q) * ∫ h, FC_evalPoly h ch X i j (FC_Dpq n p q) ∂μ) := by
    intro i j hij p q
    unfold FC_f; rw [if_neg hij]
  have hD21 := FC_Dpq_inv n hn1 2 1
  set g : FC_Mono → Bool := fun m => FC_offc m == 0
  set P1 := (FC_Dpq n 2 1).filter g
  set P2 := (FC_Dpq n 2 1).filter fun m => !g m
  have hP1i : ∀ m ∈ P1, (∀ f ∈ m, FC_segOK n f.1) ∧ m.length = 2 + 1 + 1 ∧ FC_excess m = n - 1 :=
    fun m hm => hD21.1 m (List.mem_of_mem_filter hm)
  have hP2i : ∀ m ∈ P2, (∀ f ∈ m, FC_segOK n f.1) ∧ 2 ≤ FC_offc m ∧ m.length = 4 ∧
      FC_excess m = n - 1 := by
    intro m hm
    obtain ⟨a1, a2, a3⟩ := hD21.1 m (List.mem_of_mem_filter hm)
    have hg := (List.mem_filter.1 hm).2
    have h21 := FC_struct21 n hn m (List.mem_of_mem_filter hm)
    simp only [g, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hg
    exact ⟨a1, h21.resolve_left hg, by rw [a2], a3⟩
  have hsplit21 : ∀ (i j : Idx D N), i ≠ j → FC_f μ ch X i j 2 1 -
      ccum (μ.map fun h => h i j) 2 (1 + 1) / ((Nat.factorial 2 * Nat.factorial 1 : ℕ) : ℂ) *
        ((-1) ^ (2 + 1) * ∫ h, FC_evalPoly h ch X i j P1 ∂μ) =
      ccum (μ.map fun h => h i j) 2 (1 + 1) / ((Nat.factorial 2 * Nat.factorial 1 : ℕ) : ℂ) *
        ((-1) ^ (2 + 1) * ∫ h, FC_evalPoly h ch X i j P2 ∂μ) := by
    intro i j hij
    rw [hoff i j hij]
    have e : ∫ h, FC_evalPoly h ch X i j (FC_Dpq n 2 1) ∂μ =
        ∫ h, FC_evalPoly h ch X i j P1 ∂μ + ∫ h, FC_evalPoly h ch X i j P2 ∂μ := by
      rw [← integral_add (FC_integrable_poly L t hμ hΛ hz hz1 ch hch hn X hX S ε hε hSc w hw hG
        P1 _ _ hP1i i j)
        (FC_integrable_poly L t hμ hΛ hz hz1 ch hch hn X hX S ε hε hSc w hw hG P2 4 (n - 1)
          (fun m hm => ⟨(hP2i m hm).1, (hP2i m hm).2.2⟩) i j)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun h =>
        FC_evalPoly_filter h ch X i j _ g)
    rw [e]; ring
  have hlead : (∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 2 1 else 0)) - FC_lead μ ch X =
      ∑ i, ∑ j, (if i ≠ j then ccum (μ.map fun h => h i j) 2 (1 + 1) /
        ((Nat.factorial 2 * Nat.factorial 1 : ℕ) : ℂ) *
          ((-1) ^ (2 + 1) * ∫ h, FC_evalPoly h ch X i j P2 ∂μ) else 0) := by
    unfold FC_lead
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i ≠ j
    · rw [if_pos hij, if_pos hij, if_pos hij]
      exact hsplit21 i j hij
    · rw [if_neg hij, if_neg hij, if_neg hij, sub_zero]
  have hoffP : ∀ (p q : ℕ), (∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j p q else 0)) =
      ∑ i, ∑ j, (if i ≠ j then ccum (μ.map fun h => h i j) p (q + 1) /
        ((p.factorial * q.factorial : ℕ) : ℂ) *
          ((-1) ^ (p + q) * ∫ h, FC_evalPoly h ch X i j (FC_Dpq n p q) ∂μ) else 0) := by
    intro p q
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i ≠ j
    · rw [if_pos hij, if_pos hij, hoff i j hij]
    · rw [if_neg hij, if_neg hij]
  have hmain : (∑ i, ∑ j, ∫ h, (chainB h ch * X) i j * starRingEnd ℂ (h i j) ∂μ) -
      (∑ i, ∑ j, (FC_f μ ch X i j 1 0 + FC_f μ ch X i j 0 1)) - FC_lead μ ch X =
      (∑ i, ∑ j, ((∫ h, (chainB h ch * X) i j * starRingEnd ℂ (h i j) ∂μ) -
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), FC_f μ ch X i j p q)) +
      ((∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 2 0 else 0)) + ∑ i, FC_f μ ch X i i 2 0) +
      ((∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 1 1 else 0)) + ∑ i, FC_f μ ch X i i 1 1) +
      ((∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 0 2 else 0)) + ∑ i, FC_f μ ch X i i 0 2) +
      ((∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 3 0 else 0)) + ∑ i, FC_f μ ch X i i 3 0) +
      (((∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 2 1 else 0)) - FC_lead μ ch X) +
        ∑ i, FC_f μ ch X i i 2 1) +
      ((∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 1 2 else 0)) + ∑ i, FC_f μ ch X i i 1 2) +
      ((∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 0 3 else 0)) + ∑ i, FC_f μ ch X i i 0 3) +
      ∑ i, ∑ j, ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        (if 4 ≤ p + q then FC_f μ ch X i j p q else 0) := by
    simp only [← FC_sum_diag_split]
    simp only [Finset.sum_sub_distrib, hdec, Finset.sum_add_distrib]
    rw [FC_sum_diag_split (fun i j => FC_f μ ch X i j 2 1)]
    ring
  rw [hmain]
  set E1 : ℝ := (kk + 2) * (D * N) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ * w ^ (n - 1)
  set E2 : ℝ := (D * N) * (N : ℝ) ^ (-(2 : ℝ)) * (z.im)⁻¹ * w ^ (n - 1)
  set E3 : ℝ := (D * N) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * w ^ (n - 1)
  set E4 : ℝ := ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(5 / 2 : ℝ)) * w ^ (n - 1)
  set E5 : ℝ := ((D : ℝ) * N) ^ 2 * (z.im)⁻¹ ^ (l + 2) * ε
  set E6 : ℝ := ((D : ℝ) * N) ^ 3 * Rem
  have hE : FC_err D N n l k kk z.im w ε = E1 + E2 + E3 + E4 + E5 + E6 := rfl
  have hwn : 0 ≤ w ^ (n - 1) := pow_nonneg hw0 _
  have hE1 : 0 ≤ E1 := by positivity
  have hE2 : 0 ≤ E2 := by positivity
  have hE3 : 0 ≤ E3 := by positivity
  have hE4 : 0 ≤ E4 := by positivity
  have hE5 : 0 ≤ E5 := by positivity
  have hE6 : 0 ≤ E6 := by positivity
  have hDNsq : ((D : ℝ) * N) ≤ ((D : ℝ) * N) ^ 2 := by
    rcases hDN1 with h | h
    · nlinarith
    · subst h; simp
  have hη4 : (z.im)⁻¹ ^ 4 ≤ (z.im)⁻¹ ^ (l + 2) := FC_inv_pow_mono hz hz1 (by omega)
  have hη5 : (z.im)⁻¹ ^ 5 ≤ (z.im)⁻¹ ^ (l + 2) := FC_inv_pow_mono hz hz1 (by omega)
  have hDN2 : (0 : ℝ) ≤ ((D : ℝ) * N) ^ 2 := by positivity
  have hE5a : ((D : ℝ) * N) ^ 2 * (z.im)⁻¹ ^ 4 * ε ≤ E5 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη4 hDN2) hε
  have hE5b : ((D : ℝ) * N) ^ 2 * (z.im)⁻¹ ^ 5 * ε ≤ E5 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη5 hDN2) hε
  have hE5c : (D * N : ℝ) * (z.im)⁻¹ ^ 5 * ε ≤ E5 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDNsq (pow_nonneg hηi 5)) hε).trans
      hE5b
  have hR : ‖∑ i, ∑ j, ((∫ h, (chainB h ch * X) i j * starRingEnd ℂ (h i j) ∂μ) -
      ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), FC_f μ ch X i j p q)‖ ≤
      Kr * E6 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖∑ j, ((∫ h, (chainB h ch * X) i j * starRingEnd ℂ (h i j) ∂μ) -
          ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), FC_f μ ch X i j p q)‖
        ≤ ∑ _i : Idx D N, ∑ _j : Idx D N, Kr * ((D : ℝ) * N) ^ (n - 1) * Rem :=
          Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun j _ => hpair i j)
      _ = Kr * (((D : ℝ) * N) ^ 2 * ((D : ℝ) * N) ^ (n - 1)) * Rem := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
      _ ≤ Kr * ((D : ℝ) * N) ^ 3 * Rem := by
          gcongr
          rw [← pow_add]
          rcases hDN1 with h | h
          · exact pow_le_pow_right₀ h (by omega)
          · subst h; simp
      _ = Kr * E6 := by ring
  have hO2 : ∀ p q, p + q = 2 →
      ‖∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j p q else 0)‖ ≤
        16 * (2 * K3) * 36 * E1 + 16 * (2 * K3) * E5 := by
    intro p q hpq
    have := FC_piece_off2 L t hμ hΛ hz hz1 ch hch hn X hX S ε hε hSc w hw hG hN ht kk hkk p q hpq
      K3 (hK3b p q hpq L)
    have h16 : 0 ≤ 16 * (2 * K3) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hE5a h16]
  have hDg : ∀ p q, 2 ≤ p + q → p + q ≤ 3 → ‖∑ i, FC_f μ ch X i i p q‖ ≤
      Kmax * 125 * 81 * E3 + Kmax * 125 * E5 := by
    intro p q h2 h3
    have := FC_piece_diag L t hμ hΛ hz hz1 ch hch hn X hX S ε hε hSc w hw hG hN p q h2 h3 Kmax
      hKmax0 (hKc p q (by omega) (by omega))
    have h125 : 0 ≤ Kmax * 125 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hE5c h125]
  have hO3 : ∀ p q, p + q = 3 → ¬ (p = 2 ∧ q = 1) →
      ‖∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j p q else 0)‖ ≤
        125 * Kmax * 27 * E2 + 125 * Kmax * E5 := by
    intro p q hpq hne
    rw [hoffP p q]
    have hinv := FC_Dpq_inv n hn1 p q
    have hst := FC_struct3 n hn p q hpq hne
    have hPl : (FC_Dpq n p q).length ≤ 125 := by
      refine hinv.2.trans ?_
      rw [hpq]
      calc (n + p + q) ^ 3 ≤ 5 ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 125 := by norm_num
    have := FC_piece_off3 L t hμ hΛ hz hz1 ch hch hn X hX S ε hε hSc w hw hG hN p q hpq
      (FC_Dpq n p q) (fun m hm => ⟨(hinv.1 m hm).1, hst m hm, by rw [(hinv.1 m hm).2.1, hpq],
        (hinv.1 m hm).2.2⟩) hPl Kmax hKmax0 (hKc p q (by omega) (by omega))
    have h125 : 0 ≤ 125 * Kmax := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hE5b h125]
  have hO21 : ‖(∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 2 1 else 0)) - FC_lead μ ch X‖ ≤
      125 * Kmax * 27 * E2 + 125 * Kmax * E5 := by
    rw [hlead]
    have hPl : P2.length ≤ 125 := by
      refine (List.length_filter_le _ _).trans (hD21.2.trans ?_)
      calc (n + 2 + 1) ^ (2 + 1) ≤ 5 ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 125 := by norm_num
    have := FC_piece_off3 L t hμ hΛ hz hz1 ch hch hn X hX S ε hε hSc w hw hG hN 2 1 rfl P2 hP2i
      hPl Kmax hKmax0 (hKc 2 1 (by omega) (by omega))
    have h125 : 0 ≤ 125 * Kmax := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hE5b h125]
  have hHi := FC_piece_high L t hμ hΛ hz hz1 ch hch hn X hX S ε hε hSc w hw hG hN l Kmax hKmax0
    (fun p q hp hq => hKc p q (by omega) (by omega))
  have b1 := hO2 2 0 rfl
  have b2 := hO2 1 1 rfl
  have b3 := hO2 0 2 rfl
  have b4 := hDg 2 0 (by norm_num) (by norm_num)
  have b5 := hDg 1 1 (by norm_num) (by norm_num)
  have b6 := hDg 0 2 (by norm_num) (by norm_num)
  have b7 := hO3 3 0 rfl (by omega)
  have b8 := hDg 3 0 (by norm_num) (by norm_num)
  have b9 := hDg 2 1 (by norm_num) (by norm_num)
  have b10 := hO3 1 2 rfl (by omega)
  have b11 := hDg 1 2 (by norm_num) (by norm_num)
  have b12 := hO3 0 3 rfl (by omega)
  have b13 := hDg 0 3 (by norm_num) (by norm_num)
  rw [hE]
  have hl0 : (0 : ℝ) ≤ (l + 1) ^ 2 * Kmax * (2 + l) ^ l := by positivity
  have hHi' : ‖∑ i, ∑ j, ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      (if 4 ≤ p + q then FC_f μ ch X i j p q else 0)‖ ≤
      (l + 1) ^ 2 * Kmax * (2 + l) ^ l * 3 ^ (l + 1) * E4 +
        (l + 1) ^ 2 * Kmax * (2 + l) ^ l * E5 := by
    refine hHi.trans (le_of_eq ?_); ring
  refine (FC_norm_add9 _ _ _ _ _ _ _ _ _).trans ?_
  have n1 := norm_add_le (∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 2 0 else 0))
    (∑ i, FC_f μ ch X i i 2 0)
  have n2 := norm_add_le (∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 1 1 else 0))
    (∑ i, FC_f μ ch X i i 1 1)
  have n3 := norm_add_le (∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 0 2 else 0))
    (∑ i, FC_f μ ch X i i 0 2)
  have n4 := norm_add_le (∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 3 0 else 0))
    (∑ i, FC_f μ ch X i i 3 0)
  have n5 := norm_add_le ((∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 2 1 else 0)) -
    FC_lead μ ch X) (∑ i, FC_f μ ch X i i 2 1)
  have n6 := norm_add_le (∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 1 2 else 0))
    (∑ i, FC_f μ ch X i i 1 2)
  have n7 := norm_add_le (∑ i, ∑ j, (if i ≠ j then FC_f μ ch X i j 0 3 else 0))
    (∑ i, FC_f μ ch X i i 0 3)
  set KK := (3 * (16 * (2 * K3) * 36) + 4 * (125 * Kmax * 27) +
      7 * (Kmax * 125 * 81) + (l + 1) ^ 2 * Kmax * (2 + l) ^ l * 3 ^ (l + 1) +
      (3 * (16 * (2 * K3)) + 4 * (125 * Kmax) + 7 * (Kmax * 125) +
        (l + 1) ^ 2 * Kmax * (2 + l) ^ l) + Kr) with hKK
  have a1 : 0 ≤ 3 * (16 * (2 * K3) * 36) := by positivity
  have a2 : 0 ≤ 4 * (125 * Kmax * 27) := by positivity
  have a3 : 0 ≤ 7 * (Kmax * 125 * 81) := by positivity
  have a4 : 0 ≤ (l + 1 : ℝ) ^ 2 * Kmax * (2 + l) ^ l * 3 ^ (l + 1) := by positivity
  have a5 : 0 ≤ 3 * (16 * (2 * K3)) + 4 * (125 * Kmax) + 7 * (Kmax * 125) +
      (l + 1) ^ 2 * Kmax * (2 + l) ^ l := by positivity
  have k1 : 3 * (16 * (2 * K3) * 36) ≤ KK := by rw [hKK]; linarith
  have k2 : 4 * (125 * Kmax * 27) ≤ KK := by rw [hKK]; linarith
  have k3 : 7 * (Kmax * 125 * 81) ≤ KK := by rw [hKK]; linarith
  have k4 : (l + 1 : ℝ) ^ 2 * Kmax * (2 + l) ^ l * 3 ^ (l + 1) ≤ KK := by rw [hKK]; linarith
  have k5 : 3 * (16 * (2 * K3)) + 4 * (125 * Kmax) + 7 * (Kmax * 125) +
      (l + 1) ^ 2 * Kmax * (2 + l) ^ l ≤ KK := by rw [hKK]; linarith
  have k6 : Kr ≤ KK := by rw [hKK]; linarith
  have m1 := mul_le_mul_of_nonneg_right k1 hE1
  have m2 := mul_le_mul_of_nonneg_right k2 hE2
  have m3 := mul_le_mul_of_nonneg_right k3 hE3
  have m4 := mul_le_mul_of_nonneg_right k4 hE4
  have m5 := mul_le_mul_of_nonneg_right k5 hE5
  have m6 := mul_le_mul_of_nonneg_right k6 hE6
  have hfinal : KK * (E1 + E2 + E3 + E4 + E5 + E6) = KK * E1 + KK * E2 + KK * E3 + KK * E4 +
      KK * E5 + KK * E6 := by ring
  rw [hfinal]
  linarith [n1, n2, n3, n4, n5, n6, n7, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13,
    hR, hO21, hHi', m1, m2, m3, m4, m5, m6]

end

section

section FC_ward
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem FC_ward_col (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (ξ : ℂ)
    (hξ : ξ = z ∨ ξ = star z) (a b : ι) :
    ∑ x, starRingEnd ℂ (res X ξ x a) * res X ξ x b =
      (res X ξ a b - starRingEnd ℂ (res X ξ b a)) / (2 * Complex.I * ξ.im) := by
  rcases hξ with rfl | rfl
  · exact (ward_sum X hX ξ hz b a).1
  · have hc : res X (star z) = (res X z)ᴴ := res_conj X hX z hz
    rw [hc]
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_conj]
    have h2 := (ward_sum X hX z hz b a).2
    have e : ∑ x, res X z a x * starRingEnd ℂ (res X z b x) =
        starRingEnd ℂ (∑ x, starRingEnd ℂ (res X z a x) * res X z b x) := by
      rw [map_sum]; exact Finset.sum_congr rfl fun x _ => by simp [mul_comm]
    rw [e, h2]
    simp only [Complex.star_def, Complex.conj_im, map_div₀, map_sub, map_mul, Complex.conj_I,
      Complex.conj_conj, Complex.conj_ofReal, map_ofNat]
    push_cast
    have hη : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz.ne'
    field_simp

private theorem FC_ward_row (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (ξ : ℂ)
    (hξ : ξ = z ∨ ξ = star z) (a b : ι) :
    ∑ x, starRingEnd ℂ (res X ξ a x) * res X ξ b x =
      (res X ξ b a - starRingEnd ℂ (res X ξ a b)) / (2 * Complex.I * ξ.im) := by
  rcases hξ with rfl | rfl
  · exact (ward_sum X hX ξ hz b a).2
  · have hc : res X (star z) = (res X z)ᴴ := res_conj X hX z hz
    rw [hc]
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_conj]
    have h1 := (ward_sum X hX z hz b a).1
    have e : ∑ x, res X z x a * starRingEnd ℂ (res X z x b) =
        starRingEnd ℂ (∑ x, starRingEnd ℂ (res X z x a) * res X z x b) := by
      rw [map_sum]; exact Finset.sum_congr rfl fun x _ => by simp [mul_comm]
    rw [e, h1]
    simp only [Complex.star_def, Complex.conj_im, map_div₀, map_sub, map_mul, Complex.conj_I,
      Complex.conj_conj, Complex.conj_ofReal, map_ofNat]
    push_cast
    have hη : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz.ne'
    field_simp

private theorem FC_im_div_le (w : ℂ) (r : ℝ) (hr : r ≠ 0) :
    ‖(w - starRingEnd ℂ w) / (2 * Complex.I * r)‖ ≤ ‖w‖ / |r| := by
  have h1 : ‖w - starRingEnd ℂ w‖ ≤ 2 * ‖w‖ :=
    (norm_sub_le _ _).trans (by rw [Complex.norm_conj]; linarith)
  have h2 : ‖2 * Complex.I * (r : ℂ)‖ = 2 * |r| := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]; norm_num
  have hr' : 0 < |r| := abs_pos.2 hr
  rw [norm_div, h2, div_le_div_iff₀ (by positivity) hr']
  nlinarith [norm_nonneg w]

private theorem FC_sum_conj_mul {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ∑ x, starRingEnd ℂ (f x) * f x = ((∑ x, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  exact Finset.sum_congr rfl fun x _ => Complex.conj_mul' (f x)

private theorem FC_norm_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ‖∑ x, starRingEnd ℂ (f x) * f x‖ = ∑ x, ‖f x‖ ^ 2 := by
  rw [FC_sum_conj_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private theorem FC_col_sq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (ξ : ℂ)
    (hξ : ξ = z ∨ ξ = star z) (a : ι) :
    ∑ x, ‖res X ξ x a‖ ^ 2 ≤ ‖res X ξ a a‖ / z.im := by
  have hξi : |ξ.im| = z.im := by
    rcases hξ with rfl | rfl
    · exact abs_of_pos hz
    · simp [abs_of_pos hz]
  have h := FC_ward_col X hX z hz ξ hξ a a
  rw [← FC_norm_sum_sq (fun x => res X ξ x a), h]
  have hne : ξ.im ≠ 0 := by rw [← abs_pos, hξi]; exact hz
  exact (FC_im_div_le _ _ hne).trans (le_of_eq (by rw [hξi]))

private theorem FC_row_sq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (ξ : ℂ)
    (hξ : ξ = z ∨ ξ = star z) (a : ι) :
    ∑ x, ‖res X ξ a x‖ ^ 2 ≤ ‖res X ξ a a‖ / z.im := by
  have hξi : |ξ.im| = z.im := by
    rcases hξ with rfl | rfl
    · exact abs_of_pos hz
    · simp [abs_of_pos hz]
  have h := FC_ward_row X hX z hz ξ hξ a a
  rw [← FC_norm_sum_sq (fun x => res X ξ a x), h]
  have hne : ξ.im ≠ 0 := by rw [← abs_pos, hξi]; exact hz
  exact (FC_im_div_le _ _ hne).trans (le_of_eq (by rw [hξi]))

private theorem FC_vec_sq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (ξ : ℂ)
    (hξ : ξ = z ∨ ξ = star z) (v : ι → ℂ) :
    ∑ x, ‖(res X ξ *ᵥ v) x‖ ^ 2 ≤ ‖star v ⬝ᵥ (res X ξ *ᵥ v)‖ / z.im := by
  have hξi : |ξ.im| = z.im := by
    rcases hξ with rfl | rfl
    · exact abs_of_pos hz
    · simp [abs_of_pos hz]
  set G := res X ξ
  have e1 : ∑ x, starRingEnd ℂ ((G *ᵥ v) x) * (G *ᵥ v) x =
      ∑ a, ∑ b, starRingEnd ℂ (v a) * v b * ∑ x, starRingEnd ℂ (G x a) * G x b := by
    have hl : ∀ x, starRingEnd ℂ ((G *ᵥ v) x) * (G *ᵥ v) x =
        ∑ a, ∑ b, starRingEnd ℂ (v a) * v b * (starRingEnd ℂ (G x a) * G x b) := by
      intro x
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp only [hl, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hA : star v ⬝ᵥ (G *ᵥ v) = ∑ a, ∑ b, starRingEnd ℂ (v a) * v b * G a b := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hB : starRingEnd ℂ (star v ⬝ᵥ (G *ᵥ v)) =
      ∑ a, ∑ b, starRingEnd ℂ (v a) * v b * starRingEnd ℂ (G b a) := by
    rw [hA, map_sum]
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have e2 : ∑ a, ∑ b, starRingEnd ℂ (v a) * v b * ∑ x, starRingEnd ℂ (G x a) * G x b =
      (star v ⬝ᵥ (G *ᵥ v) - starRingEnd ℂ (star v ⬝ᵥ (G *ᵥ v))) / (2 * Complex.I * ξ.im) := by
    rw [hB, hA, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [FC_ward_col X hX z hz ξ hξ a b]
    ring
  have hne : ξ.im ≠ 0 := by rw [← abs_pos, hξi]; exact hz
  have h := FC_im_div_le (star v ⬝ᵥ (G *ᵥ v)) ξ.im hne
  rw [← e2, ← e1, FC_norm_sum_sq (fun x => (G *ᵥ v) x), hξi] at h
  exact h

end FC_ward

end

section

section FC_det
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def FC_col (X : Matrix ι ι ℂ) (y : ι) : ι → ℂ := fun γ => X γ y

private def FC_iso (G M X : Matrix ι ι ℂ) (δ : ℝ) : Prop :=
  (∀ x y, ‖G x y - M x y‖ ≤ δ) ∧ (∀ x y, ‖(G * X) x y - (M * X) x y‖ ≤ δ) ∧
    ∀ y, ‖star (FC_col X y) ⬝ᵥ ((G - M) *ᵥ FC_col X y)‖ ≤ δ

private theorem FC_col_norm (X : Matrix ι ι ℂ) (y : ι) : ∑ γ, ‖FC_col X y γ‖ ^ 2 ≤ opNorm X ^ 2 := by
  have h := FC_mulVec_sq_le X (Pi.single y 1)
  have e1 : ∀ γ, (X *ᵥ Pi.single y 1) γ = X γ y := fun γ => by simp [Matrix.mulVec_single]
  have e2 : ∑ k, ‖(Pi.single y (1 : ℂ) : ι → ℂ) k‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  simp only [e1, e2, mul_one] at h
  exact h

private theorem FC_entry_mul_le (A B : Matrix ι ι ℂ) (x y : ι) :
    ‖(A * B) x y‖ ≤ Real.sqrt (∑ γ, ‖A x γ‖ ^ 2) * Real.sqrt (∑ γ, ‖B γ y‖ ^ 2) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

private theorem FC_hs_mul_le (A B : Matrix ι ι ℂ) :
    ∑ x, ∑ y, ‖(A * B) x y‖ ^ 2 ≤ opNorm A ^ 2 * ∑ x, ∑ y, ‖B x y‖ ^ 2 := by
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => ‖B x y‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have h := FC_mulVec_sq_le A (FC_col B y)
  have e : ∀ x, (A *ᵥ FC_col B y) x = (A * B) x y := fun x => by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, FC_col]
  simp only [e] at h
  exact h

private theorem FC_iso_bounds (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (ξ : ℂ) (hξ : ξ = z ∨ ξ = star z) (M X : Matrix ι ι ℂ) (hM : opNorm M ≤ 5 / 4)
    (hX : opNorm X ≤ 1) (δ : ℝ) (hδ : δ ≤ 1) (hiso : FC_iso (res H ξ) M X δ) :
    (∀ x y, ‖res H ξ x y‖ ≤ 3) ∧ (∀ x y, ‖(res H ξ * X) x y‖ ≤ 3) ∧
      (∀ a, ∑ x, ‖res H ξ x a‖ ^ 2 ≤ 3 / z.im) ∧ (∀ a, ∑ x, ‖res H ξ a x‖ ^ 2 ≤ 3 / z.im) ∧
      (∀ y, ∑ x, ‖(res H ξ * X) x y‖ ^ 2 ≤ 3 / z.im) ∧ opNorm (res H ξ) ≤ (z.im)⁻¹ := by
  have hres := FC_opNorm_res H hH z hz ξ hξ
  have hcol := FC_col_sq H hH z hz ξ hξ
  have hrow := FC_row_sq H hH z hz ξ hξ
  have hvec := FC_vec_sq H hH z hz ξ hξ
  generalize res H ξ = G at hiso hres hcol hrow hvec ⊢
  obtain ⟨h1, h2, h3⟩ := hiso
  have hX0 : 0 ≤ opNorm X := FC_opNorm_nonneg X
  have hM0 : 0 ≤ opNorm M := FC_opNorm_nonneg M
  have he : ∀ x y, ‖G x y‖ ≤ 3 := by
    intro x y
    have := norm_apply_le_opNorm M x y
    calc ‖G x y‖ = ‖(G x y - M x y) + M x y‖ := by rw [sub_add_cancel]
      _ ≤ ‖G x y - M x y‖ + ‖M x y‖ := norm_add_le _ _
      _ ≤ 3 := by linarith [h1 x y]
  have hMX : opNorm (M * X) ≤ 5 / 4 := (opNorm_mul_le M X).trans (by nlinarith)
  have hex : ∀ x y, ‖(G * X) x y‖ ≤ 3 := by
    intro x y
    have := norm_apply_le_opNorm (M * X) x y
    calc ‖(G * X) x y‖ = ‖((G * X) x y - (M * X) x y) + (M * X) x y‖ := by rw [sub_add_cancel]
      _ ≤ ‖(G * X) x y - (M * X) x y‖ + ‖(M * X) x y‖ := norm_add_le _ _
      _ ≤ 3 := by linarith [h2 x y]
  have hη : 0 < z.im := hz
  refine ⟨he, hex, fun a => ?_, fun a => ?_, fun y => ?_, hres⟩
  · refine (hcol a).trans ?_
    exact div_le_div_of_nonneg_right (he a a) hz.le
  · refine (hrow a).trans ?_
    exact div_le_div_of_nonneg_right (he a a) hz.le
  · have hv := hvec (FC_col X y)
    have e : ∀ x, (G *ᵥ FC_col X y) x = (G * X) x y := fun x => by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, FC_col]
    simp only [e] at hv
    refine hv.trans (div_le_div_of_nonneg_right ?_ hz.le)
    have hc := FC_col_norm X y
    have hc1 : Real.sqrt (∑ k, ‖FC_col X y k‖ ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]; nlinarith
    have hMv := FC_form_le M (FC_col X y) (FC_col X y)
    have hsplit : star (FC_col X y) ⬝ᵥ (G *ᵥ FC_col X y) =
        star (FC_col X y) ⬝ᵥ ((G - M) *ᵥ FC_col X y) +
          star (FC_col X y) ⬝ᵥ (M *ᵥ FC_col X y) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]; ring
    rw [hsplit]
    have hs0 := Real.sqrt_nonneg (∑ k, ‖FC_col X y k‖ ^ 2)
    calc _ ≤ ‖star (FC_col X y) ⬝ᵥ ((G - M) *ᵥ FC_col X y)‖ +
          ‖star (FC_col X y) ⬝ᵥ (M *ᵥ FC_col X y)‖ := norm_add_le _ _
      _ ≤ 1 + 5 / 4 * 1 * 1 := by
          gcongr
          · exact (h3 y).trans hδ
          · calc _ ≤ _ := hMv
              _ ≤ 5 / 4 * 1 * 1 := by gcongr
      _ ≤ 3 := by norm_num

end FC_det

private theorem FC_seg1 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (ξ : ℂ) (X : Matrix (Idx D N) (Idx D N) ℂ) (o x : Bool) :
    FC_evalSeg h [(1, Λ, ξ)] X (0, 1, o, x) =
      res (Matrix.of h + Λ) ξ * (if x then X else 1) := by
  cases o <;> simp [FC_evalSeg, FC_segList, FC_mod, chainB]

private theorem FC_seg2a {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (Λ E : Matrix (Idx D N) (Idx D N) ℂ)
    (ξ₁ ξ₂ : ℂ) (X : Matrix (Idx D N) (Idx D N) ℂ) (o : Bool) :
    FC_evalSeg h [(1, Λ, ξ₂), (E, Λ, ξ₁)] X (0, 1, o, false) = res (Matrix.of h + Λ) ξ₂ := by
  cases o <;> simp [FC_evalSeg, FC_segList, FC_mod, chainB]

private theorem FC_seg2b {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (Λ E : Matrix (Idx D N) (Idx D N) ℂ)
    (ξ₁ ξ₂ : ℂ) (X : Matrix (Idx D N) (Idx D N) ℂ) (o x : Bool) :
    FC_evalSeg h [(1, Λ, ξ₂), (E, Λ, ξ₁)] X (0, 2, o, x) =
      res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ * (if x then X else 1))) := by
  cases o <;> simp [FC_evalSeg, FC_segList, FC_mod, chainB, Matrix.mul_assoc]

private theorem FC_seg2c {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (Λ E : Matrix (Idx D N) (Idx D N) ℂ)
    (ξ₁ ξ₂ : ℂ) (X : Matrix (Idx D N) (Idx D N) ℂ) (x : Bool) :
    FC_evalSeg h [(1, Λ, ξ₂), (E, Λ, ξ₁)] X (1, 2, true, x) =
      res (Matrix.of h + Λ) ξ₁ * (if x then X else 1) := by
  simp [FC_evalSeg, FC_segList, FC_mod, chainB]

private theorem FC_segOK1 (s : FC_Seg) (hs : FC_segOK 1 s) : s.1 = 0 ∧ s.2.1 = 1 := by
  obtain ⟨a, b, o, x⟩ := s
  obtain ⟨h1, h2, -, -⟩ := hs
  simp only at h1 h2 ⊢; omega

private theorem FC_segOK2 (s : FC_Seg) (hs : FC_segOK 2 s) :
    (s.1 = 0 ∧ s.2.1 = 1 ∧ s.2.2.2 = false) ∨ (s.1 = 0 ∧ s.2.1 = 2) ∨
      (s.1 = 1 ∧ s.2.1 = 2 ∧ s.2.2.1 = true) := by
  obtain ⟨a, b, o, x⟩ := s
  obtain ⟨h1, h2, h3, h4⟩ := hs
  simp only at h1 h2 h3 h4 ⊢
  have : (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) := by omega
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; refine ⟨rfl, rfl, ?_⟩
    cases x
    · rfl
    · exact absurd (h3 rfl) (by norm_num)
  · right; left; exact ⟨rfl, rfl⟩
  · right; right; exact ⟨rfl, rfl, h4 (by norm_num)⟩

private theorem FC_card_idx (D N : ℕ) : (Fintype.card (Idx D N) : ℝ) = D * N := by simp

private theorem FC_good_GY {D N : ℕ} (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (ξ : ℂ) (hξ : ξ = z ∨ ξ = star z) (M X : Matrix (Idx D N) (Idx D N) ℂ)
    (hM : opNorm M ≤ 5 / 4) (hX : opNorm X ≤ 1) (δ : ℝ) (hδ : δ ≤ 1)
    (hiso : FC_iso (res H ξ) M X δ) (x : Bool) :
    (∀ a b, ‖(res H ξ * (if x then X else 1)) a b‖ ≤ 3) ∧
      ∑ a, ∑ b, ‖(res H ξ * (if x then X else 1)) a b‖ ^ 2 ≤ 3 * D * N / z.im ∧
      (∀ b, ∑ a, ‖(res H ξ * (if x then X else 1)) a b‖ ^ 2 ≤ 3 / z.im) ∧
      opNorm (res H ξ * (if x then X else 1)) ≤ (z.im)⁻¹ := by
  obtain ⟨b1, b2, b3, -, b5, b6⟩ := FC_iso_bounds H hH z hz ξ hξ M X hM hX δ hδ hiso
  have hY : opNorm (if x then X else 1) ≤ 1 := by
    split_ifs
    · exact hX
    · exact FC_opNorm_one
  have hcol : ∀ b, ∑ a, ‖(res H ξ * (if x then X else 1)) a b‖ ^ 2 ≤ 3 / z.im := by
    intro b
    cases x
    · simpa using b3 b
    · simpa using b5 b
  refine ⟨fun a b => ?_, ?_, hcol, ?_⟩
  · cases x
    · simpa using b1 a b
    · simpa using b2 a b
  · rw [Finset.sum_comm]
    calc ∑ b, ∑ a, ‖(res H ξ * (if x then X else 1)) a b‖ ^ 2 ≤ ∑ _b : Idx D N, 3 / z.im :=
          Finset.sum_le_sum fun b _ => hcol b
      _ = 3 * D * N / z.im := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, FC_card_idx]; ring
  · refine (opNorm_mul_le _ _).trans ?_
    calc opNorm (res H ξ) * opNorm (if x then X else 1) ≤ (z.im)⁻¹ * 1 :=
          mul_le_mul b6 hY (FC_opNorm_nonneg _) (inv_nonneg.2 hz.le)
      _ = _ := by ring

private theorem FC_good_one {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (ξ : ℂ) (hξ : ξ = z ∨ ξ = star z)
    (M X : Matrix (Idx D N) (Idx D N) ℂ) (hM : opNorm M ≤ 5 / 4) (hX : opNorm X ≤ 1)
    (δ : ℝ) (hδ : δ ≤ 1) (S : Set (Idx D N → Idx D N → ℂ))
    (hS : ∀ h ∈ S, (Matrix.of h).IsHermitian → FC_iso (res (Matrix.of h + Λ) ξ) M X δ)
    (w : ℝ) : FC_Good [(1, Λ, ξ)] X S z.im w := by
  have hη : 0 < z.im := hz
  have key : ∀ h ∈ S, (Matrix.of h).IsHermitian → ∀ s, FC_segOK 1 s →
      (∀ a b, ‖FC_evalSeg h [(1, Λ, ξ)] X s a b‖ ≤ 3) ∧
      ∑ a, ∑ b, ‖FC_evalSeg h [(1, Λ, ξ)] X s a b‖ ^ 2 ≤ 3 * D * N / z.im ∧
      opNorm (FC_evalSeg h [(1, Λ, ξ)] X s) ≤ (z.im)⁻¹ := by
    intro h hS' hh s hs
    obtain ⟨a, b, o, x⟩ := s
    obtain ⟨ha, hb⟩ := FC_segOK1 _ hs
    simp only at ha hb
    subst ha hb
    rw [FC_seg1]
    obtain ⟨g1, g2, -, g4⟩ := FC_good_GY _ (hh.add hΛ) z hz ξ hξ M X hM hX δ hδ
      (hS h hS' hh) x
    exact ⟨g1, g2, g4⟩
  refine ⟨fun h hS' hh s hs x y => ?_, fun h hS' hh s hs => ?_, fun h hS' hh s hs => ?_⟩
  · have hs1 := FC_segOK1 s hs
    rw [show s.2.1 - s.1 - 1 = 0 by omega, pow_zero, mul_one]
    exact (key h hS' hh s hs).1 x y
  · have hs1 := FC_segOK1 s hs
    rw [show s.2.1 - s.1 - 1 = 0 by omega, pow_zero, mul_one,
      Real.sq_sqrt (by positivity)]
    exact (key h hS' hh s hs).2.1
  · have hs1 := FC_segOK1 s hs
    rw [show s.2.1 - s.1 - 1 = 0 by omega, pow_zero, mul_one]
    refine (key h hS' hh s hs).2.2.trans ?_
    rw [div_eq_mul_inv]
    have := inv_nonneg.2 hz.le
    linarith

private theorem FC_col_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] (E B : Matrix ι ι ℂ) (b : ι) :
    ∑ γ, ‖(E * B) γ b‖ ^ 2 ≤ opNorm E ^ 2 * ∑ γ, ‖B γ b‖ ^ 2 := by
  have h := FC_mulVec_sq_le E (FC_col B b)
  have e : ∀ γ, (E *ᵥ FC_col B b) γ = (E * B) γ b := fun γ => by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, FC_col]
  simp only [e] at h
  simpa [FC_col] using h

private theorem FC_good_two {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (hz1 : z.im ≤ 1) (ξ₁ ξ₂ : ℂ) (h₁ : ξ₁ = z ∨ ξ₁ = star z)
    (h₂ : ξ₂ = z ∨ ξ₂ = star z) (E : Matrix (Idx D N) (Idx D N) ℂ) (hE : opNorm E ≤ 1)
    (M₁ M₂ X : Matrix (Idx D N) (Idx D N) ℂ) (hM₁ : opNorm M₁ ≤ 5 / 4)
    (hM₂ : opNorm M₂ ≤ 5 / 4) (hX : opNorm X ≤ 1)
    (δ : ℝ) (hδ : δ ≤ 1) (S : Set (Idx D N → Idx D N → ℂ))
    (hS : ∀ h ∈ S, (Matrix.of h).IsHermitian → FC_iso (res (Matrix.of h + Λ) ξ₁) M₁ X δ ∧
      FC_iso (res (Matrix.of h + Λ) ξ₂) M₂ X δ) :
    FC_Good [(1, Λ, ξ₂), (E, Λ, ξ₁)] X S z.im (z.im)⁻¹ := by
  have hη : 0 < z.im := hz
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  have hE0 := FC_opNorm_nonneg E
  have hlong : ∀ h ∈ S, (Matrix.of h).IsHermitian → ∀ x : Bool,
      (∀ a b, ‖(res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ *
        (if x then X else 1)))) a b‖ ≤ 3 * (z.im)⁻¹) ∧
      ∑ a, ∑ b, ‖(res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ *
        (if x then X else 1)))) a b‖ ^ 2 ≤ (Real.sqrt (3 * D * N / z.im) * (z.im)⁻¹) ^ 2 ∧
      opNorm (res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ *
        (if x then X else 1)))) ≤ 3 / z.im * (z.im)⁻¹ := by
    intro h hS' hh x
    have hH := hh.add hΛ
    obtain ⟨i1, i2⟩ := hS h hS' hh
    obtain ⟨g1, g2, g3, g4⟩ := FC_good_GY _ hH z hz ξ₁ h₁ M₁ X hM₁ hX δ hδ i1 x
    obtain ⟨-, -, -, r2, -, r6⟩ := FC_iso_bounds _ hH z hz ξ₂ h₂ M₂ X hM₂ hX δ hδ i2
    set G₁ := res (Matrix.of h + Λ) ξ₁
    set G₂ := res (Matrix.of h + Λ) ξ₂
    set Y : Matrix (Idx D N) (Idx D N) ℂ := if x then X else 1
    have hT : ∀ b, ∑ γ, ‖(E * (G₁ * Y)) γ b‖ ^ 2 ≤ 3 / z.im := by
      intro b
      refine (FC_col_mul_le E (G₁ * Y) b).trans ?_
      have := g3 b
      have hE2 : opNorm E ^ 2 ≤ 1 := by nlinarith
      have h0 : 0 ≤ ∑ γ, ‖(G₁ * Y) γ b‖ ^ 2 := by positivity
      nlinarith
    refine ⟨fun a b => ?_, ?_, ?_⟩
    · refine (FC_entry_mul_le G₂ (E * (G₁ * Y)) a b).trans ?_
      have hs1 := Real.sqrt_le_sqrt (r2 a)
      have hs2 := Real.sqrt_le_sqrt (hT b)
      have hsq : Real.sqrt (3 / z.im) * Real.sqrt (3 / z.im) = 3 / z.im :=
        Real.mul_self_sqrt (by positivity)
      calc _ ≤ Real.sqrt (3 / z.im) * Real.sqrt (3 / z.im) :=
            mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = 3 * (z.im)⁻¹ := by rw [hsq]; ring
    · refine (FC_hs_mul_le G₂ (E * (G₁ * Y))).trans ?_
      have hHS : ∑ a, ∑ b, ‖(E * (G₁ * Y)) a b‖ ^ 2 ≤ 3 * D * N / z.im := by
        refine (FC_hs_mul_le E (G₁ * Y)).trans ?_
        have hE2 : opNorm E ^ 2 ≤ 1 := by nlinarith
        have h0 : 0 ≤ ∑ a, ∑ b, ‖(G₁ * Y) a b‖ ^ 2 := by positivity
        nlinarith
      have hG2 : opNorm G₂ ^ 2 ≤ ((z.im)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (FC_opNorm_nonneg _) r6 2
      have h0 : 0 ≤ ∑ a, ∑ b, ‖(E * (G₁ * Y)) a b‖ ^ 2 := by positivity
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      calc opNorm G₂ ^ 2 * ∑ a, ∑ b, ‖(E * (G₁ * Y)) a b‖ ^ 2
          ≤ ((z.im)⁻¹) ^ 2 * (3 * D * N / z.im) :=
            mul_le_mul hG2 hHS h0 (by positivity)
        _ = _ := by ring
    · refine (opNorm_mul_le _ _).trans ?_
      have h1 := (opNorm_mul_le E (G₁ * Y)).trans (mul_le_mul hE g4 (FC_opNorm_nonneg _)
        zero_le_one)
      calc opNorm G₂ * opNorm (E * (G₁ * Y)) ≤ (z.im)⁻¹ * (1 * (z.im)⁻¹) :=
            mul_le_mul r6 h1 (FC_opNorm_nonneg _) hηi
        _ ≤ 3 / z.im * (z.im)⁻¹ := by
            rw [div_eq_mul_inv]; nlinarith [mul_nonneg hηi hηi]
  have hshort : ∀ h ∈ S, (Matrix.of h).IsHermitian → ∀ (ξ : ℂ), (ξ = z ∨ ξ = star z) →
      ∀ M : Matrix (Idx D N) (Idx D N) ℂ, opNorm M ≤ 5 / 4 →
      FC_iso (res (Matrix.of h + Λ) ξ) M X δ → ∀ x : Bool,
      (∀ a b, ‖(res (Matrix.of h + Λ) ξ * (if x then X else 1)) a b‖ ≤ 3) ∧
      ∑ a, ∑ b, ‖(res (Matrix.of h + Λ) ξ * (if x then X else 1)) a b‖ ^ 2 ≤
        3 * D * N / z.im ∧ opNorm (res (Matrix.of h + Λ) ξ * (if x then X else 1)) ≤ 3 / z.im := by
    intro h hS' hh ξ hξ M hM hi x
    obtain ⟨g1, g2, -, g4⟩ := FC_good_GY _ (hh.add hΛ) z hz ξ hξ M X hM hX δ hδ hi x
    refine ⟨g1, g2, g4.trans ?_⟩
    rw [div_eq_mul_inv]; linarith
  refine ⟨fun h hS' hh s hs x y => ?_, fun h hS' hh s hs => ?_, fun h hS' hh s hs => ?_⟩
  all_goals
    obtain ⟨a, b, o, xx⟩ := s
    rcases FC_segOK2 _ hs with ⟨ha, hb, hx⟩ | ⟨ha, hb⟩ | ⟨ha, hb, ho⟩ <;>
      simp only at ha hb <;> subst ha hb
  · simp only at hx; subst hx
    rw [FC_seg2a]
    have := (hshort h hS' hh ξ₂ h₂ M₂ hM₂ (hS h hS' hh).2 false).1 x y
    simpa using this
  · rw [FC_seg2b]
    simpa using (hlong h hS' hh xx).1 x y
  · simp only at ho; subst ho
    rw [FC_seg2c]
    simpa using (hshort h hS' hh ξ₁ h₁ M₁ hM₁ (hS h hS' hh).1 xx).1 x y
  · simp only at hx; subst hx
    rw [FC_seg2a]
    have := (hshort h hS' hh ξ₂ h₂ M₂ hM₂ (hS h hS' hh).2 false).2.1
    simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_one] at this
    simpa [Real.sq_sqrt (show (0 : ℝ) ≤ 3 * D * N / z.im by positivity)] using this
  · rw [FC_seg2b]
    simpa using (hlong h hS' hh xx).2.1
  · simp only at ho; subst ho
    rw [FC_seg2c]
    have := (hshort h hS' hh ξ₁ h₁ M₁ hM₁ (hS h hS' hh).1 xx).2.1
    simpa [Real.sq_sqrt (show (0 : ℝ) ≤ 3 * D * N / z.im by positivity)] using this
  · simp only at hx; subst hx
    rw [FC_seg2a]
    have := (hshort h hS' hh ξ₂ h₂ M₂ hM₂ (hS h hS' hh).2 false).2.2
    simpa using this
  · rw [FC_seg2b]
    simpa using (hlong h hS' hh xx).2.2
  · simp only at ho; subst ho
    rw [FC_seg2c]
    simpa using (hshort h hS' hh ξ₁ h₁ M₁ hM₁ (hS h hS' hh).1 xx).2.2

end

section

private theorem FC_aniso_le1 (D : ℕ) (hD : 1 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ u v : Idx D N → ℂ, ∑ i, ‖u i‖ ^ 2 ≤ 1 → ∑ i, ‖v i‖ ^ 2 ≤ 1 →
        μ {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' * psiIso (lam D N A) N z <
            ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *ᵥ v)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  obtain ⟨N₀, hN₀⟩ := aniso_local D hD δA τ hδA hτ C τ' hτ' D' hD'
  refine ⟨N₀, fun N hN θ h0 h1 μ hμ A hA u v hu hv => ?_⟩
  set Su := ∑ i, ‖u i‖ ^ 2
  set Sv := ∑ i, ‖v i‖ ^ 2
  have hSu0 : 0 ≤ Su := by positivity
  have hSv0 : 0 ≤ Sv := by positivity
  rcases hSu0.eq_or_lt with hu0 | hu0
  · have : u = 0 := by
      funext i
      have h := Finset.single_le_sum (f := fun i => ‖u i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ i)
      have : ‖u i‖ ^ 2 = 0 := le_antisymm (by
        have h' : ‖u i‖ ^ 2 ≤ Su := h
        rw [← hu0] at h'; exact h') (by positivity)
      simpa using this
    subst this
    have e : {h : Idx D N → Idx D N → ℂ | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' *
        psiIso (lam D N A) N z < ‖star (0 : Idx D N → ℂ) ⬝ᵥ ((res (Matrix.of h + lam D N A) z -
          MExt (lam D N A) z) *ᵥ v)‖} = ∅ := by
      ext h
      simp only [star_zero, zero_dotProduct, norm_zero, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_exists, not_and, not_lt]
      intro z _
      have : 0 ≤ psiIso (lam D N A) N z := by unfold psiIso; positivity
      positivity
    rw [e]; simp
  rcases hSv0.eq_or_lt with hv0 | hv0
  · have : v = 0 := by
      funext i
      have h := Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ i)
      have : ‖v i‖ ^ 2 = 0 := le_antisymm (by
        have h' : ‖v i‖ ^ 2 ≤ Sv := h
        rw [← hv0] at h'; exact h') (by positivity)
      simpa using this
    subst this
    have e : {h : Idx D N → Idx D N → ℂ | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' *
        psiIso (lam D N A) N z < ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z -
          MExt (lam D N A) z) *ᵥ (0 : Idx D N → ℂ))‖} = ∅ := by
      ext h
      simp only [Matrix.mulVec_zero, dotProduct_zero, norm_zero, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_exists, not_and, not_lt]
      intro z _
      have : 0 ≤ psiIso (lam D N A) N z := by unfold psiIso; positivity
      positivity
    rw [e]; simp
  set a := (Real.sqrt Su)⁻¹
  set b := (Real.sqrt Sv)⁻¹
  have hsa : 0 < Real.sqrt Su := Real.sqrt_pos.2 hu0
  have hsb : 0 < Real.sqrt Sv := Real.sqrt_pos.2 hv0
  set u' : Idx D N → ℂ := (a : ℂ) • u
  set v' : Idx D N → ℂ := (b : ℂ) • v
  have hu' : ∑ i, ‖u' i‖ ^ 2 = 1 := by
    simp only [u', Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow]
    rw [← Finset.mul_sum, sq_abs, inv_pow, Real.sq_sqrt hSu0, inv_mul_cancel₀ hu0.ne']
  have hv' : ∑ i, ‖v' i‖ ^ 2 = 1 := by
    simp only [v', Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow]
    rw [← Finset.mul_sum, sq_abs, inv_pow, Real.sq_sqrt hSv0, inv_mul_cancel₀ hv0.ne']
  refine (measure_mono ?_).trans (hN₀ N hN θ h0 h1 μ hμ A hA u' v' hu' hv')
  intro h hh
  obtain ⟨z, hz, hlt⟩ := hh
  refine ⟨z, hz, lt_of_lt_of_le hlt ?_⟩
  have e : star u' ⬝ᵥ ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *ᵥ v') =
      ((a * b : ℝ) : ℂ) * (star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z -
        MExt (lam D N A) z) *ᵥ v)) := by
    simp only [u', v', star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    simp [Complex.star_def, Complex.conj_ofReal]
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have ha1 : 1 ≤ a := by
    rw [one_le_inv₀ hsa]; exact Real.sqrt_le_one.mpr hu
  have hb1 : 1 ≤ b := by
    rw [one_le_inv₀ hsb]; exact Real.sqrt_le_one.mpr hv
  have hn := norm_nonneg (star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z -
    MExt (lam D N A) z) *ᵥ v))
  have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le ha1 hb1
  calc ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *ᵥ v)‖
      = 1 * ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *ᵥ v)‖ := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hab hn

private theorem FC_iso_event (D : ℕ) (hD : 1 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ X : Matrix (Idx D N) (Idx D N) ℂ, opNorm X ≤ 1 →
        μ {h | ¬ ∀ ξ ∈ specDom τ N, FC_iso (res (Matrix.of h + lam D N A) ξ)
            (MExt (lam D N A) ξ) X ((N : ℝ) ^ τ' * psiIso (lam D N A) N ξ)} ≤
          ENNReal.ofReal (3 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-D')) := by
  intro τ' hτ' D' hD'
  obtain ⟨N₀, hN₀⟩ := FC_aniso_le1 D hD δA τ hδA hτ C τ' hτ' D' hD'
  refine ⟨N₀, fun N hN θ h0 h1 μ hμ A hA X hX => ?_⟩
  have hprob := hμ.prob
  set Bad : (Idx D N → ℂ) → (Idx D N → ℂ) → Set (Idx D N → Idx D N → ℂ) := fun u v =>
    {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ' * psiIso (lam D N A) N z <
      ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) *ᵥ v)‖}
  have hcol : ∀ y, ∑ i, ‖FC_col X y i‖ ^ 2 ≤ 1 := fun y =>
    (FC_col_norm X y).trans (by nlinarith [FC_opNorm_nonneg X])
  have hB1 : ∀ p : Idx D N × Idx D N, μ (Bad (Pi.single p.1 1) (Pi.single p.2 1)) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := fun p =>
    hN₀ N hN θ h0 h1 μ hμ A hA _ _ (FC_single_norm _) (FC_single_norm _)
  have hB2 : ∀ p : Idx D N × Idx D N, μ (Bad (Pi.single p.1 1) (FC_col X p.2)) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := fun p =>
    hN₀ N hN θ h0 h1 μ hμ A hA _ _ (FC_single_norm _) (hcol _)
  have hB3 : ∀ y : Idx D N, μ (Bad (FC_col X y) (FC_col X y)) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := fun y =>
    hN₀ N hN θ h0 h1 μ hμ A hA _ _ (hcol _) (hcol _)
  have hsub : {h | ¬ ∀ ξ ∈ specDom τ N, FC_iso (res (Matrix.of h + lam D N A) ξ)
      (MExt (lam D N A) ξ) X ((N : ℝ) ^ τ' * psiIso (lam D N A) N ξ)} ⊆
      (⋃ p : Idx D N × Idx D N, Bad (Pi.single p.1 1) (Pi.single p.2 1)) ∪
        (⋃ p : Idx D N × Idx D N, Bad (Pi.single p.1 1) (FC_col X p.2)) ∪
        (⋃ y : Idx D N, Bad (FC_col X y) (FC_col X y)) := by
    intro h hh
    by_contra hc
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hc
    obtain ⟨⟨c1, c2⟩, c3⟩ := hc
    apply hh
    intro ξ hξ
    refine ⟨fun x y => ?_, fun x y => ?_, fun y => ?_⟩
    · have := c1 (x, y)
      simp only [Bad, Set.mem_setOf_eq, not_exists, not_and, not_lt] at this
      have h2 := this ξ hξ
      have e : star (Pi.single x (1 : ℂ) : Idx D N → ℂ) ⬝ᵥ
          ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) *ᵥ Pi.single y 1) =
          res (Matrix.of h + lam D N A) ξ x y - MExt (lam D N A) ξ x y := by
        simp [Matrix.mulVec_single, dotProduct, Pi.single_apply]
      rwa [e] at h2
    · have := c2 (x, y)
      simp only [Bad, Set.mem_setOf_eq, not_exists, not_and, not_lt] at this
      have h2 := this ξ hξ
      have e : star (Pi.single x (1 : ℂ) : Idx D N → ℂ) ⬝ᵥ
          ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) *ᵥ FC_col X y) =
          (res (Matrix.of h + lam D N A) ξ * X) x y - (MExt (lam D N A) ξ * X) x y := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, FC_col, Matrix.mul_apply, sub_mul,
          Finset.sum_sub_distrib]
      rwa [e] at h2
    · have := c3 y
      simp only [Bad, Set.mem_setOf_eq, not_exists, not_and, not_lt] at this
      exact this ξ hξ
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
  have u1 := (measure_iUnion_fintype_le μ _).trans (Finset.sum_le_sum fun p _ => hB1 p)
  have u2 := (measure_iUnion_fintype_le μ _).trans (Finset.sum_le_sum fun p _ => hB2 p)
  have u3 := (measure_iUnion_fintype_le μ _).trans (Finset.sum_le_sum fun y _ => hB3 y)
  refine (add_le_add (add_le_add u1 u2) u3).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  have hNp : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  have hDN1 : (D : ℝ) * N ≤ ((D : ℝ) * N) ^ 2 := by
    rcases Nat.eq_zero_or_pos N with hN0 | hN0
    · subst hN0; simp
    · have : (1 : ℝ) ≤ D * N := by
        have : 1 ≤ D * N := Nat.one_le_iff_ne_zero.2 (by positivity)
        exact_mod_cast this
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hDN1 hNp]

end

section

private theorem FC_sTheta_sub (D N : ℕ) (θ : ℝ) (R R' : Matrix (Idx D N) (Idx D N) ℂ) :
    sTheta D N θ (R - R') = sTheta D N θ R - sTheta D N θ R' := by
  unfold sTheta
  simp only [Matrix.sub_mul, ntr, Matrix.trace_sub, mul_sub, sub_smul, Finset.sum_sub_distrib,
    smul_sub]
  abel

private theorem FC_GmM (D N : ℕ) (hD : 2 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (ξ : ℂ) (hξ : ξ.im ≠ 0) :
    res (H + lam D N A) ξ - MExt (lam D N A) ξ =
      -(MExt (lam D N A) ξ * hgUnder D N θ H (lam D N A) ξ) +
        MExt (lam D N A) ξ * sTheta D N θ (res (H + lam D N A) ξ - MExt (lam D N A) ξ) *
          res (H + lam D N A) ξ := by
  set Λ := lam D N A
  set G := res (H + Λ) ξ
  set M := MExt Λ ξ
  set m := mExt Λ ξ
  obtain ⟨-, hM⟩ := def_M_scalar D hD N hN A ξ hξ
  have hM1 : (Λ - (m + ξ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M = 1 := by
    have : ((m + ξ) • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Λ) * M = -1 :=
      eq_neg_of_add_eq_zero_left hM
    rw [← neg_sub, Matrix.neg_mul, this, neg_neg]
  have hM2 : M * (Λ - (m + ξ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) = 1 :=
    mul_eq_one_comm.mp hM1
  obtain ⟨hG1, -⟩ := res_mul_sub_of_im_ne (H + Λ) (hH.add (lam_isHermitian D N A)) ξ hξ
  have hS : sTheta D N θ M = m • (1 : Matrix (Idx D N) (Idx D N) ℂ) := sTheta_MExt D N θ A ξ hξ
  unfold hgUnder
  rw [FC_sTheta_sub, hS]
  have key : M * (H + m • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G = M - G := by
    have e : H + m • (1 : Matrix (Idx D N) (Idx D N) ℂ) =
        (H + Λ - ξ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) -
          (Λ - (m + ξ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) := by
      rw [add_smul]; abel
    rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hG1, Matrix.mul_one, hM2,
      Matrix.one_mul]
  have e2 : -(M * (H * G + sTheta D N θ G * G)) + M * (sTheta D N θ G - m • 1) * G =
      -(M * (H + m • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [e2, key, neg_sub]

private theorem FC_ntr_Ea (D N : ℕ) (R : Matrix (Idx D N) (Idx D N) ℂ) (c : Fin D) :
    ntr (R * Ea D N c) = (((D : ℂ) * N))⁻¹ * ∑ i, (if i.1 = c then R i i else 0) := by
  unfold ntr Ea
  simp only [Fintype.card_prod, Fintype.card_fin, Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

private theorem FC_sTheta_diag (D N : ℕ) (hD : 1 ≤ D) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ) :
    sTheta D N θ R = Matrix.diagonal fun j => ∑ i, (varProf D N θ j i : ℂ) * R i i := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  ext p q
  unfold sTheta
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.diagonal_apply,
    smul_eq_mul, Matrix.one_apply]
  by_cases hpq : p = q
  · subst hpq
    simp only [↓reduceIte, mul_one]
    have e1 : ∀ a : Fin D, (Ea D N a) p p = if p.1 = a then 1 else 0 := fun a => by
      simp [Ea, Matrix.diagonal_apply]
    simp only [e1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [FC_ntr_Ea]
    have e2 : ntr R = (((D : ℂ) * N))⁻¹ * ∑ i, R i i := by
      unfold ntr; simp [Matrix.trace]
    rw [e2]
    unfold varProf
    push_cast
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    congr 1
    · congr 1
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hb : p.1 = i.1
      · rw [if_pos hb.symm, if_pos hb]
        have hN0 : (N : ℂ) ≠ 0 := by
          have := i.2.pos; exact_mod_cast (show N ≠ 0 by omega)
        push_cast
        field_simp
      · rw [if_neg (Ne.symm hb), if_neg hb]; simp
  · have e : ∀ x : Fin D, Ea D N x p q = 0 := fun x => by simp [Ea, Matrix.diagonal_apply, hpq]
    simp [e, hpq]

end

section

private theorem FC_ntr_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ‖ntr A‖ ≤ opNorm A := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [ntr, Matrix.trace]; exact FC_opNorm_nonneg A
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, opNorm A := Finset.sum_le_sum fun i _ => norm_apply_le_opNorm A i i
    _ = _ := by simp

private theorem FC_PTheta_nonneg (D : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x c : Fin D) :
    PTheta D θ x c = (((if x = c then θ else 0) + (1 - θ) / D : ℝ) : ℂ) := by
  simp only [PTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
    smul_eq_mul]
  split_ifs <;> push_cast <;> ring

private theorem FC_PTheta_row (D : ℕ) (hD : 1 ≤ D) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : Fin D) :
    ∑ c, ‖PTheta D θ x c‖ = 1 := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  simp only [FC_PTheta_nonneg D θ h0 h1, Complex.norm_real, Real.norm_eq_abs]
  have hnn : ∀ c, 0 ≤ (if x = c then θ else 0) + (1 - θ) / D := fun c => by
    have : 0 ≤ (1 - θ) / D := div_nonneg (by linarith) (Nat.cast_nonneg _)
    split_ifs <;> linarith
  simp only [fun c => abs_of_nonneg (hnn c), Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

private theorem FC_solve (D N : ℕ) (hD : 1 ≤ D) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (M : Matrix (Idx D N) (Idx D N) ℂ) (hM : opNorm M ≤ 5 / 4) (Mh : Matrix (Fin D) (Fin D) ℂ)
    (hMh : ∀ a x, Mh a x = (D : ℂ) * ntr (M * Ea D N a * M * Ea D N x))
    (hdet : (1 - Mh * PTheta D θ).det ≠ 0)
    (T Lf : Matrix (Idx D N) (Idx D N) ℂ → ℂ) (α : ℂ) (e : ℝ)
    (hT : ∀ B, opNorm B ≤ 1 → ‖T B - α * Lf B - ∑ x, ∑ c, PTheta D θ x c *
      ((D : ℂ) * T (Ea D N c)) * ntr (Ea D N x * M * B * M)‖ ≤ e)
    (B : Matrix (Idx D N) (Idx D N) ℂ) (hB : opNorm B ≤ 1) :
    ‖T B - α * (Lf B + ∑ x, ∑ c, PTheta D θ x c *
        ((1 - Mh * PTheta D θ)⁻¹ *ᵥ fun a => (D : ℂ) * Lf (Ea D N a)) c *
          ntr (Ea D N x * M * B * M))‖ ≤
      e + 2 * D * (D * Real.sqrt D * opNorm (1 - Mh * PTheta D θ)⁻¹ * e) := by
  set R := (1 - Mh * PTheta D θ)⁻¹ with hR
  set P := PTheta D θ
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hT B hB)
  obtain ⟨v, hvdef⟩ : ∃ v : Fin D → ℂ, v = fun c => (D : ℂ) * T (Ea D N c) := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : Fin D → ℂ, w = fun a => (D : ℂ) * Lf (Ea D N a) := ⟨_, rfl⟩
  have hvc : ∀ c, (D : ℂ) * T (Ea D N c) = v c := fun c => by rw [hvdef]
  have hwc : ∀ c, (D : ℂ) * Lf (Ea D N c) = w c := fun c => by rw [hwdef]
  rw [show (fun a => (D : ℂ) * Lf (Ea D N a)) = w from hwdef.symm]
  simp only [hvc] at hT ⊢
  obtain ⟨u, hudef⟩ : ∃ u : Fin D → ℂ, u = ((1 - Mh * P) *ᵥ v) - α • w := ⟨_, rfl⟩
  have hMh' : ∀ a x, (D : ℂ) * ntr (Ea D N x * M * Ea D N a * M) = Mh a x := by
    intro a x
    have h1 : ntr (Ea D N x * M * Ea D N a * M) = ntr (M * Ea D N a * M * Ea D N x) := by
      unfold ntr
      rw [show Ea D N x * M * Ea D N a * M = Ea D N x * (M * Ea D N a * M) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    rw [hMh, h1]
  have hua : ∀ a, ‖u a‖ ≤ D * e := by
    intro a
    have h := hT (Ea D N a) (FC_opNorm_Ea D N a)
    have e1 : u a = (D : ℂ) * (T (Ea D N a) - α * Lf (Ea D N a) - ∑ x, ∑ c, P x c *
        v c * ntr (Ea D N x * M * Ea D N a * M)) := by
      have e3 : ((1 - Mh * P) *ᵥ v) a = v a - ∑ c, (∑ x, Mh a x * P x c) * v c := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [hudef, Pi.sub_apply, e3, Pi.smul_apply, smul_eq_mul, mul_sub, mul_sub, hvc, ← hwc,
        Finset.mul_sum]
      have e4 : ∑ c, (∑ x, Mh a x * P x c) * v c =
          ∑ x, (D : ℂ) * ∑ c, P x c * v c * ntr (Ea D N x * M * Ea D N a * M) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => ?_
        rw [← hMh' a x]; ring
      rw [e4]; ring
    rw [e1, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
  have hRinv : R * (1 - Mh * P) = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
  have hv : v = R *ᵥ (α • w + u) := by
    have : α • w + u = (1 - Mh * P) *ᵥ v := by rw [hudef]; abel
    rw [this, Matrix.mulVec_mulVec, hRinv, Matrix.one_mulVec]
  have hdiff : ∀ c, v c - α * (R *ᵥ w) c = (R *ᵥ u) c := by
    intro c
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul]
    simp
  have hRu : ∀ c, ‖(R *ᵥ u) c‖ ≤ opNorm R * (Real.sqrt D * (D * e)) := by
    intro c
    have h := FC_form_le R (Pi.single c 1) u
    have e1 : star (Pi.single c (1 : ℂ) : Fin D → ℂ) ⬝ᵥ (R *ᵥ u) = (R *ᵥ u) c := by
      simp [dotProduct, Pi.single_apply]
    rw [e1] at h
    refine h.trans ?_
    have hs1 : Real.sqrt (∑ k, ‖(Pi.single c (1 : ℂ) : Fin D → ℂ) k‖ ^ 2) ≤ 1 :=
      Real.sqrt_le_one.mpr (by
        rw [Finset.sum_eq_single c]
        · simp
        · intro b _ hb; simp [Pi.single_apply, hb]
        · simp)
    have hs2 : Real.sqrt (∑ k, ‖u k‖ ^ 2) ≤ Real.sqrt D * (D * e) := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ D * e), ← Real.sqrt_mul (Nat.cast_nonneg _)]
      refine Real.sqrt_le_sqrt ?_
      calc ∑ k, ‖u k‖ ^ 2 ≤ ∑ _k : Fin D, (D * e) ^ 2 :=
            Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hua k) 2
        _ = D * (D * e) ^ 2 := by simp
    have hR0 := FC_opNorm_nonneg R
    calc opNorm R * Real.sqrt (∑ k, ‖(Pi.single c (1 : ℂ) : Fin D → ℂ) k‖ ^ 2) *
          Real.sqrt (∑ k, ‖u k‖ ^ 2) ≤ opNorm R * 1 * (Real.sqrt D * (D * e)) := by gcongr
      _ = _ := by ring
  have hdec : T B - α * (Lf B + ∑ x, ∑ c, P x c * (R *ᵥ w) c * ntr (Ea D N x * M * B * M)) =
      (T B - α * Lf B - ∑ x, ∑ c, P x c * v c * ntr (Ea D N x * M * B * M)) +
        ∑ x, ∑ c, P x c * (R *ᵥ u) c * ntr (Ea D N x * M * B * M) := by
    have : ∀ x c, P x c * v c * ntr (Ea D N x * M * B * M) =
        α * (P x c * (R *ᵥ w) c * ntr (Ea D N x * M * B * M)) +
          P x c * (R *ᵥ u) c * ntr (Ea D N x * M * B * M) := by
      intro x c
      rw [← hdiff c]; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hdec]
  refine (norm_add_le _ _).trans (add_le_add (hT B hB) ?_)
  have hMBM : ∀ x, ‖ntr (Ea D N x * M * B * M)‖ ≤ 2 := by
    intro x
    refine (FC_ntr_le _).trans ?_
    have h1 := opNorm_mul_le (Ea D N x * M * B) M
    have h2 := opNorm_mul_le (Ea D N x * M) B
    have h3 := opNorm_mul_le (Ea D N x) M
    have hE := FC_opNorm_Ea D N x
    have := FC_opNorm_nonneg M
    have := FC_opNorm_nonneg B
    have := FC_opNorm_nonneg (Ea D N x)
    have := FC_opNorm_nonneg (Ea D N x * M)
    have := FC_opNorm_nonneg (Ea D N x * M * B)
    nlinarith [mul_le_mul h3 hM (FC_opNorm_nonneg _) (by linarith),
      mul_le_mul h2 hB (FC_opNorm_nonneg _) (by positivity)]
  have hK : 0 ≤ opNorm R * (Real.sqrt D * (D * e)) := by
    have := FC_opNorm_nonneg R; positivity
  calc ‖∑ x, ∑ c, P x c * (R *ᵥ u) c * ntr (Ea D N x * M * B * M)‖
      ≤ ∑ x, ∑ c, ‖P x c‖ * (opNorm R * (Real.sqrt D * (D * e))) * 2 := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul, norm_mul]
        gcongr
        · exact hRu c
        · exact hMBM x
    _ = ∑ x : Fin D, (opNorm R * (Real.sqrt D * (D * e))) * 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_mul, ← Finset.sum_mul, FC_PTheta_row D hD θ h0 h1 x, one_mul]
    _ = _ := by simp; ring

end

section

private abbrev FC_diagM {D N : ℕ} (M : Matrix (Idx D N) (Idx D N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  diagonal (diag M)

private def FC_leadM {D N : ℕ} (M B : Matrix (Idx D N) (Idx D N) ℂ) : ℂ :=
  ∑ y, ((D : ℂ) * ntr (FC_diagM M * FC_diagM M * Ea D N y)) * ntr (M * B * M * FC_diagM M * Ea D N y)

private theorem FC_sum_Ea (D N : ℕ) : ∑ y, Ea D N y = (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Ea, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : p = q
  · subst h; simp
  · simp [h]

private theorem FC_ntr_sum_Ea (D N : ℕ) (Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ y, ntr (Y * Ea D N y) = ntr Y := by
  unfold ntr
  rw [← Finset.mul_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, FC_sum_Ea, Matrix.mul_one]

private theorem FC_ntr_sum_Ea' (D N : ℕ) (Y Z : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ a, ntr (Y * Ea D N a * Z) = ntr (Y * Z) := by
  unfold ntr
  rw [← Finset.mul_sum, ← Matrix.trace_sum]
  congr 2
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, FC_sum_Ea, Matrix.mul_one]

private theorem FC_Dntr_le (D N : ℕ) (Y : Matrix (Idx D N) (Idx D N) ℂ) (y : Fin D) :
    ‖(D : ℂ) * ntr (Y * Ea D N y)‖ ≤ opNorm Y := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [ntr, Matrix.trace]; exact FC_opNorm_nonneg Y
  have hD0 : (D : ℝ) ≠ 0 := by have := y.pos; exact_mod_cast (show D ≠ 0 by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [FC_ntr_Ea, ← mul_assoc, norm_mul]
  have e : ‖(D : ℂ) * ((D : ℂ) * N)⁻¹‖ = (N : ℝ)⁻¹ := by
    rw [mul_inv, ← mul_assoc, norm_mul, norm_mul, Complex.norm_natCast, norm_inv, norm_inv,
      Complex.norm_natCast, Complex.norm_natCast, mul_inv_cancel₀ hD0, one_mul]
  rw [e]
  have hs : ‖∑ i, (if i.1 = y then Y i i else 0)‖ ≤ N * opNorm Y := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖(if i.1 = y then Y i i else 0)‖ ≤ ∑ i : Idx D N, (if i.1 = y then opNorm Y else 0) :=
          Finset.sum_le_sum fun i _ => by
            split_ifs
            · exact norm_apply_le_opNorm Y i i
            · simp
      _ = N * opNorm Y := by
          rw [Fintype.sum_prod_type]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          rw [Finset.sum_eq_single y]
          · simp
          · intro b _ hb; simp [hb]
          · simp
  calc (N : ℝ)⁻¹ * ‖∑ i, (if i.1 = y then Y i i else 0)‖ ≤ (N : ℝ)⁻¹ * (N * opNorm Y) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = opNorm Y := by field_simp

private theorem FC_Dntr_Ea (D N : ℕ) (hN : 1 ≤ N) (y : Fin D) : (D : ℂ) * ntr (Ea D N y) = 1 := by
  have h := FC_ntr_Ea D N 1 y
  rw [Matrix.one_mul] at h
  rw [h]
  have hD0 : (D : ℂ) ≠ 0 := by have := y.pos; exact_mod_cast (show D ≠ 0 by omega)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e : ∑ i : Idx D N, (if i.1 = y then (1 : Matrix (Idx D N) (Idx D N) ℂ) i i else 0) = N := by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.one_apply_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [e]
  field_simp

private theorem FC_dg_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (m : ℂ) :
    opNorm (diagonal (diag M) - m • (1 : Matrix ι ι ℂ)) ≤ opNorm (M - m • 1) ∧
      opNorm (diagonal (diag M)) ≤ opNorm M := by
  have e : diagonal (diag M) - m • (1 : Matrix ι ι ℂ) = diagonal fun i => M i i - m := by
    ext i j; by_cases h : i = j
    · subst h; simp [Matrix.diagonal_apply]
    · simp [Matrix.diagonal_apply, h]
  have hnorm : ∀ v : ι → ℂ, opNorm (diagonal v) = ‖v‖ := fun v => by
    unfold opNorm; rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  constructor
  · rw [e, hnorm]
    refine (pi_norm_le_iff_of_nonneg (FC_opNorm_nonneg _)).2 fun i => ?_
    have := norm_apply_le_opNorm (M - m • (1 : Matrix ι ι ℂ)) i i
    simpa using this
  · rw [hnorm]
    refine (pi_norm_le_iff_of_nonneg (FC_opNorm_nonneg _)).2 fun i => ?_
    exact norm_apply_le_opNorm M i i

private def FC_lead15M {D N : ℕ} (M B : Matrix (Idx D N) (Idx D N) ℂ) : ℂ :=
  ntr (FC_diagM M * FC_diagM M) * (ntr (M * B * M * FC_diagM M) +
    ntr (M * M * FC_diagM M) * ntr (M * M * B) / (1 - ntr (M * M)))

private theorem FC_op4 {ι : Type*} [Fintype ι] [DecidableEq ι] (A B C E : Matrix ι ι ℂ) (a b c e : ℝ)
    (ha : opNorm A ≤ a) (hb : opNorm B ≤ b) (hc : opNorm C ≤ c) (he : opNorm E ≤ e) :
    opNorm (A * B * C * E) ≤ a * b * c * e := by
  have h0a := FC_opNorm_nonneg A
  have h0b := FC_opNorm_nonneg B
  have h0c := FC_opNorm_nonneg C
  have h0e := FC_opNorm_nonneg E
  have ha0 : 0 ≤ a := h0a.trans ha
  have hb0 : 0 ≤ b := h0b.trans hb
  have hc0 : 0 ≤ c := h0c.trans hc
  refine (opNorm_mul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_right ((opNorm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) h0c)) h0e).trans ?_
  have h1 : opNorm A * opNorm B ≤ a * b := mul_le_mul ha hb h0b ha0
  have h2 : opNorm A * opNorm B * opNorm C ≤ a * b * c :=
    mul_le_mul h1 hc h0c (by positivity)
  exact mul_le_mul h2 he h0e (by positivity)

private theorem FC_Dntr_sub (D N : ℕ) (hN : 1 ≤ N) (Y : Matrix (Idx D N) (Idx D N) ℂ) (c : ℂ)
    (y : Fin D) :
    (D : ℂ) * ntr ((Y - c • 1) * Ea D N y) = (D : ℂ) * ntr (Y * Ea D N y) - c := by
  have h := FC_Dntr_Ea D N hN y
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  unfold ntr at h ⊢
  rw [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  linear_combination (-c) * h

private theorem FC_avg_le {D : ℕ} (hD : 1 ≤ D) (x : Fin D → ℂ) (c : ℂ) (b : ℝ)
    (hx : ∀ y, ‖x y - c‖ ≤ b) : ‖(D : ℂ)⁻¹ * (∑ y, x y) - c‖ ≤ b := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hDr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have e : (D : ℂ)⁻¹ * (∑ y, x y) - c = (D : ℂ)⁻¹ * ∑ y, (x y - c) := by
    rw [Finset.sum_sub_distrib]; simp; field_simp
  rw [e, norm_mul, norm_inv, Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  calc (D : ℝ)⁻¹ * ∑ y, ‖x y - c‖ ≤ (D : ℝ)⁻¹ * ∑ _y : Fin D, b :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hx y) (by positivity)
    _ = b := by simp; field_simp

private theorem FC_sq_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) (c : ℂ)
    (κ : ℝ) (hκ : opNorm (Y - c • 1) ≤ κ) :
    opNorm (Y * Y - (c ^ 2) • 1) ≤ κ * (opNorm Y + ‖c‖) := by
  have e : Y * Y - (c ^ 2) • (1 : Matrix ι ι ℂ) = (Y - c • 1) * (Y + c • 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, sq]
    module
  rw [e]
  refine (opNorm_mul_le _ _).trans ?_
  have h2 : opNorm (Y + c • 1) ≤ opNorm Y + ‖c‖ := by
    refine (opNorm_add_le _ _).trans ?_
    rw [opNorm_smul]
    have := FC_opNorm_one (ι := ι)
    nlinarith [norm_nonneg c]
  exact mul_le_mul hκ h2 (FC_opNorm_nonneg _) ((FC_opNorm_nonneg _).trans hκ)

private theorem FC_cube_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M dM : Matrix ι ι ℂ) (m : ℂ)
    (κ : ℝ) (hκ : opNorm (M - m • 1) ≤ κ) (hdκ : opNorm (dM - m • 1) ≤ κ) :
    opNorm (M * dM * M - (m ^ 3) • 1) ≤ κ * (opNorm dM * opNorm M + ‖m‖ * opNorm M + ‖m‖ ^ 2) := by
  have e : M * dM * M - (m ^ 3) • (1 : Matrix ι ι ℂ) =
      (M - m • 1) * dM * M + m • ((dM - m • 1) * M) + (m ^ 2) • (M - m • 1) := by
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul,
      Matrix.mul_smul, Matrix.mul_one]
    module
  rw [e]
  have h0 := FC_opNorm_nonneg (M - m • 1)
  have h0' := FC_opNorm_nonneg (dM - m • 1)
  have hdM := FC_opNorm_nonneg dM
  have hM0 := FC_opNorm_nonneg M
  have hk0 : 0 ≤ κ := h0.trans hκ
  have t1 : opNorm ((M - m • 1) * dM * M) ≤ κ * (opNorm dM * opNorm M) := by
    refine (opNorm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) hM0).trans ?_
    nlinarith [mul_le_mul_of_nonneg_right hκ hdM]
  have t2 : opNorm (m • ((dM - m • 1) * M)) ≤ κ * (‖m‖ * opNorm M) := by
    rw [opNorm_smul]
    refine (mul_le_mul_of_nonneg_left (opNorm_mul_le _ _) (norm_nonneg _)).trans ?_
    nlinarith [mul_le_mul_of_nonneg_right hdκ hM0, norm_nonneg m]
  have t3 : opNorm ((m ^ 2) • (M - m • 1)) ≤ κ * ‖m‖ ^ 2 := by
    rw [opNorm_smul, norm_pow]
    nlinarith [pow_nonneg (norm_nonneg m) 2]
  calc _ ≤ opNorm ((M - m • 1) * dM * M + m • ((dM - m • 1) * M)) +
        opNorm ((m ^ 2) • (M - m • 1)) := opNorm_add_le _ _
    _ ≤ opNorm ((M - m • 1) * dM * M) + opNorm (m • ((dM - m • 1) * M)) +
        opNorm ((m ^ 2) • (M - m • 1)) := by gcongr; exact opNorm_add_le _ _
    _ ≤ _ := by nlinarith

private theorem FC_g_sum (D N : ℕ) (M dM : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D) :
    ∑ y, (D : ℂ) * ntr (M * Ea D N a * M * dM * Ea D N y) =
      (D : ℂ) * ntr (M * dM * M * Ea D N a) := by
  have h : ntr (M * Ea D N a * M * dM) = ntr (M * dM * M * Ea D N a) := by
    unfold ntr
    rw [show M * Ea D N a * M * dM = M * (Ea D N a * (M * dM)) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show Ea D N a * (M * dM) * M = Ea D N a * (M * dM * M) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  rw [← Finset.mul_sum, FC_ntr_sum_Ea, h]

private theorem FC_ntr_MBM (D N : ℕ) (M B : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ x, ntr (Ea D N x * M * B * M) = ntr (M * M * B) := by
  have h := FC_ntr_sum_Ea' D N 1 (M * B * M)
  simp only [Matrix.one_mul] at h
  rw [show ∑ x, ntr (Ea D N x * M * B * M) = ∑ x, ntr (Ea D N x * (M * B * M)) by
    simp only [Matrix.mul_assoc], h]
  unfold ntr
  rw [show M * B * M = (M * B) * M from rfl, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

private theorem FC_Ltrue (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (M : Matrix (Idx D N) (Idx D N) ℂ) (hM : opNorm M ≤ 5 / 4) (m : ℂ) (hm : ‖m‖ ≤ 1)
    (κ : ℝ) (hκ : opNorm (M - m • 1) ≤ κ) (Mh : Matrix (Fin D) (Fin D) ℂ)
    (sR : ℂ) (hR1 : (1 - Mh * PTheta D θ)⁻¹ *ᵥ (fun _ => 1) = fun _ => sR)
    (hsR : sR = (1 - ntr (M * M))⁻¹) (B : Matrix (Idx D N) (Idx D N) ℂ) (hB : opNorm B ≤ 1) :
    ‖FC_leadM M B + (∑ x, (∑ c, PTheta D θ x c *
        ((1 - Mh * PTheta D θ)⁻¹ *ᵥ fun a => (D : ℂ) * FC_leadM M (Ea D N a)) c *
          ntr (Ea D N x * M * B * M))) - FC_lead15M M B‖ ≤
      (12 * D + 24 * D * ‖sR‖ + 4 * D * Real.sqrt D * (6 * D + 4) *
        opNorm (1 - Mh * PTheta D θ)⁻¹) * κ := by
  obtain ⟨R, hRd⟩ : ∃ R, R = (1 - Mh * PTheta D θ)⁻¹ := ⟨_, rfl⟩
  rw [← hRd] at hR1 ⊢
  obtain ⟨dM, hdMd⟩ : ∃ dM, dM = FC_diagM M := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := (FC_opNorm_nonneg _).trans hκ
  obtain ⟨hdm, hdM⟩ := FC_dg_le M m
  have hdm' : opNorm (dM - m • 1) ≤ κ := by rw [hdMd]; exact hdm.trans hκ
  have hdM' : opNorm dM ≤ 5 / 4 := by rw [hdMd]; exact hdM.trans hM
  have hDr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hE := FC_opNorm_Ea D N
  have hm0 := norm_nonneg m
  have hxy : ∀ y, ‖(D : ℂ) * ntr (dM * dM * Ea D N y) - m ^ 2‖ ≤ 3 * κ := by
    intro y
    rw [← FC_Dntr_sub D N hN]
    refine (FC_Dntr_le D N _ y).trans ((FC_sq_sub_le dM m κ hdm').trans ?_)
    nlinarith
  have hxb0 : ntr (dM * dM) = (D : ℂ)⁻¹ * ∑ y, (D : ℂ) * ntr (dM * dM * Ea D N y) := by
    rw [← Finset.mul_sum, FC_ntr_sum_Ea, ← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast (show D ≠ 0 by omega) : (D : ℂ) ≠ 0), one_mul]
  have hxb : ‖ntr (dM * dM) - m ^ 2‖ ≤ 3 * κ := by
    rw [hxb0]; exact FC_avg_le hD _ _ _ hxy
  have hdx : ∀ y, ‖(D : ℂ) * ntr (dM * dM * Ea D N y) - ntr (dM * dM)‖ ≤ 6 * κ := fun y => by
    calc _ = ‖((D : ℂ) * ntr (dM * dM * Ea D N y) - m ^ 2) - (ntr (dM * dM) - m ^ 2)‖ := by
          ring_nf
      _ ≤ _ := norm_sub_le _ _
      _ ≤ 6 * κ := by linarith [hxy y, hxb]
  have hg : ∀ a y, ‖(D : ℂ) * ntr (M * Ea D N a * M * dM * Ea D N y)‖ ≤ 2 := by
    intro a y
    refine (FC_Dntr_le D N _ y).trans ?_
    have := FC_op4 M (Ea D N a) M dM (5 / 4) 1 (5 / 4) (5 / 4) hM (hE a) hM hdM'
    linarith
  have hq : ∀ a, ‖(D : ℂ) * ntr (M * dM * M * Ea D N a) - m ^ 3‖ ≤ 4 * κ := by
    intro a
    rw [← FC_Dntr_sub D N hN]
    refine (FC_Dntr_le D N _ a).trans ((FC_cube_sub_le M dM m κ hκ hdm').trans ?_)
    have : opNorm dM * opNorm M + ‖m‖ * opNorm M + ‖m‖ ^ 2 ≤ 4 := by
      have := FC_opNorm_nonneg dM; have := FC_opNorm_nonneg M
      have : ‖m‖ ^ 2 ≤ 1 := pow_le_one₀ hm0 hm
      nlinarith
    nlinarith
  have hw : ∀ a, (D : ℂ) * FC_leadM M (Ea D N a) = ∑ y, (D : ℂ) * ntr (dM * dM * Ea D N y) *
      ((D : ℂ) * ntr (M * Ea D N a * M * dM * Ea D N y)) := by
    intro a
    unfold FC_leadM
    rw [Finset.mul_sum, ← hdMd]
    exact Finset.sum_congr rfl fun y _ => by ring
  obtain ⟨w, hwd⟩ : ∃ w : Fin D → ℂ, w = fun a => (D : ℂ) * FC_leadM M (Ea D N a) := ⟨_, rfl⟩
  rw [← hwd]
  have hwa : ∀ a, ‖w a - m ^ 5‖ ≤ (6 * D + 4) * κ := by
    intro a
    have e : w a - m ^ 5 = (∑ y, ((D : ℂ) * ntr (dM * dM * Ea D N y) - m ^ 2) *
        ((D : ℂ) * ntr (M * Ea D N a * M * dM * Ea D N y))) +
        m ^ 2 * ((D : ℂ) * ntr (M * dM * M * Ea D N a) - m ^ 3) := by
      rw [hwd]
      simp only
      rw [hw a, ← FC_g_sum D N M dM a, mul_sub, Finset.mul_sum]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖∑ y, ((D : ℂ) * ntr (dM * dM * Ea D N y) - m ^ 2) *
        ((D : ℂ) * ntr (M * Ea D N a * M * dM * Ea D N y))‖ ≤ D * (3 * κ * 2) := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ _y : Fin D, 3 * κ * 2 := Finset.sum_le_sum fun y _ => by
            rw [norm_mul]; exact mul_le_mul (hxy y) (hg a y) (norm_nonneg _) (by positivity)
        _ = D * (3 * κ * 2) := by simp
    have h2 : ‖m ^ 2 * ((D : ℂ) * ntr (M * dM * M * Ea D N a) - m ^ 3)‖ ≤ 4 * κ := by
      rw [norm_mul, norm_pow]
      have hm2 : ‖m‖ ^ 2 ≤ 1 := pow_le_one₀ hm0 hm
      nlinarith [hq a, norm_nonneg ((D : ℂ) * ntr (M * dM * M * Ea D N a) - m ^ 3)]
    linarith
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  obtain ⟨wb, hwbd⟩ : ∃ wb : ℂ, wb = ∑ y, (D : ℂ) * ntr (dM * dM * Ea D N y) *
      ntr (M * M * dM * Ea D N y) := ⟨_, rfl⟩
  have hwbar : (D : ℂ)⁻¹ * ∑ a, w a = wb := by
    rw [hwbd, hwd]
    simp only [hw]
    rw [Finset.sum_comm]
    have e : ∀ y, ∑ a, (D : ℂ) * ntr (dM * dM * Ea D N y) *
        ((D : ℂ) * ntr (M * Ea D N a * M * dM * Ea D N y)) =
        (D : ℂ) * ((D : ℂ) * ntr (dM * dM * Ea D N y) * ntr (M * M * dM * Ea D N y)) := by
      intro y
      have h := FC_ntr_sum_Ea' D N M (M * dM * Ea D N y)
      simp only [← Matrix.mul_assoc] at h
      rw [← Finset.mul_sum, ← Finset.mul_sum, h]; ring
    simp only [e, ← Finset.mul_sum]
    rw [← mul_assoc, inv_mul_cancel₀ hD0, one_mul]
  have hwbm : ‖wb - m ^ 5‖ ≤ (6 * D + 4) * κ := by
    rw [← hwbar]; exact FC_avg_le hD _ _ _ hwa
  have hwd' : ∀ a, ‖w a - wb‖ ≤ 2 * (6 * D + 4) * κ := fun a => by
    calc ‖w a - wb‖ = ‖(w a - m ^ 5) - (wb - m ^ 5)‖ := by ring_nf
      _ ≤ ‖w a - m ^ 5‖ + ‖wb - m ^ 5‖ := norm_sub_le _ _
      _ ≤ 2 * (6 * D + 4) * κ := by linarith [hwa a, hwbm]
  have hP1 : ∀ x, ∑ c, PTheta D θ x c = 1 := by
    intro x
    simp only [PTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      smul_eq_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
    ring
  have hRw : ∀ c, (R *ᵥ w) c = (R *ᵥ (w - fun (_ : Fin D) => wb)) c + wb * sR := by
    intro c
    have : R *ᵥ w = R *ᵥ (w - fun (_ : Fin D) => wb) + wb • (R *ᵥ fun _ => 1) := by
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add]
      congr 1; funext a; simp
    rw [this, hR1]; simp
  have hsum : ∑ x, ∑ c, PTheta D θ x c * (R *ᵥ w) c * ntr (Ea D N x * M * B * M) =
      (∑ x, (∑ c, PTheta D θ x c * (R *ᵥ (w - fun (_ : Fin D) => wb)) c * ntr (Ea D N x * M * B * M))) +
        wb * sR * ntr (M * M * B) := by
    simp only [hRw, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [← FC_ntr_MBM, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, hP1 x]; ring
  have hlead : FC_leadM M B = ∑ y, (D : ℂ) * ntr (dM * dM * Ea D N y) *
      ntr (M * B * M * dM * Ea D N y) := by
    unfold FC_leadM; rw [← hdMd]
  have h15 : FC_lead15M M B = ntr (dM * dM) * ((∑ y, ntr (M * B * M * dM * Ea D N y)) +
      (∑ y, ntr (M * M * dM * Ea D N y)) * ntr (M * M * B) * sR) := by
    unfold FC_lead15M
    rw [← hdMd, FC_ntr_sum_Ea, FC_ntr_sum_Ea, hsR, div_eq_mul_inv]
  have hdec : FC_leadM M B + (∑ x, (∑ c, PTheta D θ x c * (R *ᵥ w) c *
      ntr (Ea D N x * M * B * M))) - FC_lead15M M B =
      (∑ y, ((D : ℂ) * ntr (dM * dM * Ea D N y) - ntr (dM * dM)) *
          ntr (M * B * M * dM * Ea D N y)) +
        (∑ y, ((D : ℂ) * ntr (dM * dM * Ea D N y) - ntr (dM * dM)) *
          ntr (M * M * dM * Ea D N y)) * sR * ntr (M * M * B) +
        ∑ x, ∑ c, PTheta D θ x c * (R *ᵥ (w - fun (_ : Fin D) => wb)) c * ntr (Ea D N x * M * B * M) := by
    rw [hsum, hlead, h15, hwbd]
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hdec]
  have hl : ∀ y, ‖ntr (M * B * M * dM * Ea D N y)‖ ≤ 2 := by
    intro y
    refine (FC_ntr_le _).trans ?_
    have h4 := FC_op4 M B M dM (5 / 4) 1 (5 / 4) (5 / 4) hM hB hM hdM'
    have := (opNorm_mul_le (M * B * M * dM) (Ea D N y)).trans
      (mul_le_mul h4 (hE y) (FC_opNorm_nonneg _) (by norm_num))
    linarith
  have hk : ∀ y, ‖ntr (M * M * dM * Ea D N y)‖ ≤ 2 := by
    intro y
    refine (FC_ntr_le _).trans ?_
    have h4 := FC_op4 M M dM (Ea D N y) (5 / 4) (5 / 4) (5 / 4) 1 hM hM hdM' (hE y)
    linarith
  have hMMB : ‖ntr (M * M * B)‖ ≤ 2 := by
    refine (FC_ntr_le _).trans ?_
    have h4 := FC_op4 M M B 1 (5 / 4) (5 / 4) 1 1 hM hM hB FC_opNorm_one
    rw [Matrix.mul_one] at h4
    linarith
  have hn : ∀ x, ‖ntr (Ea D N x * M * B * M)‖ ≤ 2 := by
    intro x
    refine (FC_ntr_le _).trans ?_
    have h4 := FC_op4 (Ea D N x) M B M 1 (5 / 4) 1 (5 / 4) (hE x) hM hB hM
    linarith
  have hT1 : ‖∑ y, ((D : ℂ) * ntr (dM * dM * Ea D N y) - ntr (dM * dM)) *
      ntr (M * B * M * dM * Ea D N y)‖ ≤ 12 * D * κ := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _y : Fin D, 6 * κ * 2 := Finset.sum_le_sum fun y _ => by
          rw [norm_mul]; exact mul_le_mul (hdx y) (hl y) (norm_nonneg _) (by positivity)
      _ = 12 * D * κ := by simp; ring
  have hT3 : ‖(∑ y, ((D : ℂ) * ntr (dM * dM * Ea D N y) - ntr (dM * dM)) *
      ntr (M * M * dM * Ea D N y)) * sR * ntr (M * M * B)‖ ≤ 24 * D * ‖sR‖ * κ := by
    rw [norm_mul, norm_mul]
    have hs1 : ‖∑ y, ((D : ℂ) * ntr (dM * dM * Ea D N y) - ntr (dM * dM)) *
        ntr (M * M * dM * Ea D N y)‖ ≤ 12 * D * κ := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ _y : Fin D, 6 * κ * 2 := Finset.sum_le_sum fun y _ => by
            rw [norm_mul]; exact mul_le_mul (hdx y) (hk y) (norm_nonneg _) (by positivity)
        _ = 12 * D * κ := by simp; ring
    have := norm_nonneg sR
    calc _ ≤ 12 * D * κ * ‖sR‖ * 2 := by gcongr
      _ = _ := by ring
  have hRu : ∀ c, ‖(R *ᵥ (w - fun (_ : Fin D) => wb)) c‖ ≤
      opNorm R * (Real.sqrt D * (2 * (6 * D + 4) * κ)) := by
    intro c
    have h := FC_form_le R (Pi.single c 1) (w - fun (_ : Fin D) => wb)
    have e1 : star (Pi.single c (1 : ℂ) : Fin D → ℂ) ⬝ᵥ (R *ᵥ (w - fun (_ : Fin D) => wb)) =
        (R *ᵥ (w - fun (_ : Fin D) => wb)) c := by simp [dotProduct, Pi.single_apply]
    rw [e1] at h
    refine h.trans ?_
    have hs1 : Real.sqrt (∑ k, ‖(Pi.single c (1 : ℂ) : Fin D → ℂ) k‖ ^ 2) ≤ 1 :=
      Real.sqrt_le_one.mpr (by
        rw [Finset.sum_eq_single c]
        · simp
        · intro b _ hb; simp [Pi.single_apply, hb]
        · simp)
    have hs2 : Real.sqrt (∑ k, ‖(w - fun (_ : Fin D) => wb) k‖ ^ 2) ≤
        Real.sqrt D * (2 * (6 * D + 4) * κ) := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * (6 * D + 4) * κ),
        ← Real.sqrt_mul (Nat.cast_nonneg _)]
      refine Real.sqrt_le_sqrt ?_
      calc ∑ k, ‖(w - fun (_ : Fin D) => wb) k‖ ^ 2 ≤ ∑ _k : Fin D, (2 * (6 * D + 4) * κ) ^ 2 :=
            Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (by
              simpa using hwd' k) 2
        _ = D * (2 * (6 * D + 4) * κ) ^ 2 := by simp
    have hR0 := FC_opNorm_nonneg R
    calc opNorm R * Real.sqrt (∑ k, ‖(Pi.single c (1 : ℂ) : Fin D → ℂ) k‖ ^ 2) *
          Real.sqrt (∑ k, ‖(w - fun (_ : Fin D) => wb) k‖ ^ 2) ≤
          opNorm R * 1 * (Real.sqrt D * (2 * (6 * D + 4) * κ)) := by gcongr
      _ = _ := by ring
  have hT2 : ‖∑ x, ∑ c, PTheta D θ x c * (R *ᵥ (w - fun (_ : Fin D) => wb)) c *
      ntr (Ea D N x * M * B * M)‖ ≤ 4 * D * Real.sqrt D * (6 * D + 4) * opNorm R * κ := by
    have hK : 0 ≤ opNorm R * (Real.sqrt D * (2 * (6 * D + 4) * κ)) := by
      have := FC_opNorm_nonneg R; positivity
    calc _ ≤ ∑ x, ∑ c, ‖PTheta D θ x c‖ * (opNorm R * (Real.sqrt D * (2 * (6 * D + 4) * κ))) *
          2 := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
          rw [norm_mul, norm_mul]
          gcongr
          · exact hRu c
          · exact hn x
      _ = ∑ x : Fin D, (opNorm R * (Real.sqrt D * (2 * (6 * D + 4) * κ))) * 2 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_mul, ← Finset.sum_mul, FC_PTheta_row D hD θ h0 h1 x, one_mul]
      _ = _ := by simp; ring
  calc _ ≤ ‖(∑ y, ((D : ℂ) * ntr (dM * dM * Ea D N y) - ntr (dM * dM)) *
          ntr (M * B * M * dM * Ea D N y)) +
        (∑ y, ((D : ℂ) * ntr (dM * dM * Ea D N y) - ntr (dM * dM)) *
          ntr (M * M * dM * Ea D N y)) * sR * ntr (M * M * B)‖ +
        ‖∑ x, ∑ c, PTheta D θ x c * (R *ᵥ (w - fun (_ : Fin D) => wb)) c *
          ntr (Ea D N x * M * B * M)‖ := norm_add_le _ _
    _ ≤ 12 * D * κ + 24 * D * ‖sR‖ * κ + 4 * D * Real.sqrt D * (6 * D + 4) * opNorm R * κ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hT1 hT3)
    _ = _ := by ring

end

section

private theorem FC_D110 : FC_Dpq 1 1 0 = [[((0, 1, false, false), false, false),
    ((0, 1, true, true), true, true)]] := by decide

private theorem FC_D101 : FC_Dpq 1 0 1 = [[((0, 1, false, false), false, true),
    ((0, 1, true, true), false, true)]] := by decide

private theorem FC_D121 : (FC_Dpq 1 2 1).filter (fun m => FC_offc m == 0) =
    [[((0, 1, false, false), false, false), ((0, 1, true, false), true, true),
      ((0, 1, true, false), false, false), ((0, 1, true, true), true, true)],
     [((0, 1, false, false), false, false), ((0, 1, true, false), true, true),
      ((0, 1, true, false), false, false), ((0, 1, true, true), true, true)]] := by decide

section FC_one
variable {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (ξ : ℂ)
  (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N)

private theorem FC_eval110 : FC_evalPoly h [(1, Λ, ξ)] X i j (FC_Dpq 1 1 0) =
    res (Matrix.of h + Λ) ξ i i * (res (Matrix.of h + Λ) ξ * X) j j := by
  rw [FC_D110]
  simp [FC_evalPoly, FC_evalMono, FC_evalFac, FC_seg1, FC_idx]

private theorem FC_eval101 : FC_evalPoly h [(1, Λ, ξ)] X i j (FC_Dpq 1 0 1) =
    res (Matrix.of h + Λ) ξ i j * (res (Matrix.of h + Λ) ξ * X) i j := by
  rw [FC_D101]
  simp [FC_evalPoly, FC_evalMono, FC_evalFac, FC_seg1, FC_idx]

private theorem FC_eval121 : FC_evalPoly h [(1, Λ, ξ)] X i j
    ((FC_Dpq 1 2 1).filter (fun m => FC_offc m == 0)) =
    2 * (res (Matrix.of h + Λ) ξ i i ^ 2 * res (Matrix.of h + Λ) ξ j j *
      (res (Matrix.of h + Λ) ξ * X) j j) := by
  rw [FC_D121]
  simp [FC_evalPoly, FC_evalMono, FC_evalFac, FC_seg1, FC_idx]
  ring

end FC_one

private theorem FC_sum_varProf (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (R Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i, ∑ j, (varProf D N θ i j : ℂ) * (R i i * Y j j) =
      ((D : ℂ) * N) * ntr (sTheta D N θ R * Y) := by
  rw [FC_sTheta_diag D N hD θ R]
  unfold ntr
  rw [← mul_assoc, show (Fintype.card (Idx D N) : ℂ) = (D : ℂ) * N by simp,
    mul_inv_cancel₀ (by
      have h1 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
      have h2 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      exact mul_ne_zero h1 h2), one_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : varProf D N θ i j = varProf D N θ j i := by
    unfold varProf; by_cases h : i.1 = j.1
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this]; ring

end

section

private theorem FC_aesm_res {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)}
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (ξ : ℂ) (hξ : ξ.im ≠ 0) (f : Matrix (Idx D N) (Idx D N) ℂ → ℂ)
    (hf : Continuous f) :
    AEStronglyMeasurable (fun h => f (res (Matrix.of h + Λ) ξ)) μ := by
  have hc : Continuous (fun h : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h) + Λ) ξ) :=
    continuous_pi fun x => continuous_pi fun y =>
      (contDiff_res_symArr Λ hΛ ξ hξ x y 0).continuous
  refine (hf.comp hc).aestronglyMeasurable.congr ?_
  filter_upwards [hμh] with h hh
  simp only [Function.comp, symArr_of_isHermitian h hh]

private theorem FC_int_of_bound {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)} [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (f : (Idx D N → Idx D N → ℂ) → ℂ)
    (hf : AEStronglyMeasurable f μ) (K : ℝ)
    (hb : ∀ h, (Matrix.of h).IsHermitian → ‖f h‖ ≤ K) : Integrable f μ :=
  (integrable_const K).mono' hf (by filter_upwards [hμh] with h hh; exact hb h hh)

private theorem FC_ntr_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    ntr (A + B) = ntr A + ntr B := by unfold ntr; rw [Matrix.trace_add, mul_add]

private theorem FC_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (A : Matrix ι ι ℂ) :
    ntr (c • A) = c * ntr A := by unfold ntr; rw [Matrix.trace_smul, smul_eq_mul]; ring

private theorem FC_ntr_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι ℂ) :
    ntr (∑ k ∈ s, A k) = ∑ k ∈ s, ntr (A k) := by
  unfold ntr; rw [Matrix.trace_sum, Finset.mul_sum]

private theorem FC_ntr_sTheta (D N : ℕ) (hD : 1 ≤ D) (θ : ℝ) (R Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr (sTheta D N θ R * Y) = ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr (R * Ea D N c)) *
      ntr (Ea D N x * Y) := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hR : ∑ c, ntr (R * Ea D N c) = ntr R := FC_ntr_sum_Ea D N R
  have hY : ∑ x, ntr (Ea D N x * Y) = ntr Y := by
    have := FC_ntr_sum_Ea' D N 1 Y; simpa using this
  have hA : ntr (sTheta D N θ R * Y) = (θ : ℂ) * (∑ a, (D : ℂ) * ntr (R * Ea D N a) *
      ntr (Ea D N a * Y)) + ((1 - θ : ℝ) : ℂ) * (ntr R * ntr Y) := by
    have h1 : ntr ((∑ a, ((D : ℂ) * ntr (R * Ea D N a)) • Ea D N a) * Y) =
        ∑ a, (D : ℂ) * ntr (R * Ea D N a) * ntr (Ea D N a * Y) := by
      rw [Finset.sum_mul, FC_ntr_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Matrix.smul_mul, FC_ntr_smul]
    have h2 : ntr ((ntr R • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * Y) = ntr R * ntr Y := by
      rw [Matrix.smul_mul, Matrix.one_mul, FC_ntr_smul]
    unfold sTheta
    rw [Matrix.add_mul, FC_ntr_add, Matrix.smul_mul, FC_ntr_smul, Matrix.smul_mul, FC_ntr_smul,
      h1, h2]
  rw [hA]
  have hP : ∀ x c, PTheta D θ x c = (if x = c then (θ : ℂ) else 0) + ((1 - θ : ℝ) : ℂ) / D := by
    intro x c
    simp only [PTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  simp only [hP, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  congr 1
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  · have e : ∀ x c, ((1 - θ : ℝ) : ℂ) / D * ((D : ℂ) * ntr (R * Ea D N c)) *
        ntr (Ea D N x * Y) = ((1 - θ : ℝ) : ℂ) * (ntr (R * Ea D N c) * ntr (Ea D N x * Y)) := by
      intro x c; field_simp
    simp only [e, ← Finset.mul_sum]
    congr 1
    rw [← hR, ← hY, Finset.sum_mul_sum, Finset.sum_comm]

private theorem FC_box_compact {ι : Type*} [Fintype ι] (r : ℝ) :
    IsCompact {G : Matrix ι ι ℂ | ∀ i j, ‖G i j‖ ≤ r} := by
  have : {G : Matrix ι ι ℂ | ∀ i j, ‖G i j‖ ≤ r} =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => Metric.closedBall (0 : ℂ) r)) := by
    ext G
    constructor
    · intro hG i _ j _
      simpa [Metric.mem_closedBall, dist_zero_right] using hG i j
    · intro hG i j
      have := hG i (Set.mem_univ _) j (Set.mem_univ _)
      simpa [Metric.mem_closedBall, dist_zero_right] using this
  rw [this]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _

private theorem FC_int_cont {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)} [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (ξ : ℂ) (hξ : ξ = z ∨ ξ = star z)
    (f : Matrix (Idx D N) (Idx D N) ℂ → ℂ) (hf : Continuous f) :
    Integrable (fun h => f (res (Matrix.of h + Λ) ξ)) μ := by
  have hξ0 : ξ.im ≠ 0 := by
    rcases hξ with rfl | rfl
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  obtain ⟨K, hK⟩ := (FC_box_compact (ι := Idx D N) (z.im)⁻¹).exists_bound_of_continuousOn
    hf.continuousOn
  refine FC_int_of_bound hμh _ (FC_aesm_res hμh Λ hΛ ξ hξ0 f hf) K fun h hh => hK _ ?_
  intro x y
  exact (norm_apply_le_opNorm _ x y).trans (FC_opNorm_res _ (hh.add hΛ) z hz ξ hξ)

private theorem FC_int_cont2 {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)} [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (ξ₁ ξ₂ : ℂ) (h₁ : ξ₁ = z ∨ ξ₁ = star z)
    (h₂ : ξ₂ = z ∨ ξ₂ = star z)
    (f : Matrix (Idx D N) (Idx D N) ℂ × Matrix (Idx D N) (Idx D N) ℂ → ℂ) (hf : Continuous f) :
    Integrable (fun h => f (res (Matrix.of h + Λ) ξ₁, res (Matrix.of h + Λ) ξ₂)) μ := by
  have him : ∀ ξ : ℂ, (ξ = z ∨ ξ = star z) → ξ.im ≠ 0 := by
    rintro ξ (rfl | rfl)
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  obtain ⟨K, hK⟩ := ((FC_box_compact (ι := Idx D N) (z.im)⁻¹).prod
    (FC_box_compact (ι := Idx D N) (z.im)⁻¹)).exists_bound_of_continuousOn hf.continuousOn
  have hc : ∀ ξ : ℂ, ξ.im ≠ 0 → Continuous (fun h : Idx D N → Idx D N → ℂ =>
      res (Matrix.of (symArr h) + Λ) ξ) := fun ξ hξ =>
    continuous_pi fun x => continuous_pi fun y =>
      (contDiff_res_symArr Λ hΛ ξ hξ x y 0).continuous
  have hm : AEStronglyMeasurable (fun h => f (res (Matrix.of h + Λ) ξ₁,
      res (Matrix.of h + Λ) ξ₂)) μ := by
    refine (hf.comp ((hc ξ₁ (him ξ₁ h₁)).prodMk (hc ξ₂ (him ξ₂ h₂)))).aestronglyMeasurable.congr ?_
    filter_upwards [hμh] with h hh
    simp only [Function.comp, symArr_of_isHermitian h hh]
  refine FC_int_of_bound hμh _ hm K fun h hh => hK _ ⟨fun x y => ?_, fun x y => ?_⟩
  · exact (norm_apply_le_opNorm _ x y).trans (FC_opNorm_res _ (hh.add hΛ) z hz ξ₁ h₁)
  · exact (norm_apply_le_opNorm _ x y).trans (FC_opNorm_res _ (hh.add hΛ) z hz ξ₂ h₂)

private theorem FC_cont_ntr {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℂ → Matrix ι ι ℂ) (hY : Continuous Y) :
    Continuous (fun G => ntr (Y G)) := by
  unfold ntr; exact continuous_const.mul hY.matrix_trace

private theorem FC_cont_sTheta (D N : ℕ) (hD : 1 ≤ D) (θ : ℝ) (Y : Matrix (Idx D N) (Idx D N) ℂ →
    Matrix (Idx D N) (Idx D N) ℂ) (hY : Continuous Y) (Z : Matrix (Idx D N) (Idx D N) ℂ →
    Matrix (Idx D N) (Idx D N) ℂ) (hZ : Continuous Z) :
    Continuous (fun G => ntr (sTheta D N θ (Y G) * Z G)) := by
  have e : (fun G => ntr (sTheta D N θ (Y G) * Z G)) = fun G =>
      ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr (Y G * Ea D N c)) * ntr (Ea D N x * Z G) := by
    funext G; exact FC_ntr_sTheta D N hD θ (Y G) (Z G)
  rw [e]
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun c _ => ?_
  exact (continuous_const.mul (continuous_const.mul (FC_cont_ntr _ (hY.matrix_mul
    continuous_const)))).mul (FC_cont_ntr _ (continuous_const.matrix_mul hZ))

end

section

private theorem FC_ntr_cyc {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) : ntr (A * B) = ntr (B * A) := by
  unfold ntr; rw [Matrix.trace_mul_comm]

private theorem FC_path1 (D N : ℕ) (hD : 2 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (ξ : ℂ) (hξ : ξ.im ≠ 0)
    (B : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) * B) =
      -ntr (hgUnder D N θ (Matrix.of h) (lam D N A) ξ * (B * MExt (lam D N A) ξ)) +
        ntr (sTheta D N θ (res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) *
          res (Matrix.of h + lam D N A) ξ * (B * MExt (lam D N A) ξ)) := by
  have hid := congrArg (fun Y => ntr (Y * B)) (FC_GmM D N hD hN θ A (Matrix.of h) hh ξ hξ)
  rw [hid, Matrix.add_mul, FC_ntr_add, Matrix.neg_mul]
  have e1 : ntr (-(MExt (lam D N A) ξ * hgUnder D N θ (Matrix.of h) (lam D N A) ξ) * B) =
      -ntr (hgUnder D N θ (Matrix.of h) (lam D N A) ξ * (B * MExt (lam D N A) ξ)) := by
    unfold ntr
    rw [Matrix.neg_mul, Matrix.trace_neg, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc]
    ring
  have e2 : ntr (MExt (lam D N A) ξ * sTheta D N θ (res (Matrix.of h + lam D N A) ξ -
      MExt (lam D N A) ξ) * res (Matrix.of h + lam D N A) ξ * B) =
      ntr (sTheta D N θ (res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) *
        res (Matrix.of h + lam D N A) ξ * (B * MExt (lam D N A) ξ)) := by
    unfold ntr
    rw [show MExt (lam D N A) ξ * sTheta D N θ (res (Matrix.of h + lam D N A) ξ -
      MExt (lam D N A) ξ) * res (Matrix.of h + lam D N A) ξ * B = MExt (lam D N A) ξ *
        (sTheta D N θ (res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) *
          res (Matrix.of h + lam D N A) ξ * B) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [Matrix.neg_mul] at e1
  rw [e1, e2]

private theorem FC_ntr_HGX {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr (Matrix.of h * Y) = (((D : ℂ) * N))⁻¹ * ∑ i, ∑ j, Y i j * starRingEnd ℂ (h i j) := by
  unfold ntr
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : starRingEnd ℂ (h i j) = h j i := by
    have := hh.apply j i
    simpa [Complex.star_def] using this
  rw [this]; ring

private theorem FC_lead1_eq (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (ξ : ℂ) (X : Matrix (Idx D N) (Idx D N) ℂ) :
    FC_lead (ouMatLaw D N L t) [(1, Λ, ξ)] X =
      -(((Real.exp (-(2 * t)) / (N : ℝ) ^ 2 : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2) *
        ∑ i, ∑ j, (if i.1 = j.1 ∧ i ≠ j then ∫ h, res (Matrix.of h + Λ) ξ i i ^ 2 *
          res (Matrix.of h + Λ) ξ j j * (res (Matrix.of h + Λ) ξ * X) j j ∂(ouMatLaw D N L t)
          else 0) := by
  unfold FC_lead
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlen : ([(1, Λ, ξ)] : FC_Ch D N).length = 1 := rfl
  by_cases hij : i ≠ j
  · rw [if_pos hij]
    simp only [hlen, FC_eval121]
    by_cases hb : i.1 = j.1
    · rw [(ouMatLaw_ccum D N L t i j).2 hb hij, if_pos ⟨hb, hij⟩, integral_const_mul]
      norm_num
      ring
    · rw [(ouMatLaw_ccum D N L t i j).1 hb 2 (1 + 1) (by norm_num), if_neg (fun h => hb h.1)]
      simp
  · rw [if_neg hij, if_neg (fun h => hij h.2)]; simp

private theorem FC_leadM_eq (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (M B : Matrix (Idx D N) (Idx D N) ℂ) :
    FC_leadM M B = ((N : ℂ)⁻¹ * ((D : ℂ) * N)⁻¹) *
      ∑ i, ∑ j, (if i.1 = j.1 then M i i ^ 2 * M j j * (M * B * M) j j else 0) := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold FC_leadM
  have e1 : ∀ y, (D : ℂ) * ntr (FC_diagM M * FC_diagM M * Ea D N y) =
      (N : ℂ)⁻¹ * ∑ i, (if i.1 = y then M i i ^ 2 else 0) := by
    intro y
    rw [FC_ntr_Ea, ← mul_assoc, show (D : ℂ) * ((D : ℂ) * N)⁻¹ = (N : ℂ)⁻¹ by field_simp]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [FC_diagM, Matrix.diagonal_apply, sq]
  have e2 : ∀ y, ntr (M * B * M * FC_diagM M * Ea D N y) =
      ((D : ℂ) * N)⁻¹ * ∑ j, (if j.1 = y then M j j * (M * B * M) j j else 0) := by
    intro y
    rw [FC_ntr_Ea]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · simp [FC_diagM, Matrix.mul_diagonal]; ring
    · rfl
  simp only [e1, e2]
  have key : ∀ i j : Idx D N, ∑ y : Fin D, (if i.1 = y then M i i ^ 2 else 0) *
      (if j.1 = y then M j j * (M * B * M) j j else 0) =
      if i.1 = j.1 then M i i ^ 2 * M j j * (M * B * M) j j else 0 := by
    intro i j
    rw [Finset.sum_eq_single i.1]
    · by_cases hb : i.1 = j.1
      · rw [if_pos rfl, if_pos hb.symm, if_pos hb]; ring
      · rw [if_pos rfl, if_neg (Ne.symm hb), if_neg hb]; ring
    · intro y _ hy; rw [if_neg (Ne.symm hy), zero_mul]
    · simp
  have e3 : ∀ y : Fin D, (N : ℂ)⁻¹ * (∑ i, (if i.1 = y then M i i ^ 2 else 0)) *
      (((D : ℂ) * N)⁻¹ * ∑ j, (if j.1 = y then M j j * (M * B * M) j j else 0)) =
      ((N : ℂ)⁻¹ * ((D : ℂ) * N)⁻¹) * ∑ i, ∑ j, (if i.1 = y then M i i ^ 2 else 0) *
        (if j.1 = y then M j j * (M * B * M) j j else 0) := by
    intro y
    rw [show ∀ (a b S T : ℂ), (a * S) * (b * T) = (a * b) * (S * T) from fun a b S T => by ring,
      Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun y _ => e3 y, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => key i j

private theorem FC_int_res {D N : ℕ} {μ : Measure (Idx D N → Idx D N → ℂ)} [IsProbabilityMeasure μ]
    (hμh : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (ξ : ℂ) (hξ : ξ = z ∨ ξ = star z)
    (f : Matrix (Idx D N) (Idx D N) ℂ → ℂ) (hf : Continuous f) (K : ℝ)
    (hK : ∀ G : Matrix (Idx D N) (Idx D N) ℂ, opNorm G ≤ (z.im)⁻¹ → ‖f G‖ ≤ K) :
    Integrable (fun h => f (res (Matrix.of h + Λ) ξ)) μ := by
  have hξ0 : ξ.im ≠ 0 := by
    rcases hξ with rfl | rfl
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  refine FC_int_of_bound hμh _ (FC_aesm_res hμh Λ hΛ ξ hξ0 f hf) K fun h hh => hK _ ?_
  exact FC_opNorm_res _ (hh.add hΛ) z hz ξ hξ

private theorem FC_entry_le_inv {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (η : ℝ)
    (hG : opNorm G ≤ η) (x y : ι) : ‖G x y‖ ≤ η := (norm_apply_le_opNorm G x y).trans hG

private theorem FC_second1 (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) {C' : ℕ → ℝ} (θ : ℝ)
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C' θ μ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (ξ : ℂ) (hξ : ξ = z ∨ ξ = star z) (X : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i, ∑ j, (FC_f μ [(1, Λ, ξ)] X i j 1 0 + FC_f μ [(1, Λ, ξ)] X i j 0 1) =
      -(((D : ℂ) * N) * ∫ h, ntr (sTheta D N θ (res (Matrix.of h + Λ) ξ) *
        (res (Matrix.of h + Λ) ξ * X)) ∂μ) := by
  have hprob := hμ.prob
  have hlen : ([(1, Λ, ξ)] : FC_Ch D N).length = 1 := rfl
  have hX0 := FC_opNorm_nonneg X
  have hint : ∀ i j, Integrable (fun h => res (Matrix.of h + Λ) ξ i i *
      (res (Matrix.of h + Λ) ξ * X) j j) μ := by
    intro i j
    refine FC_int_res hμ.herm Λ hΛ z hz ξ hξ (fun G => G i i * (G * X) j j) ?_
      ((z.im)⁻¹ * ((z.im)⁻¹ * opNorm X)) fun G hG => ?_
    · exact (continuous_id.matrix_elem i i).mul
        ((continuous_id.matrix_mul continuous_const).matrix_elem j j)
    · rw [norm_mul]
      refine mul_le_mul (FC_entry_le_inv G _ hG i i) ?_ (norm_nonneg _) (inv_nonneg.2 hz.le)
      refine FC_entry_le_inv _ _ ((opNorm_mul_le _ _).trans ?_) j j
      exact mul_le_mul_of_nonneg_right hG hX0
  have hterm : ∀ i j, FC_f μ [(1, Λ, ξ)] X i j 1 0 + FC_f μ [(1, Λ, ξ)] X i j 0 1 =
      -((varProf D N θ i j : ℂ) * ∫ h, res (Matrix.of h + Λ) ξ i i *
        (res (Matrix.of h + Λ) ξ * X) j j ∂μ) := by
    intro i j
    obtain ⟨-, c11, -, c02⟩ := llClass_ccum_low D N C' θ μ hμ i j
    unfold FC_f
    simp only [hlen, FC_eval110, FC_eval101, zero_add, Nat.factorial, Nat.mul_one,
      Nat.cast_one, div_one, pow_one, c11, c02]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      ring
    · simp only [hij, ↓reduceIte, zero_mul, add_zero]
      ring
  simp only [hterm, Finset.sum_neg_distrib]
  congr 1
  have e : ∀ i j, (varProf D N θ i j : ℂ) * ∫ h, res (Matrix.of h + Λ) ξ i i *
      (res (Matrix.of h + Λ) ξ * X) j j ∂μ = ∫ h, (varProf D N θ i j : ℂ) *
        (res (Matrix.of h + Λ) ξ i i * (res (Matrix.of h + Λ) ξ * X) j j) ∂μ := fun i j =>
    (integral_const_mul _ _).symm
  simp only [e]
  rw [← integral_const_mul]
  have hsum : ∀ i, ∑ j, ∫ h, (varProf D N θ i j : ℂ) * (res (Matrix.of h + Λ) ξ i i *
      (res (Matrix.of h + Λ) ξ * X) j j) ∂μ = ∫ h, ∑ j, (varProf D N θ i j : ℂ) *
        (res (Matrix.of h + Λ) ξ i i * (res (Matrix.of h + Λ) ξ * X) j j) ∂μ := fun i =>
    (integral_finsetSum _ fun j _ => (hint i j).const_mul _).symm
  simp only [hsum]
  rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  exact FC_sum_varProf D N hD hN θ _ _

private theorem FC_point1 (D N : ℕ) (hD : 2 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (ξ : ℂ) (hξ : ξ.im ≠ 0)
    (B : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) * B) =
      -((2 : ℂ) / ((D : ℂ) * N) * ∑ i, ∑ j, (chainB h [(1, lam D N A, ξ)] *
          ((1 / 2 : ℂ) • (B * MExt (lam D N A) ξ))) i j * starRingEnd ℂ (h i j)) -
        2 * ntr (sTheta D N θ (res (Matrix.of h + lam D N A) ξ) * (res (Matrix.of h + lam D N A) ξ *
          ((1 / 2 : ℂ) • (B * MExt (lam D N A) ξ)))) +
        (∑ x, (∑ c, PTheta D θ x c * ((D : ℂ) * ntr ((res (Matrix.of h + lam D N A) ξ -
          MExt (lam D N A) ξ) * Ea D N c)) * ntr (Ea D N x * MExt (lam D N A) ξ * B *
            MExt (lam D N A) ξ))) +
        ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr ((res (Matrix.of h + lam D N A) ξ -
          MExt (lam D N A) ξ) * Ea D N c)) * ntr (Ea D N x * ((res (Matrix.of h + lam D N A) ξ -
            MExt (lam D N A) ξ) * (B * MExt (lam D N A) ξ))) := by
  have hD1 : 1 ≤ D := by omega
  rw [FC_path1 D N hD hN θ A h hh ξ hξ B]
  have hchain : chainB h [(1, lam D N A, ξ)] = res (Matrix.of h + lam D N A) ξ := by
    simp [chainB]
  rw [hchain]
  unfold hgUnder
  generalize res (Matrix.of h + lam D N A) ξ = G
  generalize MExt (lam D N A) ξ = M
  have e : ∀ Y : Matrix (Idx D N) (Idx D N) ℂ, Y * ((1 / 2 : ℂ) • (B * M)) =
      (1 / 2 : ℂ) • (Y * (B * M)) := fun Y => Matrix.mul_smul _ _ _
  have h1 : ntr ((Matrix.of h * G + sTheta D N θ G * G) * (B * M)) =
      (2 : ℂ) / ((D : ℂ) * N) * (∑ i, (∑ j, (G * ((1 / 2 : ℂ) • (B * M))) i j *
        starRingEnd ℂ (h i j))) + 2 * ntr (sTheta D N θ G * (G * ((1 / 2 : ℂ) • (B * M)))) := by
    rw [Matrix.add_mul, FC_ntr_add, Matrix.mul_assoc, FC_ntr_HGX h hh, Matrix.mul_assoc, e,
      Matrix.mul_smul, FC_ntr_smul]
    simp only [Matrix.smul_apply, smul_eq_mul]
    have e2 : ∑ i, ∑ j, 1 / 2 * (G * (B * M)) i j * starRingEnd ℂ (h i j) =
        1 / 2 * ∑ i, ∑ j, (G * (B * M)) i j * starRingEnd ℂ (h i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    field_simp
  have h2 : ntr (sTheta D N θ (G - M) * G * (B * M)) =
      (∑ x, (∑ c, PTheta D θ x c * ((D : ℂ) * ntr ((G - M) * Ea D N c)) *
        ntr (Ea D N x * M * B * M))) +
      ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr ((G - M) * Ea D N c)) *
        ntr (Ea D N x * ((G - M) * (B * M))) := by
    rw [Matrix.mul_assoc, FC_ntr_sTheta D N hD1 θ (G - M) (G * (B * M)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_add, ← FC_ntr_add]
    have : Ea D N x * M * B * M + Ea D N x * ((G - M) * (B * M)) = Ea D N x * (G * (B * M)) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [this]
  rw [h1, h2]
  ring

private theorem FC_int1 (D N : ℕ) (hD : 2 ≤ D) (hN : 1 ≤ N) {C' : ℕ → ℝ} (θ : ℝ)
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C' θ μ)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im) (ξ : ℂ) (hξ : ξ = z ∨ ξ = star z)
    (B : Matrix (Idx D N) (Idx D N) ℂ) :
    ∫ h, ntr ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) * B) ∂μ =
      -((2 : ℂ) / ((D : ℂ) * N) * ((∑ i, ∑ j, ∫ h, (chainB h [(1, lam D N A, ξ)] *
          ((1 / 2 : ℂ) • (B * MExt (lam D N A) ξ))) i j * starRingEnd ℂ (h i j) ∂μ) -
        ∑ i, ∑ j, (FC_f μ [(1, lam D N A, ξ)] ((1 / 2 : ℂ) • (B * MExt (lam D N A) ξ)) i j 1 0 +
          FC_f μ [(1, lam D N A, ξ)] ((1 / 2 : ℂ) • (B * MExt (lam D N A) ξ)) i j 0 1))) +
        (∑ x, (∑ c, PTheta D θ x c * ((D : ℂ) * ∫ h, ntr ((res (Matrix.of h + lam D N A) ξ -
          MExt (lam D N A) ξ) * Ea D N c) ∂μ) * ntr (Ea D N x * MExt (lam D N A) ξ * B *
            MExt (lam D N A) ξ))) +
        ∫ h, ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr ((res (Matrix.of h + lam D N A) ξ -
          MExt (lam D N A) ξ) * Ea D N c)) * ntr (Ea D N x * ((res (Matrix.of h + lam D N A) ξ -
            MExt (lam D N A) ξ) * (B * MExt (lam D N A) ξ))) ∂μ := by
  have hprob := hμ.prob
  have hD1 : 1 ≤ D := by omega
  have hΛ := lam_isHermitian D N A
  have hξ0 : ξ.im ≠ 0 := by
    rcases hξ with rfl | rfl
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  set Λ := lam D N A
  set M := MExt Λ ξ
  set Xs : Matrix (Idx D N) (Idx D N) ℂ := (1 / 2 : ℂ) • (B * M)
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  have hM0 := FC_opNorm_nonneg M
  have hB0 := FC_opNorm_nonneg B
  have hF : ∀ i j, Integrable (fun h => (chainB h [(1, Λ, ξ)] * Xs) i j *
      starRingEnd ℂ (h i j)) μ := by
    intro i j
    have hc : ∀ h, chainB h [(1, Λ, ξ)] = res (Matrix.of h + Λ) ξ := fun h => by simp [chainB]
    simp only [hc]
    refine Integrable.bdd_mul (c := (z.im)⁻¹ * opNorm Xs) ?_ ?_ ?_
    · have := (hμ.integrable 1 i j)
      have hm : AEStronglyMeasurable (fun h : Idx D N → Idx D N → ℂ => starRingEnd ℂ (h i j)) μ :=
        (Complex.continuous_conj.comp ((continuous_apply j).comp (continuous_apply i))
          ).aestronglyMeasurable
      refine ⟨hm, ?_⟩
      have h2 := this.2
      simpa [HasFiniteIntegral, Complex.norm_conj] using h2
    · exact FC_aesm_res hμ.herm Λ hΛ ξ hξ0 (fun G => (G * Xs) i j)
        ((continuous_id.matrix_mul continuous_const).matrix_elem i j)
    · filter_upwards [hμ.herm] with h hh
      exact FC_entry_le_inv _ _ ((opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (FC_opNorm_res _ (hh.add hΛ) z hz ξ hξ) (FC_opNorm_nonneg _))) i j
  have hcont_ntrE : ∀ (Y Z : Matrix (Idx D N) (Idx D N) ℂ), Continuous
      (fun G : Matrix (Idx D N) (Idx D N) ℂ => ntr ((G - M) * Y) * ntr (Z * ((G - M) * (B * M)))) :=
    fun Y Z => (FC_cont_ntr _ ((continuous_id.sub continuous_const).matrix_mul continuous_const)).mul
      (FC_cont_ntr _ (continuous_const.matrix_mul ((continuous_id.sub continuous_const).matrix_mul
        continuous_const)))
  have hS : Integrable (fun h => ntr (sTheta D N θ (res (Matrix.of h + Λ) ξ) *
      (res (Matrix.of h + Λ) ξ * Xs))) μ :=
    FC_int_cont hμ.herm Λ hΛ z hz ξ hξ _ (FC_cont_sTheta D N hD1 θ _ continuous_id _
      (continuous_id.matrix_mul continuous_const))
  have hE : ∀ c, Integrable (fun h => ntr ((res (Matrix.of h + Λ) ξ - M) * Ea D N c)) μ :=
    fun c => FC_int_cont hμ.herm Λ hΛ z hz ξ hξ _ (FC_cont_ntr _
      ((continuous_id.sub continuous_const).matrix_mul continuous_const))
  have hfl : Integrable (fun h => ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) *
      ntr ((res (Matrix.of h + Λ) ξ - M) * Ea D N c)) * ntr (Ea D N x *
        ((res (Matrix.of h + Λ) ξ - M) * (B * M)))) μ := by
    refine FC_int_cont hμ.herm Λ hΛ z hz ξ hξ (fun G => ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) *
      ntr ((G - M) * Ea D N c)) * ntr (Ea D N x * ((G - M) * (B * M)))) ?_
    refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun c _ => ?_
    exact (continuous_const.mul (continuous_const.mul (FC_cont_ntr _
      ((continuous_id.sub continuous_const).matrix_mul continuous_const)))).mul
      (FC_cont_ntr _ (continuous_const.matrix_mul ((continuous_id.sub continuous_const).matrix_mul
        continuous_const)))
  have hpt : ∀ᵐ h ∂μ, ntr ((res (Matrix.of h + Λ) ξ - M) * B) =
      -((2 : ℂ) / ((D : ℂ) * N) * ∑ i, ∑ j, (chainB h [(1, Λ, ξ)] * Xs) i j *
        starRingEnd ℂ (h i j)) -
        2 * ntr (sTheta D N θ (res (Matrix.of h + Λ) ξ) * (res (Matrix.of h + Λ) ξ * Xs)) +
        (∑ x, (∑ c, PTheta D θ x c * ((D : ℂ) * ntr ((res (Matrix.of h + Λ) ξ - M) * Ea D N c)) *
          ntr (Ea D N x * M * B * M))) +
        ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr ((res (Matrix.of h + Λ) ξ - M) * Ea D N c)) *
          ntr (Ea D N x * ((res (Matrix.of h + Λ) ξ - M) * (B * M))) := by
    filter_upwards [hμ.herm] with h hh
    exact FC_point1 D N hD hN θ A h hh ξ hξ0 B
  rw [integral_congr_ae hpt]
  have hI1 : Integrable (fun h => -((2 : ℂ) / ((D : ℂ) * N) * ∑ i, ∑ j,
      (chainB h [(1, Λ, ξ)] * Xs) i j * starRingEnd ℂ (h i j))) μ :=
    ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hF i j).const_mul _).neg
  have hI2 : Integrable (fun h => 2 * ntr (sTheta D N θ (res (Matrix.of h + Λ) ξ) *
      (res (Matrix.of h + Λ) ξ * Xs))) μ := hS.const_mul _
  have hI3 : Integrable (fun h => ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) *
      ntr ((res (Matrix.of h + Λ) ξ - M) * Ea D N c)) * ntr (Ea D N x * M * B * M)) μ :=
    integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun c _ =>
      (((hE c).const_mul _).const_mul _).mul_const _
  rw [integral_add (f := fun h => -((2 : ℂ) / ((D : ℂ) * N) * ∑ i, ∑ j,
      (chainB h [(1, Λ, ξ)] * Xs) i j * starRingEnd ℂ (h i j)) -
        2 * ntr (sTheta D N θ (res (Matrix.of h + Λ) ξ) * (res (Matrix.of h + Λ) ξ * Xs)) +
        ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr ((res (Matrix.of h + Λ) ξ - M) * Ea D N c)) *
          ntr (Ea D N x * M * B * M)) ((hI1.sub hI2).add hI3) hfl,
    integral_add (f := fun h => -((2 : ℂ) / ((D : ℂ) * N) * ∑ i, ∑ j,
      (chainB h [(1, Λ, ξ)] * Xs) i j * starRingEnd ℂ (h i j)) -
        2 * ntr (sTheta D N θ (res (Matrix.of h + Λ) ξ) * (res (Matrix.of h + Λ) ξ * Xs)))
      (hI1.sub hI2) hI3,
    integral_sub hI1 hI2, integral_neg, integral_const_mul, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hF i j, integral_const_mul]
  simp only [integral_finsetSum _ fun j _ => hF _ j]
  rw [FC_second1 D N hD1 hN θ hμ Λ hΛ z hz ξ hξ Xs]
  have h3 : ∫ h, ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr ((res (Matrix.of h + Λ) ξ - M) *
      Ea D N c)) * ntr (Ea D N x * M * B * M) ∂μ = ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) *
        ∫ h, ntr ((res (Matrix.of h + Λ) ξ - M) * Ea D N c) ∂μ) * ntr (Ea D N x * M * B * M) := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun c _ => ?_
        rw [integral_mul_const, integral_const_mul, integral_const_mul]
      · intro c _; exact (((hE c).const_mul _).const_mul _).mul_const _
    · intro x _
      exact integrable_finsetSum _ fun c _ => (((hE c).const_mul _).const_mul _).mul_const _
  rw [h3]
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp
  ring

end

section

private theorem FC_opNorm_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) :
    opNorm (A - B) ≤ opNorm A + opNorm B := by
  rw [sub_eq_add_neg]
  refine (opNorm_add_le _ _).trans (le_of_eq ?_)
  rw [show -B = (-1 : ℂ) • B by simp, opNorm_smul]; simp

private theorem FC_card_same (D N : ℕ) :
    ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then (1 : ℝ) else 0) = D * N * N := by
  have : ∀ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then (1 : ℝ) else 0) = N := by
    intro i
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i.1]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast; ring

private theorem FC_tele4 (a b c a' b' c' : ℂ) (δ : ℝ) (ha : ‖a‖ ≤ 3) (hb : ‖b‖ ≤ 3) (hc : ‖c‖ ≤ 3)
    (ha' : ‖a'‖ ≤ 3) (hb' : ‖b'‖ ≤ 3) (hda : ‖a - a'‖ ≤ δ) (hdb : ‖b - b'‖ ≤ δ)
    (hdc : ‖c - c'‖ ≤ δ) : ‖a ^ 2 * b * c - a' ^ 2 * b' * c'‖ ≤ 108 * δ := by
  have e : a ^ 2 * b * c - a' ^ 2 * b' * c' = (a - a') * (a + a') * b * c +
      a' ^ 2 * (b - b') * c + a' ^ 2 * b' * (c - c') := by ring
  rw [e]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hda
  have t1 : ‖(a - a') * (a + a') * b * c‖ ≤ δ * 6 * 3 * 3 := by
    rw [norm_mul, norm_mul, norm_mul]
    have : ‖a + a'‖ ≤ 6 := (norm_add_le _ _).trans (by linarith)
    gcongr
  have t2 : ‖a' ^ 2 * (b - b') * c‖ ≤ 9 * δ * 3 := by
    rw [norm_mul, norm_mul, norm_pow]
    have : ‖a'‖ ^ 2 ≤ 9 := by nlinarith [norm_nonneg a']
    gcongr
  have t3 : ‖a' ^ 2 * b' * (c - c')‖ ≤ 9 * 3 * δ := by
    rw [norm_mul, norm_mul, norm_pow]
    have : ‖a'‖ ^ 2 ≤ 9 := by nlinarith [norm_nonneg a']
    gcongr
  calc _ ≤ ‖(a - a') * (a + a') * b * c‖ + ‖a' ^ 2 * (b - b') * c‖ + ‖a' ^ 2 * b' * (c - c')‖ :=
        norm_add₃_le
    _ ≤ _ := by linarith

set_option maxHeartbeats 2000000 in
private theorem FC_P15_step1 (D N : ℕ) (hD : 2 ≤ D) (hN : 1 ≤ N) {C : ℕ → ℝ} (L : EntryLaws C)
    (t : ℝ) (ht : 0 ≤ t) {C' : ℕ → ℝ} (hμ : LLClass D N C' (Real.exp (-t)) (ouMatLaw D N L t))
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im) (hz1 : z.im ≤ 1) (ξ : ℂ)
    (hξ : ξ = z ∨ ξ = star z) (hM : opNorm (MExt (lam D N A) ξ) ≤ 5 / 4)
    (B : Matrix (Idx D N) (Idx D N) ℂ) (hB : opNorm B ≤ 1) (l k : ℕ) (Kc : ℝ)
    (hcore : ‖(∑ i, ∑ j, ∫ h, (chainB h [(1, lam D N A, ξ)] *
          ((1 / 2 : ℂ) • (B * MExt (lam D N A) ξ))) i j * starRingEnd ℂ (h i j)
            ∂(ouMatLaw D N L t)) -
        (∑ i, ∑ j, (FC_f (ouMatLaw D N L t) [(1, lam D N A, ξ)]
          ((1 / 2 : ℂ) • (B * MExt (lam D N A) ξ)) i j 1 0 +
          FC_f (ouMatLaw D N L t) [(1, lam D N A, ξ)]
            ((1 / 2 : ℂ) • (B * MExt (lam D N A) ξ)) i j 0 1)) -
        FC_lead (ouMatLaw D N L t) [(1, lam D N A, ξ)]
          ((1 / 2 : ℂ) • (B * MExt (lam D N A) ξ))‖ ≤ Kc)
    (S : Set (Idx D N → Idx D N → ℂ)) (ε : ℝ) (hε : 0 ≤ ε)
    (hSc : ouMatLaw D N L t Sᶜ ≤ ENNReal.ofReal ε) (δ δa : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hδa : 0 ≤ δa)
    (hiso : ∀ h ∈ S, (Matrix.of h).IsHermitian → FC_iso (res (Matrix.of h + lam D N A) ξ)
      (MExt (lam D N A) ξ) ((1 / 2 : ℂ) • (B * MExt (lam D N A) ξ)) δ)
    (hav1 : ∀ h ∈ S, (Matrix.of h).IsHermitian → ∀ c,
      ‖ntr ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) * Ea D N c)‖ ≤ δa)
    (hav2 : ∀ h ∈ S, (Matrix.of h).IsHermitian → ∀ x,
      ‖ntr ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) *
        ((1 / 2 : ℂ) • (B * MExt (lam D N A) ξ) * Ea D N x))‖ ≤ δa)
    (Kν : ℝ) (hKν : ‖ccum (L.νo : Measure ℂ) 2 2‖ ≤ Kν) :
    ‖(∫ h, ntr ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) * B)
        ∂(ouMatLaw D N L t)) -
      ((Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 *
        FC_leadM (MExt (lam D N A) ξ) B -
      ∑ x, ∑ c, PTheta D (Real.exp (-t)) x c * ((D : ℂ) *
        ∫ h, ntr ((res (Matrix.of h + lam D N A) ξ - MExt (lam D N A) ξ) * Ea D N c)
          ∂(ouMatLaw D N L t)) * ntr (Ea D N x * MExt (lam D N A) ξ * B * MExt (lam D N A) ξ)‖ ≤
      2 / ((D : ℝ) * N) * Kc + 2 * Kν * ((108 * δ + 4 * (z.im)⁻¹ ^ 4 * ε) / N + 3 / N ^ 2) +
        (2 * D ^ 2 * δa ^ 2 + 18 * D ^ 2 * (z.im)⁻¹ ^ 2 * ε) := by
  have hprob := hμ.prob
  have hD1 : 1 ≤ D := by omega
  have hΛ := lam_isHermitian D N A
  have hξ0 : ξ.im ≠ 0 := by
    rcases hξ with rfl | rfl
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  have hη1 : 1 ≤ (z.im)⁻¹ := one_le_inv₀ hz |>.2 hz1
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hDr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT := FC_int1 D N hD hN (Real.exp (-t)) hμ A z hz ξ hξ B
  rw [hT]
  set μ := ouMatLaw D N L t
  set Λ := lam D N A
  set M := MExt Λ ξ
  set Xs : Matrix (Idx D N) (Idx D N) ℂ := (1 / 2 : ℂ) • (B * M) with hXs
  have hM0 := FC_opNorm_nonneg M
  have hXs1 : opNorm Xs ≤ 1 := by
    rw [hXs, opNorm_smul]
    have := opNorm_mul_le B M
    have : opNorm B * opNorm M ≤ 1 * (5 / 4) := mul_le_mul hB hM hM0 zero_le_one
    norm_num
    nlinarith [FC_opNorm_nonneg (B * M)]
  set I1 := ∑ i, ∑ j, ∫ h, (chainB h [(1, Λ, ξ)] * Xs) i j * starRingEnd ℂ (h i j) ∂μ
  set Sec := ∑ i, ∑ j, (FC_f μ [(1, Λ, ξ)] Xs i j 1 0 + FC_f μ [(1, Λ, ξ)] Xs i j 0 1)
  set Ld := FC_lead μ [(1, Λ, ξ)] Xs
  set α : ℂ := ((Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2
  set Efl := ∫ h, ∑ x, ∑ c, PTheta D (Real.exp (-t)) x c * ((D : ℂ) *
    ntr ((res (Matrix.of h + Λ) ξ - M) * Ea D N c)) *
      ntr (Ea D N x * ((res (Matrix.of h + Λ) ξ - M) * (B * M))) ∂μ
  set PT := ∑ x, ∑ c, PTheta D (Real.exp (-t)) x c * ((D : ℂ) *
    ∫ h, ntr ((res (Matrix.of h + Λ) ξ - M) * Ea D N c) ∂μ) * ntr (Ea D N x * M * B * M)
  have hdec : -((2 : ℂ) / ((D : ℂ) * N) * (I1 - Sec)) + PT + Efl - α * FC_leadM M B - PT =
      -((2 : ℂ) / ((D : ℂ) * N) * (I1 - Sec - Ld)) -
        ((2 : ℂ) / ((D : ℂ) * N) * Ld + α * FC_leadM M B) + Efl := by ring
  rw [hdec]
  have h1 : ‖-((2 : ℂ) / ((D : ℂ) * N) * (I1 - Sec - Ld))‖ ≤ 2 / ((D : ℝ) * N) * Kc := by
    rw [norm_neg, norm_mul]
    have : ‖(2 : ℂ) / ((D : ℂ) * N)‖ = 2 / ((D : ℝ) * N) := by
      rw [norm_div, Complex.norm_ofNat, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    rw [this]
    exact mul_le_mul_of_nonneg_left hcore (by positivity)
  have hpair : ∀ i j : Idx D N, ‖(∫ h, res (Matrix.of h + Λ) ξ i i ^ 2 *
      res (Matrix.of h + Λ) ξ j j * (res (Matrix.of h + Λ) ξ * Xs) j j ∂μ) -
        M i i ^ 2 * M j j * (M * Xs) j j‖ ≤ 108 * δ + 4 * (z.im)⁻¹ ^ 4 * ε := by
    intro i j
    have hint : Integrable (fun h => res (Matrix.of h + Λ) ξ i i ^ 2 *
        res (Matrix.of h + Λ) ξ j j * (res (Matrix.of h + Λ) ξ * Xs) j j) μ :=
      FC_int_cont hμ.herm Λ hΛ z hz ξ hξ (fun G => G i i ^ 2 * G j j * (G * Xs) j j)
        (((continuous_id.matrix_elem i i).pow 2).mul (continuous_id.matrix_elem j j) |>.mul
          ((continuous_id.matrix_mul continuous_const).matrix_elem j j))
    have e : (∫ h, res (Matrix.of h + Λ) ξ i i ^ 2 * res (Matrix.of h + Λ) ξ j j *
        (res (Matrix.of h + Λ) ξ * Xs) j j ∂μ) - M i i ^ 2 * M j j * (M * Xs) j j =
        ∫ h, (res (Matrix.of h + Λ) ξ i i ^ 2 * res (Matrix.of h + Λ) ξ j j *
          (res (Matrix.of h + Λ) ξ * Xs) j j - M i i ^ 2 * M j j * (M * Xs) j j) ∂μ := by
      rw [integral_sub hint (integrable_const _), integral_const]; simp
    rw [e]
    have hMe : ∀ x y, ‖M x y‖ ≤ 5 / 4 := fun x y => (norm_apply_le_opNorm M x y).trans hM
    have hMXs : ∀ x y, ‖(M * Xs) x y‖ ≤ 5 / 4 := fun x y =>
      (norm_apply_le_opNorm _ x y).trans ((opNorm_mul_le _ _).trans (by nlinarith))
    refine FC_int_split _ ((hint.sub (integrable_const _)).aestronglyMeasurable) S _ _ ε
      (by positivity) (by positivity) ?_ ?_ hSc hε
    · filter_upwards [hμ.herm] with h hh hS
      obtain ⟨b1, b2, -, -, -, -⟩ := FC_iso_bounds _ (hh.add hΛ) z hz ξ hξ M Xs hM hXs1 δ hδ
        (hiso h hS hh)
      obtain ⟨i1, i2, -⟩ := hiso h hS hh
      exact FC_tele4 _ _ _ _ _ _ δ (b1 i i) (b1 j j) (b2 j j) ((hMe i i).trans (by norm_num))
        ((hMe j j).trans (by norm_num)) (i1 i i) (i1 j j) (i2 j j)
    · filter_upwards [hμ.herm] with h hh
      have hG := FC_opNorm_res _ (hh.add hΛ) z hz ξ hξ
      have g1 : ∀ x y, ‖res (Matrix.of h + Λ) ξ x y‖ ≤ (z.im)⁻¹ := fun x y =>
        FC_entry_le_inv _ _ hG x y
      have g2 : ‖(res (Matrix.of h + Λ) ξ * Xs) j j‖ ≤ (z.im)⁻¹ :=
        FC_entry_le_inv _ _ ((opNorm_mul_le _ _).trans (by nlinarith [FC_opNorm_nonneg (res (Matrix.of h + Λ) ξ)])) j j
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow, norm_mul, norm_mul, norm_pow]
      have t1 : ‖res (Matrix.of h + Λ) ξ i i‖ ^ 2 * ‖res (Matrix.of h + Λ) ξ j j‖ *
          ‖(res (Matrix.of h + Λ) ξ * Xs) j j‖ ≤ (z.im)⁻¹ ^ 4 := by
        have := pow_le_pow_left₀ (norm_nonneg _) (g1 i i) 2
        calc _ ≤ (z.im)⁻¹ ^ 2 * (z.im)⁻¹ * (z.im)⁻¹ := by gcongr; exact g1 j j
          _ = _ := by ring
      have t2 : ‖M i i‖ ^ 2 * ‖M j j‖ * ‖(M * Xs) j j‖ ≤ 3 * (z.im)⁻¹ ^ 4 := by
        have h4 : (1 : ℝ) ≤ (z.im)⁻¹ ^ 4 := one_le_pow₀ hη1
        have a1 := pow_le_pow_left₀ (norm_nonneg _) (hMe i i) 2
        have a2 : ‖M i i‖ ^ 2 * ‖M j j‖ ≤ (5 / 4) ^ 2 * (5 / 4) :=
          mul_le_mul a1 (hMe j j) (norm_nonneg _) (by positivity)
        have a3 : ‖M i i‖ ^ 2 * ‖M j j‖ * ‖(M * Xs) j j‖ ≤ (5 / 4) ^ 2 * (5 / 4) * (5 / 4) :=
          mul_le_mul a2 (hMXs j j) (norm_nonneg _) (by positivity)
        linarith
      linarith
  set α' : ℂ := ((Real.exp (-(2 * t)) / (N : ℝ) ^ 2 : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2
    with hα'd
  have hKν0 : 0 ≤ Kν := (norm_nonneg _).trans hKν
  have hα' : ‖α'‖ ≤ Kν / N ^ 2 := by
    rw [hα'd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h0 : 0 < (N : ℝ) ^ 2 := by positivity
    calc Real.exp (-(2 * t)) / (N : ℝ) ^ 2 * ‖ccum (L.νo : Measure ℂ) 2 2‖ ≤
        1 / (N : ℝ) ^ 2 * Kν := by gcongr
      _ = Kν / N ^ 2 := by ring
  have hαα : α * ((N : ℂ)⁻¹ * ((D : ℂ) * N)⁻¹) = α' * ((D : ℂ) * N)⁻¹ := by
    simp only [α, hα'd]; push_cast; field_simp
  have hMBM : ∀ j, (M * B * M) j j = 2 * (M * Xs) j j := by
    intro j
    rw [hXs, Matrix.mul_smul, Matrix.mul_assoc]
    simp
  set w : Idx D N → Idx D N → ℂ := fun i j =>
    (if i.1 = j.1 then M i i ^ 2 * M j j * (M * Xs) j j else 0) -
      (if i.1 = j.1 ∧ i ≠ j then ∫ h, res (Matrix.of h + Λ) ξ i i ^ 2 *
        res (Matrix.of h + Λ) ξ j j * (res (Matrix.of h + Λ) ξ * Xs) j j ∂μ else 0) with hw
  have hrep_eq : (2 : ℂ) / ((D : ℂ) * N) * Ld + α * FC_leadM M B =
      (2 : ℂ) / ((D : ℂ) * N) * α' * ∑ i, ∑ j, w i j := by
    have hLd : Ld = -α' * ∑ i, ∑ j, (if i.1 = j.1 ∧ i ≠ j then ∫ h, res (Matrix.of h + Λ) ξ i i ^ 2 *
        res (Matrix.of h + Λ) ξ j j * (res (Matrix.of h + Λ) ξ * Xs) j j ∂μ else 0) :=
      FC_lead1_eq D N L t Λ ξ Xs
    have hαN : α = α' * N := by
      simp only [α, hα'd]; push_cast; field_simp
    rw [hLd, FC_leadM_eq D N hD1 hN M B, hαN]
    simp only [hMBM, hw, Finset.sum_sub_distrib]
    have e2 : ∑ i, ∑ j, (if i.1 = j.1 then M i i ^ 2 * M j j * (2 * (M * Xs) j j) else 0) =
        2 * ∑ i, ∑ j, (if i.1 = j.1 then M i i ^ 2 * M j j * (M * Xs) j j else 0) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [e2]
    field_simp
    ring
  have hMe : ∀ x y, ‖M x y‖ ≤ 5 / 4 := fun x y => (norm_apply_le_opNorm M x y).trans hM
  have hMXs : ∀ x y, ‖(M * Xs) x y‖ ≤ 5 / 4 := fun x y =>
    (norm_apply_le_opNorm _ x y).trans ((opNorm_mul_le _ _).trans (by nlinarith))
  have hwb : ∀ i j, ‖w i j‖ ≤ (if i.1 = j.1 then 108 * δ + 4 * (z.im)⁻¹ ^ 4 * ε else 0) +
      (if i = j then 3 else 0) := by
    intro i j
    simp only [hw]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, ne_eq, not_true_eq_false, and_false, sub_zero]
      have hb : ‖M i i ^ 2 * M i i * (M * Xs) i i‖ ≤ 3 := by
        rw [norm_mul, norm_mul, norm_pow]
        have a1 := pow_le_pow_left₀ (norm_nonneg _) (hMe i i) 2
        have a2 : ‖M i i‖ ^ 2 * ‖M i i‖ ≤ (5 / 4) ^ 2 * (5 / 4) :=
          mul_le_mul a1 (hMe i i) (norm_nonneg _) (by positivity)
        have a3 := mul_le_mul a2 (hMXs i i) (norm_nonneg _) (by positivity)
        linarith
      have : 0 ≤ 108 * δ + 4 * (z.im)⁻¹ ^ 4 * ε := by positivity
      linarith
    · by_cases hb : i.1 = j.1
      · simp only [hb, ↓reduceIte, ne_eq, hij, not_false_eq_true, and_self, add_zero]
        rw [norm_sub_rev]
        exact hpair i j
      · simp [hb, hij]
  have hsumw : ∑ i, ∑ j, ‖w i j‖ ≤ (D * N * N) * (108 * δ + 4 * (z.im)⁻¹ ^ 4 * ε) +
      3 * (D * N) := by
    calc ∑ i, ∑ j, ‖w i j‖ ≤ ∑ i, ∑ j, ((if i.1 = j.1 then 108 * δ + 4 * (z.im)⁻¹ ^ 4 * ε
          else 0) + (if i = j then 3 else 0)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hwb i j
      _ = (∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then (1 : ℝ) else 0)) *
            (108 * δ + 4 * (z.im)⁻¹ ^ 4 * ε) + 3 * (D * N) := by
          simp only [Finset.sum_add_distrib, Finset.sum_mul]
          congr 1
          · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            split_ifs <;> simp
          · simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
              Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
      _ = _ := by rw [FC_card_same]
  have h2 : ‖(2 : ℂ) / ((D : ℂ) * N) * Ld + α * FC_leadM M B‖ ≤
      2 * Kν * ((108 * δ + 4 * (z.im)⁻¹ ^ 4 * ε) / N + 3 / N ^ 2) := by
    rw [hrep_eq, norm_mul, norm_mul]
    have hn2 : ‖(2 : ℂ) / ((D : ℂ) * N)‖ = 2 / ((D : ℝ) * N) := by
      rw [norm_div, Complex.norm_ofNat, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    rw [hn2]
    have hs := (norm_sum_le _ _).trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      norm_sum_le (Finset.univ) (fun j => w i j))
    have hs2 : ‖∑ i, ∑ j, w i j‖ ≤ (D * N * N) * (108 * δ + 4 * (z.im)⁻¹ ^ 4 * ε) +
        3 * (D * N) := hs.trans hsumw
    have hNr0 : (0 : ℝ) < N := by linarith
    calc 2 / ((D : ℝ) * N) * ‖α'‖ * ‖∑ i, ∑ j, w i j‖ ≤ 2 / ((D : ℝ) * N) * (Kν / N ^ 2) *
          ((D * N * N) * (108 * δ + 4 * (z.im)⁻¹ ^ 4 * ε) + 3 * (D * N)) := by gcongr
      _ = _ := by field_simp
  have hBM : opNorm (B * M) ≤ 5 / 4 :=
    (opNorm_mul_le _ _).trans (by nlinarith [FC_opNorm_nonneg B])
  have h3 : ‖Efl‖ ≤ 2 * D ^ 2 * δa ^ 2 + 18 * D ^ 2 * (z.im)⁻¹ ^ 2 * ε := by
    have hfl : Integrable (fun h => ∑ x, ∑ c, PTheta D (Real.exp (-t)) x c * ((D : ℂ) *
        ntr ((res (Matrix.of h + Λ) ξ - M) * Ea D N c)) *
          ntr (Ea D N x * ((res (Matrix.of h + Λ) ξ - M) * (B * M)))) μ := by
      refine FC_int_cont hμ.herm Λ hΛ z hz ξ hξ (fun G => ∑ x, ∑ c, PTheta D (Real.exp (-t)) x c *
        ((D : ℂ) * ntr ((G - M) * Ea D N c)) * ntr (Ea D N x * ((G - M) * (B * M)))) ?_
      refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun c _ => ?_
      exact (continuous_const.mul (continuous_const.mul (FC_cont_ntr _
        ((continuous_id.sub continuous_const).matrix_mul continuous_const)))).mul
        (FC_cont_ntr _ (continuous_const.matrix_mul ((continuous_id.sub continuous_const).matrix_mul
          continuous_const)))
    have hP0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
    have hP1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hrow := FC_PTheta_row D hD1 (Real.exp (-t)) hP0 hP1
    have hgen : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → ∀ G : Matrix (Idx D N) (Idx D N) ℂ,
        (∀ c, ‖ntr ((G - M) * Ea D N c)‖ ≤ a) →
        (∀ x, ‖ntr (Ea D N x * ((G - M) * (B * M)))‖ ≤ b) →
        ‖∑ x, ∑ c, PTheta D (Real.exp (-t)) x c * ((D : ℂ) * ntr ((G - M) * Ea D N c)) *
          ntr (Ea D N x * ((G - M) * (B * M)))‖ ≤ D * (D * a * b) := by
      intro a b ha hb G hA hB'
      calc _ ≤ ∑ x, ∑ c, ‖PTheta D (Real.exp (-t)) x c‖ * (D * a) * b := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
            rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
            gcongr
            · exact hA c
            · exact hB' x
        _ = ∑ _x : Fin D, D * a * b := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [← Finset.sum_mul, ← Finset.sum_mul, hrow x, one_mul]
        _ = _ := by simp
    have hcyc : ∀ (G : Matrix (Idx D N) (Idx D N) ℂ) x,
        ntr (Ea D N x * ((G - M) * (B * M))) = 2 * ntr ((G - M) * (Xs * Ea D N x)) := by
      intro G x
      rw [FC_ntr_cyc, hXs, Matrix.smul_mul, Matrix.mul_smul, FC_ntr_smul]
      simp only [Matrix.mul_assoc]
      ring
    refine (FC_int_split _ hfl.aestronglyMeasurable S (2 * D ^ 2 * δa ^ 2)
      (18 * D ^ 2 * (z.im)⁻¹ ^ 2) ε (by positivity) (by positivity) ?_ ?_ hSc hε).trans le_rfl
    · filter_upwards [hμ.herm] with h hh hS
      have := hgen δa (2 * δa) hδa (by positivity) (res (Matrix.of h + Λ) ξ) (hav1 h hS hh)
        (fun x => by
          rw [hcyc, norm_mul, Complex.norm_ofNat]
          linarith [hav2 h hS hh x])
      calc _ ≤ (D : ℝ) * (D * δa * (2 * δa)) := this
        _ = 2 * D ^ 2 * δa ^ 2 := by ring
    · filter_upwards [hμ.herm] with h hh
      have hG := FC_opNorm_res _ (hh.add hΛ) z hz ξ hξ
      have hGM : opNorm (res (Matrix.of h + Λ) ξ - M) ≤ 3 * (z.im)⁻¹ :=
        (FC_opNorm_sub_le _ _).trans (by linarith)
      have hGM0 := FC_opNorm_nonneg (res (Matrix.of h + Λ) ξ - M)
      have := hgen (3 * (z.im)⁻¹) (6 * (z.im)⁻¹) (by positivity) (by positivity)
        (res (Matrix.of h + Λ) ξ) (fun c => by
          refine (FC_ntr_le _).trans ((opNorm_mul_le _ _).trans ?_)
          calc opNorm (res (Matrix.of h + Λ) ξ - M) * opNorm (Ea D N c) ≤ 3 * (z.im)⁻¹ * 1 :=
                mul_le_mul hGM (FC_opNorm_Ea D N c) (FC_opNorm_nonneg _) (by positivity)
            _ = _ := by ring)
        (fun x => by
          refine (FC_ntr_le _).trans ((opNorm_mul_le _ _).trans ?_)
          have h2 := (opNorm_mul_le (res (Matrix.of h + Λ) ξ - M) (B * M)).trans
            (mul_le_mul hGM hBM (FC_opNorm_nonneg _) (by positivity))
          calc opNorm (Ea D N x) * opNorm ((res (Matrix.of h + Λ) ξ - M) * (B * M)) ≤
                1 * (3 * (z.im)⁻¹ * (5 / 4)) :=
                mul_le_mul (FC_opNorm_Ea D N x) h2 (FC_opNorm_nonneg _) zero_le_one
            _ ≤ 6 * (z.im)⁻¹ := by nlinarith)
      calc _ ≤ (D : ℝ) * (D * (3 * (z.im)⁻¹) * (6 * (z.im)⁻¹)) := this
        _ = 18 * D ^ 2 * (z.im)⁻¹ ^ 2 := by ring
  calc _ ≤ ‖-((2 : ℂ) / ((D : ℂ) * N) * (I1 - Sec - Ld)) -
        ((2 : ℂ) / ((D : ℂ) * N) * Ld + α * FC_leadM M B)‖ + ‖Efl‖ := norm_add_le _ _
    _ ≤ ‖-((2 : ℂ) / ((D : ℂ) * N) * (I1 - Sec - Ld))‖ +
        ‖(2 : ℂ) / ((D : ℂ) * N) * Ld + α * FC_leadM M B‖ + ‖Efl‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith [h1, h2, h3]

end

section

private theorem FC_ntr_lam (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : ntr (lam D N A) = 0 := by
  have hf : ∀ a : Fin D, ¬ fwd D a a := fun a => by unfold fwd; omega
  have h : ∀ p : Idx D N, lam D N A p p = 0 := fun p => by simp [lam, hf]
  simp [ntr, Matrix.trace, Matrix.diag, h]

private theorem FC_MExt_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : 0 < z.im) : mExt Λ z = mSol Λ z ∧ MExt Λ z = MSol Λ z := by
  have hm : mExt Λ z = mSol Λ z := by simp only [mExt, hz, ↓reduceIte]
  exact ⟨hm, by rw [MExt, MSol, hm]⟩

private theorem FC_Mfacts (τ : ℝ) (hτ : 0 < τ) : ∃ Cm : ℝ, 0 < Cm ∧ ∀ (D N : ℕ), 1 ≤ D → 1 ≤ N →
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm (lam D N A) ≤ 1 / 10 →
    ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im → ∀ z₁ : ℂ, (z₁ = z ∨ z₁ = star z) →
      opNorm (MExt (lam D N A) z₁) ≤ 5 / 4 ∧ ‖mExt (lam D N A) z₁‖ ≤ 1 ∧
        opNorm (MExt (lam D N A) z₁ - mExt (lam D N A) z₁ • 1) ≤ Cm * opNorm (lam D N A) := by
  obtain ⟨Cm, hCm, hmsc⟩ := eq_msc_traceless τ hτ
  refine ⟨Cm, hCm, fun D N hD hN A hA z hzn hz z₁ h₁ => ?_⟩
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hΛ := lam_isHermitian D N A
  obtain ⟨hm, hM⟩ := FC_MExt_pos (lam D N A) z hz
  obtain ⟨a1, a2, a3⟩ := mSol_apriori (lam D N A) hΛ hA z hz
  have hL0 := FC_opNorm_nonneg (lam D N A)
  have hb : opNorm (MExt (lam D N A) z) ≤ 5 / 4 := by
    rw [hM]
    refine a3.le.trans ?_
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hsm : ‖mExt (lam D N A) z‖ ≤ 1 := by rw [hm]; exact a2.le
  have hk : opNorm (MExt (lam D N A) z - mExt (lam D N A) z • 1) ≤ Cm * opNorm (lam D N A) := by
    have h := hmsc (Idx D N) (lam D N A) hΛ hA (FC_ntr_lam D N A) z hzn hz
    rw [hm, hM]
    have e : MSol (lam D N A) z - mSol (lam D N A) z • (1 : Matrix (Idx D N) (Idx D N) ℂ) =
        (MSol (lam D N A) z - msc z • 1) + (msc z - mSol (lam D N A) z) • 1 := by
      rw [sub_smul]; abel
    rw [e]
    refine (opNorm_add_le _ _).trans ?_
    rw [opNorm_smul]
    have := FC_opNorm_one (ι := Idx D N)
    have h0 := norm_nonneg (msc z - mSol (lam D N A) z)
    rw [norm_sub_rev] at h0 ⊢
    nlinarith
  rcases h₁ with rfl | rfl
  · exact ⟨hb, hsm, hk⟩
  · obtain ⟨c1, c2⟩ := mExt_conj (lam D N A) hΛ z hz.ne'
    rw [c1, c2]
    refine ⟨by rw [FC_opNorm_conjTranspose]; exact hb, by rw [norm_star]; exact hsm, ?_⟩
    have e : (MExt (lam D N A) z)ᴴ - star (mExt (lam D N A) z) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ) =
        (MExt (lam D N A) z - mExt (lam D N A) z • 1)ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    rw [e, FC_opNorm_conjTranspose]
    exact hk

private theorem FC_Mhat_rowsum (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (z₁ : ℂ)
    (h₁ : z₁.im ≠ 0) (a : Fin D) :
    ∑ b, Mhat (lam D N A) z₁ z₁ a b = ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₁) := by
  have : NeZero D := ⟨by omega⟩
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  set M := MExt (lam D N A) z₁
  have hrow : ∀ a' : Fin D, ∑ b, Mhat (lam D N A) z₁ z₁ a' b = (D : ℂ) * ntr (M * M * Ea D N a') := by
    intro a'
    simp only [Mhat]
    rw [← Finset.mul_sum]
    congr 1
    rw [FC_ntr_sum_Ea]
    unfold ntr
    rw [show M * Ea D N a' * M = M * (Ea D N a' * M) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show Ea D N a' * M * M = Ea D N a' * (M * M) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  have htr : ∀ a' : Fin D, ∑ b, Mhat (lam D N A) z₁ z₁ a' b = ∑ b, Mhat (lam D N A) z₁ z₁ 0 b := by
    intro a'
    calc ∑ b, Mhat (lam D N A) z₁ z₁ a' b = ∑ c, Mhat (lam D N A) z₁ z₁ a' (c + a') :=
          (Fintype.sum_equiv (Equiv.addRight a') _ _ (fun c => rfl)).symm
      _ = _ := Finset.sum_congr rfl fun b _ =>
          Mhat_translation D hD N A z₁ z₁ h₁ h₁ a' (b + a') 0 b (by simp)
  have hall : (D : ℂ) * ∑ b, Mhat (lam D N A) z₁ z₁ 0 b = (D : ℂ) * ntr (M * M) := by
    have h1 : ∑ a' : Fin D, ∑ b, Mhat (lam D N A) z₁ z₁ a' b = (D : ℂ) * ntr (M * M) := by
      simp only [hrow, ← Finset.mul_sum, FC_ntr_sum_Ea]
    rw [← h1]
    simp only [htr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [htr a]
  exact mul_left_cancel₀ hD0 hall

private theorem FC_R1 (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (z₁ : ℂ)
    (h₁ : z₁.im ≠ 0) (θ : ℝ)
    (hdet : (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ).det ≠ 0)
    (hne : 1 - ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₁) ≠ 0) :
    (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹ *ᵥ (fun _ => 1) =
      fun _ => (1 - ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₁))⁻¹ := by
  set r := ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₁)
  set R := (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹
  have hP1 : ∀ x, ∑ c, PTheta D θ x c = 1 := by
    intro x
    have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
    simp only [PTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      smul_eq_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
    ring
  have hv : (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ) *ᵥ (fun _ => 1) = fun _ => 1 - r := by
    funext a
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    have e1 : (PTheta D θ *ᵥ fun _ => (1 : ℂ)) = fun _ => 1 := by
      funext x; simp [Matrix.mulVec, dotProduct, hP1 x]
    rw [e1]
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, mul_one]
    rw [FC_Mhat_rowsum D hD N A z₁ h₁ a]
  have hRinv : R * (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
  have e : (fun _ : Fin D => (1 : ℂ)) = R *ᵥ (fun _ => 1 - r) := by
    rw [← hv, Matrix.mulVec_mulVec, hRinv, Matrix.one_mulVec]
  have e2 : (fun _ : Fin D => (1 - r)) = (1 - r) • (fun _ : Fin D => (1 : ℂ)) := by
    funext; simp
  rw [e2, Matrix.mulVec_smul] at e
  funext a
  have := congrFun e a
  simp only [Pi.smul_apply, smul_eq_mul] at this
  field_simp
  rw [mul_comm] at this
  exact this.symm

end

section

open Filter

private theorem FC_ev_ge {a : ℝ} (ha : 0 < a) (K : ℝ) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → K ≤ (N : ℝ) ^ a :=
  eventually_atTop.mp
    (((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K)

private theorem FC_ev_pow {p q : ℝ} (hpq : p < q) (K : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → K * (N : ℝ) ^ p ≤ (N : ℝ) ^ q := by
  obtain ⟨N₀, hN₀⟩ := FC_ev_ge (sub_pos.2 hpq) K
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hNp : (0 : ℝ) < N := by linarith
  have h := hN₀ N ((le_max_left _ _).trans hN)
  have e : (N : ℝ) ^ q = (N : ℝ) ^ (q - p) * (N : ℝ) ^ p := by
    rw [← Real.rpow_add hNp]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hNp.le _)

private theorem FC_ev_log (D : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ((Nat.log 2 (D * N) : ℕ) : ℝ) + 3 ≤ (N : ℝ) ^ a := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N₀, hN₀⟩ := FC_ev_pow (show a / 2 < a by linarith)
    ((D : ℝ) ^ (a / 2) / ((a / 2) * Real.log 2) + 3)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hNp : (0 : ℝ) < N := by linarith
  refine le_trans ?_ (hN₀ N ((le_max_left _ _).trans hN))
  rcases Nat.eq_zero_or_pos (D * N) with h0 | h0
  · rw [h0]; simp
    have : (0 : ℝ) ≤ (D : ℝ) ^ (a / 2) / ((a / 2) * Real.log 2) := by positivity
    nlinarith [Real.one_le_rpow hN1 (show (0 : ℝ) ≤ a / 2 by linarith)]
  have hpow : (2 : ℝ) ^ (Nat.log 2 (D * N)) ≤ ((D * N : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 h0.ne'
  have hlog : (Nat.log 2 (D * N) : ℝ) * Real.log 2 ≤ Real.log ((D * N : ℕ) : ℝ) := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  have hlr := Real.log_le_rpow_div (show (0 : ℝ) ≤ ((D * N : ℕ) : ℝ) by positivity)
    (show 0 < a / 2 by linarith)
  have hk : (Nat.log 2 (D * N) : ℝ) ≤ ((D * N : ℕ) : ℝ) ^ (a / 2) / (a / 2) / Real.log 2 := by
    rw [le_div_iff₀ hl2]; linarith
  have e : ((D * N : ℕ) : ℝ) ^ (a / 2) = (D : ℝ) ^ (a / 2) * (N : ℝ) ^ (a / 2) := by
    push_cast; rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  rw [e] at hk
  have hNa : (1 : ℝ) ≤ (N : ℝ) ^ (a / 2) := Real.one_le_rpow hN1 (by linarith)
  calc ((Nat.log 2 (D * N) : ℕ) : ℝ) + 3 ≤
      (D : ℝ) ^ (a / 2) * (N : ℝ) ^ (a / 2) / (a / 2) / Real.log 2 + 3 := by linarith
    _ ≤ ((D : ℝ) ^ (a / 2) / ((a / 2) * Real.log 2) + 3) * (N : ℝ) ^ (a / 2) := by
        rw [div_div, add_mul, show (D : ℝ) ^ (a / 2) * (N : ℝ) ^ (a / 2) / (a / 2 * Real.log 2) =
          (D : ℝ) ^ (a / 2) / (a / 2 * Real.log 2) * (N : ℝ) ^ (a / 2) by ring]
        nlinarith

private theorem FC_rem_le (c : ℝ) (hc : 1 ≤ c) (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hηl : c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ η) :
    (N : ℝ) ^ (-((24 : ℕ) + 2 : ℝ) / 2) * (6 * η⁻¹) ^ (2 + 24 + 1) +
      (1 + η⁻¹) ^ (2 + 24 + 1) *
        Real.sqrt (0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (η / 24)) ^ (-((160 : ℕ) : ℝ))) ≤
      ((6 * c) ^ 27 + (2 * c) ^ 27 * (24 * c) ^ 80) * (N : ℝ) ^ (-(4 : ℝ)) := by
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hc0 : 0 < c := by linarith
  have hηi : η⁻¹ ≤ c * (N : ℝ) ^ (1 / 3 : ℝ) := by
    have h1 : 0 < c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
    have := inv_anti₀ h1 hηl
    rw [mul_inv, inv_inv, Real.rpow_neg hx0.le, inv_inv] at this
    exact this
  have hη1' : 1 ≤ η⁻¹ := one_le_inv₀ hη |>.2 hη1
  have hx13 : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hx0.le _
  have p9 : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 27 = (N : ℝ) ^ (9 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have t1 : (6 * η⁻¹) ^ (2 + 24 + 1) ≤ (6 * c) ^ 27 * (N : ℝ) ^ (9 : ℝ) := by
    rw [← p9, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have t2 : (1 + η⁻¹) ^ (2 + 24 + 1) ≤ (2 * c) ^ 27 * (N : ℝ) ^ (9 : ℝ) := by
    rw [← p9, ← mul_pow]
    have : 1 + η⁻¹ ≤ 2 * c * (N : ℝ) ^ (1 / 3 : ℝ) := by
      have : (1 : ℝ) ≤ c * (N : ℝ) ^ (1 / 3 : ℝ) := hη1'.trans hηi
      linarith
    exact pow_le_pow_left₀ (by positivity) this _
  have hb : (N : ℝ) ^ (1 / 6 : ℝ) / (24 * c) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * (η / 24) := by
    have e : (N : ℝ) ^ (1 / 6 : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [e, div_eq_mul_inv, mul_inv]
    have : c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) / 24 ≤ η / 24 := by linarith
    have h2 : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
    calc (N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ (-(1 / 3 : ℝ)) * (24⁻¹ * c⁻¹) =
        (N : ℝ) ^ ((1 : ℝ) / 2) * (c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) / 24) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this h2
  have hb0 : 0 < (N : ℝ) ^ (1 / 6 : ℝ) / (24 * c) := by positivity
  have t3 : ((N : ℝ) ^ ((1 : ℝ) / 2) * (η / 24)) ^ (-((160 : ℕ) : ℝ)) ≤
      ((N : ℝ) ^ (1 / 6 : ℝ) / (24 * c)) ^ (-((160 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hb0 hb (by norm_num)
  have e3 : ((N : ℝ) ^ (1 / 6 : ℝ) / (24 * c)) ^ (-((160 : ℕ) : ℝ)) =
      ((24 * c) ^ 80) ^ 2 * ((N : ℝ) ^ (-(40 / 3 : ℝ))) ^ 2 := by
    rw [Real.div_rpow (Real.rpow_nonneg hx0.le _) (by positivity), ← Real.rpow_mul hx0.le,
      div_eq_mul_inv, ← Real.rpow_neg (by positivity), ← pow_mul, ← Real.rpow_natCast,
      ← Real.rpow_natCast (_ ^ _), ← Real.rpow_mul hx0.le]
    norm_num
    rw [← Real.rpow_natCast]
    norm_num
    ring_nf
  have t3' : Real.sqrt (0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (η / 24)) ^ (-((160 : ℕ) : ℝ))) ≤
      (24 * c) ^ 80 * (N : ℝ) ^ (-(40 / 3 : ℝ)) := by
    rw [zero_add]
    calc _ ≤ Real.sqrt (((24 * c) ^ 80) ^ 2 * ((N : ℝ) ^ (-(40 / 3 : ℝ))) ^ 2) :=
          Real.sqrt_le_sqrt (t3.trans (le_of_eq e3))
      _ = _ := by
          rw [← mul_pow, Real.sqrt_sq (by positivity)]
  have e1 : (N : ℝ) ^ (-((24 : ℕ) + 2 : ℝ) / 2) * (N : ℝ) ^ (9 : ℝ) = (N : ℝ) ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_add hx0]; norm_num
  have e2 : (N : ℝ) ^ (9 : ℝ) * (N : ℝ) ^ (-(40 / 3 : ℝ)) ≤ (N : ℝ) ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hn13 : 0 ≤ (N : ℝ) ^ (-((24 : ℕ) + 2 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
  calc _ ≤ (N : ℝ) ^ (-((24 : ℕ) + 2 : ℝ) / 2) * ((6 * c) ^ 27 * (N : ℝ) ^ (9 : ℝ)) +
        (2 * c) ^ 27 * (N : ℝ) ^ (9 : ℝ) * ((24 * c) ^ 80 * (N : ℝ) ^ (-(40 / 3 : ℝ))) := by
        gcongr
    _ = (6 * c) ^ 27 * ((N : ℝ) ^ (-((24 : ℕ) + 2 : ℝ) / 2) * (N : ℝ) ^ (9 : ℝ)) +
        (2 * c) ^ 27 * (24 * c) ^ 80 * ((N : ℝ) ^ (9 : ℝ) * (N : ℝ) ^ (-(40 / 3 : ℝ))) := by ring
    _ ≤ (6 * c) ^ 27 * (N : ℝ) ^ (-(4 : ℝ)) + (2 * c) ^ 27 * (24 * c) ^ 80 *
        (N : ℝ) ^ (-(4 : ℝ)) := by
        rw [e1]; gcongr
    _ = _ := by ring

private theorem FC_s_facts (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2 ∧
    (N : ℝ) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2 ∧
    (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2 ∧
    (N : ℝ) ^ (-(3 / 2 : ℝ)) ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2 := by
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hηi1 : 1 ≤ η⁻¹ := one_le_inv₀ hη |>.2 hη1
  have hp32 : 0 ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hp2 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have h2 : (N : ℝ) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hq : 1 ≤ η⁻¹ ^ 2 := one_le_pow₀ hηi1
  have a : 0 ≤ (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2 := by positivity
  have b : 0 ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ := by positivity
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · have : (N : ℝ) ^ (-(2 : ℝ)) * 1 ≤ (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_left hq hp2
    linarith
  · have : (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  · have : (N : ℝ) ^ (-(3 / 2 : ℝ)) * 1 ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ :=
      mul_le_mul_of_nonneg_left hηi1 hp32
    linarith

private theorem FC_E1 (D : ℕ) (hD : 1 ≤ D) (c : ℝ) (hc : 1 ≤ c) (Kc Kν τ'' : ℝ) (hKc : 0 ≤ Kc)
    (hKν : 0 ≤ Kν) (hτ'' : 0 < τ'') : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ η δ δa ε : ℝ, 0 < η → η ≤ 1 → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ η → 0 ≤ δ →
      δ ≤ (N : ℝ) ^ τ'' * (Real.sqrt (1 / (N * η)) + 1 / (N * η)) →
      δa = (N : ℝ) ^ τ'' * (1 / (N * η)) → 0 ≤ ε →
      ε ≤ 3 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(30 : ℝ)) + 2 * D * (N : ℝ) ^ (-(30 : ℝ)) →
        2 / ((D : ℝ) * N) * (Kc * FC_err D N 1 24 160 (Nat.log 2 (D * N) + 1) η 1 ε) +
          2 * Kν * ((108 * δ + 4 * η⁻¹ ^ 4 * ε) / N + 3 / N ^ 2) +
          (2 * D ^ 2 * δa ^ 2 + 18 * D ^ 2 * η⁻¹ ^ 2 * ε) ≤
        K₁ * (N : ℝ) ^ (2 * τ'') * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ +
          (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2) := by
  obtain ⟨KR, hKR⟩ : ∃ KR : ℝ, KR = (D : ℝ) ^ 2 * ((6 * c) ^ 27 + (2 * c) ^ 27 * (24 * c) ^ 80) :=
    ⟨_, rfl⟩
  have hKR0 : 0 ≤ KR := by rw [hKR]; positivity
  refine ⟨2 * Kc * (5 + D + KR) + 2 * Kν * 223 + 20 * D ^ 2, by positivity, ?_⟩
  obtain ⟨N₁, hN₁⟩ := FC_ev_log D hτ''
  obtain ⟨N₂, hN₂⟩ := FC_ev_pow (show (1 + 26 / 3 - 28 : ℝ) < -2 by norm_num)
    (5 * D ^ 3 * c ^ 26)
  obtain ⟨N₃, hN₃⟩ := FC_ev_pow (show (4 / 3 - 29 : ℝ) < -2 by norm_num) (5 * D ^ 2 * c ^ 4)
  obtain ⟨N₄, hN₄⟩ := FC_ev_pow (show (2 / 3 - 28 : ℝ) < -2 by norm_num) (5 * D ^ 2 * c ^ 2)
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) 1, fun N hN η δ δa ε hη hη1 hηl hδ0 hδ hδa hε0 hε => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx0 : (0 : ℝ) < N := by linarith
  have hc0 : 0 < c := by linarith
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hηi1 : 1 ≤ η⁻¹ := one_le_inv₀ hη |>.2 hη1
  have hηi : η⁻¹ ≤ c * (N : ℝ) ^ (1 / 3 : ℝ) := by
    have h1 : 0 < c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
    have := inv_anti₀ h1 hηl
    rw [mul_inv, inv_inv, Real.rpow_neg hx0.le, inv_inv] at this
    exact this
  obtain ⟨hS1, hS2, hS3, hS4⟩ := FC_s_facts N hN1 η hη hη1
  have hτp : 1 ≤ (N : ℝ) ^ τ'' := Real.one_le_rpow hx hτ''.le
  have h2τ : (N : ℝ) ^ τ'' ≤ (N : ℝ) ^ (2 * τ'') :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hε' : ε ≤ 5 * D ^ 2 * (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-(30 : ℝ)) := by
    have hp30 : 0 ≤ (N : ℝ) ^ (-(30 : ℝ)) := Real.rpow_nonneg hx0.le _
    have hx2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) ^ 2 := by rw [← Real.rpow_natCast]; norm_num
    rw [hx2]
    have hD2 : (D : ℝ) ≤ D ^ 2 := by
      have := mul_le_mul_of_nonneg_left hD1 (show (0 : ℝ) ≤ D by positivity)
      rw [sq]; linarith only [this]
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hx
    have h1 : 2 * (D : ℝ) ≤ 2 * D ^ 2 * N ^ 2 := by
      have := mul_le_mul hD2 hN2 zero_le_one (by positivity)
      linarith only [this]
    have h3 := mul_le_mul_of_nonneg_right h1 hp30
    calc ε ≤ 3 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(30 : ℝ)) + 2 * D * (N : ℝ) ^ (-(30 : ℝ)) := hε
      _ ≤ 3 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(30 : ℝ)) +
          2 * D ^ 2 * N ^ 2 * (N : ℝ) ^ (-(30 : ℝ)) := by linarith only [h3]
      _ = _ := by ring
  have hηpow : ∀ k : ℕ, η⁻¹ ^ k ≤ c ^ k * (N : ℝ) ^ ((k : ℝ) / 3) := by
    intro k
    calc η⁻¹ ^ k ≤ (c * (N : ℝ) ^ (1 / 3 : ℝ)) ^ k :=
          pow_le_pow_left₀ (inv_nonneg.2 hη.le) hηi k
      _ = _ := by
          rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 3 : ℝ)), ← Real.rpow_mul hx0.le]
          ring_nf
  have hsmall : ∀ (k : ℕ) (a b : ℝ), (c ^ k * (N : ℝ) ^ ((k : ℝ) / 3)) * (b * (5 * D ^ 2 *
      (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-(30 : ℝ)))) = (5 * b * D ^ 2 * c ^ k) *
        (N : ℝ) ^ ((k : ℝ) / 3 + 2 - 30) := by
    intro k a b
    rw [show ((k : ℝ) / 3 + 2 - 30) = (k : ℝ) / 3 + (2 + -(30 : ℝ)) by ring,
      Real.rpow_add hx0, Real.rpow_add hx0]
    ring
  have hlog := hN₁ N ((le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans hN)))
  have hrem := FC_rem_le c hc N hN1 η hη hη1 hηl
  obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ +
      (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2 := ⟨_, rfl⟩
  rw [← hSd] at hS1 hS2 hS3 hS4 ⊢
  have hS0 : 0 ≤ S := by rw [hSd]; positivity
  set T := (N : ℝ) ^ (2 * τ'') with hT
  have hT1 : 1 ≤ T := (Real.one_le_rpow hx hτ''.le).trans h2τ
  have hST : S ≤ T * S := le_mul_of_one_le_left hS0 hT1
  have hDN0 : (0 : ℝ) < D * N := by positivity
  have hp30 : 0 ≤ (N : ℝ) ^ (-(30 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hpx2 : 0 ≤ (N : ℝ) ^ (2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hεb : ∀ k : ℕ, η⁻¹ ^ k * ε ≤ (5 * D ^ 2 * c ^ k) * (N : ℝ) ^ ((k : ℝ) / 3 + 2 - 30) := by
    intro k
    calc η⁻¹ ^ k * ε ≤ (c ^ k * (N : ℝ) ^ ((k : ℝ) / 3)) *
          (5 * D ^ 2 * (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-(30 : ℝ))) :=
          mul_le_mul (hηpow k) hε' hε0 (by positivity)
      _ = _ := by
          rw [show ((k : ℝ) / 3 + 2 - 30) = (k : ℝ) / 3 + (2 + -(30 : ℝ)) by ring,
            Real.rpow_add hx0, Real.rpow_add hx0]
          ring
  have e26 : (D : ℝ) * N * (η⁻¹ ^ 26 * ε) ≤ (N : ℝ) ^ (-(2 : ℝ)) := by
    have h := hN₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans
      ((le_max_left _ _).trans hN)))
    have hk := hεb 26
    have e : (D : ℝ) * N * ((5 * D ^ 2 * c ^ 26) * (N : ℝ) ^ (((26 : ℕ) : ℝ) / 3 + 2 - 30)) =
        5 * D ^ 3 * c ^ 26 * (N : ℝ) ^ (1 + 26 / 3 - 28 : ℝ) := by
      rw [show (1 + 26 / 3 - 28 : ℝ) = 1 + (((26 : ℕ) : ℝ) / 3 + 2 - 30) by push_cast; ring,
        Real.rpow_add hx0, Real.rpow_one]
      ring
    calc _ ≤ (D : ℝ) * N * ((5 * D ^ 2 * c ^ 26) * (N : ℝ) ^ (((26 : ℕ) : ℝ) / 3 + 2 - 30)) :=
          mul_le_mul_of_nonneg_left hk hDN0.le
      _ = _ := e
      _ ≤ _ := h
  have e4 : η⁻¹ ^ 4 * ε / N ≤ (N : ℝ) ^ (-(2 : ℝ)) := by
    have h := hN₃ N ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_left _ _).trans hN)))
    have hk := hεb 4
    have e : ((5 * D ^ 2 * c ^ 4) * (N : ℝ) ^ (((4 : ℕ) : ℝ) / 3 + 2 - 30)) / N =
        5 * D ^ 2 * c ^ 4 * (N : ℝ) ^ (4 / 3 - 29 : ℝ) := by
      rw [show (4 / 3 - 29 : ℝ) = (((4 : ℕ) : ℝ) / 3 + 2 - 30) + (-1) by push_cast; ring,
        Real.rpow_add hx0, Real.rpow_neg_one]
      ring
    calc _ ≤ ((5 * D ^ 2 * c ^ 4) * (N : ℝ) ^ (((4 : ℕ) : ℝ) / 3 + 2 - 30)) / N :=
          div_le_div_of_nonneg_right hk hx0.le
      _ = _ := e
      _ ≤ _ := h
  have e2' : η⁻¹ ^ 2 * ε ≤ (N : ℝ) ^ (-(2 : ℝ)) := by
    have h := hN₄ N ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_left _ _).trans hN)))
    have hk := hεb 2
    have e : (5 * D ^ 2 * c ^ 2) * (N : ℝ) ^ (((2 : ℕ) : ℝ) / 3 + 2 - 30) =
        5 * D ^ 2 * c ^ 2 * (N : ℝ) ^ (2 / 3 - 28 : ℝ) := by
      congr 2; push_cast; ring
    linarith only [hk, h, e]
  have hFC : FC_err D N 1 24 160 (Nat.log 2 (D * N) + 1) η 1 ε ≤
      ((D : ℝ) * N) * ((4 + D + KR) * (T * S)) := by
    unfold FC_err
    simp only [Nat.sub_self, pow_zero, mul_one]
    push_cast
    have t1 : ((Nat.log 2 (D * N) : ℝ) + 1 + 2) * (D * N) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ ≤
        ((D : ℝ) * N) * (T * S) := by
      have : ((Nat.log 2 (D * N) : ℝ) + 1 + 2) ≤ T := by
        have := hlog; linarith only [this, h2τ]
      calc _ = ((D : ℝ) * N) * (((Nat.log 2 (D * N) : ℝ) + 1 + 2) *
            ((N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹)) := by ring
        _ ≤ ((D : ℝ) * N) * (T * S) := by
            gcongr
    have t2 : (D * N : ℝ) * (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ≤ ((D : ℝ) * N) * (T * S) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hS3.trans hST) hDN0.le
    have t3 : (D * N : ℝ) * (N : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ((D : ℝ) * N) * (T * S) :=
      mul_le_mul_of_nonneg_left (hS4.trans hST) hDN0.le
    have t4 : ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(5 / 2 : ℝ)) ≤ ((D : ℝ) * N) * (D * (T * S)) := by
      have e : ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(5 / 2 : ℝ)) =
          ((D : ℝ) * N) * (D * (N : ℝ) ^ (-(3 / 2 : ℝ))) := by
        rw [show (-(3 / 2 : ℝ)) = 1 + (-(5 / 2 : ℝ)) by norm_num, Real.rpow_add hx0,
          Real.rpow_one]
        ring
      rw [e]
      gcongr
      exact hS4.trans hST
    have t5 : ((D : ℝ) * N) ^ 2 * η⁻¹ ^ (24 + 2) * ε ≤ ((D : ℝ) * N) * (T * S) := by
      have e : ((D : ℝ) * N) ^ 2 * η⁻¹ ^ (24 + 2) * ε = ((D : ℝ) * N) * ((D : ℝ) * N *
          (η⁻¹ ^ 26 * ε)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (e26.trans (hS2.trans hST)) hDN0.le
    have t6 : ((D : ℝ) * N) ^ 3 * ((N : ℝ) ^ (-((24 : ℕ) + 2 : ℝ) / 2) * (6 * η⁻¹) ^ (2 + 24 + 1) +
        (1 + η⁻¹) ^ (2 + 24 + 1) *
          Real.sqrt (0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (η / 24)) ^ (-((160 : ℕ) : ℝ)))) ≤
        ((D : ℝ) * N) * (KR * (T * S)) := by
      have e : ((D : ℝ) * N) ^ 3 * (((6 * c) ^ 27 + (2 * c) ^ 27 * (24 * c) ^ 80) *
          (N : ℝ) ^ (-(4 : ℝ))) = ((D : ℝ) * N) * (KR * (N : ℝ) ^ (-(2 : ℝ))) := by
        rw [hKR, show (-(4 : ℝ)) = -(2 : ℝ) + (-(2 : ℝ)) by norm_num, Real.rpow_add hx0]
        have hN2 : (N : ℝ) ^ (-(2 : ℝ)) * (N : ℝ) ^ 2 = 1 := by
          rw [Real.rpow_neg hx0.le, ← Real.rpow_natCast]; norm_num
          exact inv_mul_cancel₀ (by positivity)
        linear_combination ((D : ℝ) ^ 3 * ((6 * c) ^ 27 + (2 * c) ^ 27 * (24 * c) ^ 80) * N *
          (N : ℝ) ^ (-(2 : ℝ))) * hN2
      calc _ ≤ ((D : ℝ) * N) ^ 3 * (((6 * c) ^ 27 + (2 * c) ^ 27 * (24 * c) ^ 80) *
            (N : ℝ) ^ (-(4 : ℝ))) := by
            gcongr
        _ = _ := e
        _ ≤ _ := by
            gcongr
            exact hS2.trans hST
    linarith only [t1, t2, t3, t4, t5, t6]
  have P1 : 2 / ((D : ℝ) * N) * (Kc * FC_err D N 1 24 160 (Nat.log 2 (D * N) + 1) η 1 ε) ≤
      2 * Kc * (4 + D + KR) * (T * S) := by
    calc _ ≤ 2 / ((D : ℝ) * N) * (Kc * (((D : ℝ) * N) * ((4 + D + KR) * (T * S)))) := by
          gcongr
      _ = _ := by field_simp
  have hsq : Real.sqrt (1 / (N * η)) / N ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ := by
    have e1 : Real.sqrt (1 / (N * η)) = Real.sqrt ((N : ℝ)⁻¹) * Real.sqrt η⁻¹ := by
      rw [one_div, mul_inv, Real.sqrt_mul (inv_nonneg.2 hx0.le)]
    have e2 : Real.sqrt ((N : ℝ)⁻¹) / N = (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hx0.le, div_eq_mul_inv,
        ← Real.rpow_neg_one (N : ℝ), ← Real.rpow_add hx0]
      norm_num
    have e3 : Real.sqrt η⁻¹ ≤ η⁻¹ := by
      calc Real.sqrt η⁻¹ ≤ Real.sqrt (η⁻¹ ^ 2) := Real.sqrt_le_sqrt (le_self_pow₀ hηi1 (by norm_num))
        _ = η⁻¹ := Real.sqrt_sq (by positivity)
    calc Real.sqrt (1 / (N * η)) / N = Real.sqrt ((N : ℝ)⁻¹) / N * Real.sqrt η⁻¹ := by
          rw [e1]; ring
      _ ≤ _ := by
          rw [e2]
          exact mul_le_mul_of_nonneg_left e3 (Real.rpow_nonneg hx0.le _)
  have hlin : 1 / (N * η) / N = (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.rpow_two]
    field_simp
  have hδN : δ / N ≤ 2 * (T * S) := by
    have hτS : (N : ℝ) ^ τ'' * S ≤ T * S := mul_le_mul_of_nonneg_right h2τ hS0
    calc δ / N ≤ (N : ℝ) ^ τ'' * (Real.sqrt (1 / (N * η)) + 1 / (N * η)) / N :=
          div_le_div_of_nonneg_right hδ hx0.le
      _ = (N : ℝ) ^ τ'' * (Real.sqrt (1 / (N * η)) / N + 1 / (N * η) / N) := by ring
      _ ≤ (N : ℝ) ^ τ'' * (S + S) := by
          gcongr
          · exact hsq.trans hS1
          · rw [hlin]; exact hS3
      _ ≤ 2 * (T * S) := by linarith only [hτS]
  have P2 : 2 * Kν * ((108 * δ + 4 * η⁻¹ ^ 4 * ε) / N + 3 / N ^ 2) ≤ 2 * Kν * 223 * (T * S) := by
    have hN2 : 3 / (N : ℝ) ^ 2 = 3 * (N : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hx0.le, Real.rpow_two]; ring
    have h4 : 4 * η⁻¹ ^ 4 * ε / N ≤ 4 * (N : ℝ) ^ (-(2 : ℝ)) := by
      have := e4; rw [mul_assoc, mul_div_assoc]; linarith only [this]
    have hin : (108 * δ + 4 * η⁻¹ ^ 4 * ε) / N + 3 / N ^ 2 ≤ 223 * (T * S) := by
      rw [add_div, hN2, mul_div_assoc]
      have := hS2
      linarith only [hδN, h4, hS2, hST, this]
    calc _ ≤ 2 * Kν * (223 * (T * S)) := by gcongr
      _ = _ := by ring
  have P3 : 2 * D ^ 2 * δa ^ 2 + 18 * D ^ 2 * η⁻¹ ^ 2 * ε ≤ 20 * D ^ 2 * (T * S) := by
    have hδa2 : δa ^ 2 = T * ((N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2) := by
      rw [hδa, hT, mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ τ''), ← Real.rpow_mul hx0.le]
      have : (1 / (N * η)) ^ 2 = (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2 := by
        rw [Real.rpow_neg hx0.le, Real.rpow_two]; field_simp
      rw [this]; push_cast; ring_nf
    have h1 : δa ^ 2 ≤ T * S := by
      rw [hδa2]
      have : (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2 ≤ S := by
        rw [hSd]; have := mul_nonneg (Real.rpow_nonneg hx0.le (-(3 / 2 : ℝ))) (inv_nonneg.2 hη.le)
        linarith only [this]
      exact mul_le_mul_of_nonneg_left this (by linarith only [hT1])
    have h2 : η⁻¹ ^ 2 * ε ≤ T * S := e2'.trans (hS2.trans hST)
    have hD2 : (0 : ℝ) ≤ D ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h1 hD2
    have := mul_le_mul_of_nonneg_left h2 hD2
    nlinarith only [mul_le_mul_of_nonneg_left h1 hD2, mul_le_mul_of_nonneg_left h2 hD2]
  have hTS : 0 ≤ T * S := mul_nonneg (by linarith only [hT1]) hS0
  have : 2 * Kc * (4 + D + KR) * (T * S) ≤ 2 * Kc * (5 + D + KR) * (T * S) := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hKc) hTS
    nlinarith only [this]
  calc _ ≤ 2 * Kc * (4 + D + KR) * (T * S) + 2 * Kν * 223 * (T * S) + 20 * D ^ 2 * (T * S) := by
        linarith only [P1, P2, P3]
    _ ≤ (2 * Kc * (5 + D + KR) + 2 * Kν * 223 + 20 * D ^ 2) * (T * S) := by
        linarith only [this]
    _ = _ := by rw [hT]; ring

end

section

private theorem FC_good15 (D : ℕ) (hD : 1 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) (C' : ℕ → ℝ)
    (τ'' : ℝ) (hτ'' : 0 < τ'') : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C' θ μ →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ Xs : Matrix (Idx D N) (Idx D N) ℂ, opNorm Xs ≤ 1 →
        ∃ S : Set (Idx D N → Idx D N → ℂ),
          μ Sᶜ ≤ ENNReal.ofReal (3 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(30 : ℝ)) +
            2 * D * (N : ℝ) ^ (-(30 : ℝ))) ∧
          ∀ h ∈ S, (∀ ξ ∈ specDom τ N, FC_iso (res (Matrix.of h + lam D N A) ξ)
              (MExt (lam D N A) ξ) Xs ((N : ℝ) ^ τ'' * psiIso (lam D N A) N ξ)) ∧
            (∀ c, ∀ ξ ∈ specDom τ N, ‖ntr ((res (Matrix.of h + lam D N A) ξ -
              MExt (lam D N A) ξ) * Ea D N c)‖ ≤ (N : ℝ) ^ τ'' * (1 / ((N : ℝ) * |ξ.im|))) ∧
            (∀ x, ∀ ξ ∈ specDom τ N, ‖ntr ((res (Matrix.of h + lam D N A) ξ -
              MExt (lam D N A) ξ) * (Xs * Ea D N x))‖ ≤
                (N : ℝ) ^ τ'' * (1 / ((N : ℝ) * |ξ.im|))) := by
  obtain ⟨N₁, hN₁⟩ := FC_iso_event D hD δA τ hδA hτ C' τ'' hτ'' 30 (by norm_num)
  obtain ⟨N₂, hN₂⟩ := aver_local D hD δA τ hδA hτ C' τ'' hτ'' 30 (by norm_num)
  refine ⟨max N₁ N₂, fun N hN θ h0 h1 μ hμ A hA Xs hXs => ?_⟩
  have hprob := hμ.prob
  set S1 := {h : Idx D N → Idx D N → ℂ | ∀ ξ ∈ specDom τ N, FC_iso
    (res (Matrix.of h + lam D N A) ξ) (MExt (lam D N A) ξ) Xs
    ((N : ℝ) ^ τ'' * psiIso (lam D N A) N ξ)}
  set Bad : Matrix (Idx D N) (Idx D N) ℂ → Set (Idx D N → Idx D N → ℂ) := fun B' =>
    {h | ∃ z ∈ specDom τ N, (N : ℝ) ^ τ'' * (1 / ((N : ℝ) * |z.im|)) <
      ‖ntr ((res (Matrix.of h + lam D N A) z - MExt (lam D N A) z) * B')‖}
  refine ⟨S1 ∩ (⋂ c, (Bad (Ea D N c))ᶜ) ∩ (⋂ x, (Bad (Xs * Ea D N x))ᶜ), ?_, ?_⟩
  · have hc : (S1 ∩ (⋂ c, (Bad (Ea D N c))ᶜ) ∩ (⋂ x, (Bad (Xs * Ea D N x))ᶜ))ᶜ ⊆
        S1ᶜ ∪ (⋃ c, Bad (Ea D N c)) ∪ (⋃ x, Bad (Xs * Ea D N x)) := by
      intro h hh
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_iInter, not_and_or,
        not_forall, not_not] at hh
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion]
      tauto
    refine (measure_mono hc).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
    have u1 := hN₁ N ((le_max_left _ _).trans hN) θ h0 h1 μ hμ A hA Xs hXs
    have hE := FC_opNorm_Ea D N
    have hb2 : ∀ c : Fin D, μ (Bad (Ea D N c)) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(30 : ℝ))) :=
      fun c => hN₂ N ((le_max_right _ _).trans hN) θ h0 h1 μ hμ A hA (Ea D N c) (hE c)
    have u2 := (measure_iUnion_fintype_le μ _).trans
      (Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hb2 c)
    have hXE : ∀ x, opNorm (Xs * Ea D N x) ≤ 1 := by
      intro x
      refine (opNorm_mul_le _ _).trans ?_
      calc opNorm Xs * opNorm (Ea D N x) ≤ 1 * 1 :=
            mul_le_mul hXs (hE x) (FC_opNorm_nonneg _) zero_le_one
        _ = 1 := by ring
    have hb3 : ∀ x : Fin D, μ (Bad (Xs * Ea D N x)) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(30 : ℝ))) :=
      fun x => hN₂ N ((le_max_right _ _).trans hN) θ h0 h1 μ hμ A hA (Xs * Ea D N x) (hXE x)
    have u3 := (measure_iUnion_fintype_le μ _).trans
      (Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hb3 x)
    refine (add_le_add (add_le_add u1 u2) u3).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNp : 0 ≤ (N : ℝ) ^ (-(30 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    linarith
  · intro h hh
    obtain ⟨⟨hS1, hc⟩, hx⟩ := hh
    simp only [Set.mem_iInter, Set.mem_compl_iff, Bad, Set.mem_setOf_eq, not_exists, not_and,
      not_lt] at hc hx
    exact ⟨hS1, fun c ξ hξ => hc c ξ hξ, fun x ξ hξ => hx x ξ hξ⟩

end

section

private theorem FC_delta_le (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 1 ≤ c) (η : ℝ) (hη : 0 < η)
    (hηl : c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ η) :
    Real.sqrt (1 / (N * η)) + 1 / (N * η) ≤ 2 * c * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (N : ℝ) ^ (-(1 / 3 : ℝ)) := ⟨_, rfl⟩
  rw [← hu] at hηl ⊢
  have hu0 : 0 < u := by rw [hu]; exact Real.rpow_pos_of_pos hx0 _
  have hu1 : u ≤ 1 := by rw [hu]; exact Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hN3 : (N : ℝ)⁻¹ = u ^ 3 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_neg_one]
    norm_num
  have hc0 : 0 < c := by linarith
  have h1 : 1 / (N * η) ≤ c * u ^ 2 := by
    rw [one_div, mul_inv, hN3]
    have hηi : η⁻¹ ≤ c * u⁻¹ := by
      have h := inv_anti₀ (by positivity) hηl
      rw [mul_inv, inv_inv] at h
      exact h
    calc u ^ 3 * η⁻¹ ≤ u ^ 3 * (c * u⁻¹) := mul_le_mul_of_nonneg_left hηi (by positivity)
      _ = c * u ^ 2 := by field_simp
  have h2 : c * u ^ 2 ≤ c * u := by
    have : u ^ 2 ≤ u := by rw [sq]; exact mul_le_of_le_one_left hu0.le hu1
    exact mul_le_mul_of_nonneg_left this hc0.le
  have h3 : Real.sqrt (1 / (N * η)) ≤ c * u := by
    calc Real.sqrt (1 / (N * η)) ≤ Real.sqrt ((c * u) ^ 2) := by
          apply Real.sqrt_le_sqrt
          have : c * u ^ 2 ≤ (c * u) ^ 2 := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_right (le_self_pow₀ hc (by norm_num)) (by positivity)
          linarith
      _ = c * u := Real.sqrt_sq (by positivity)
  linarith

private theorem FC_arith (d sd C₁ Cm Kν ρ r q e κ a ni s P Q K₁ αn : ℝ) (hd : 0 ≤ d) (hsd : 0 ≤ sd)
    (hC₁ : 0 ≤ C₁) (hCm : 0 ≤ Cm) (hKν : 0 ≤ Kν) (hρ : 1 ≤ ρ) (hr0 : 0 ≤ r) (hr : r ≤ 2 * C₁ * ρ)
    (hq0 : 0 ≤ q) (hq : q ≤ C₁ * ρ) (he0 : 0 ≤ e) (he : e ≤ K₁ * P * s) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 2 * Cm * a) (ha : 0 ≤ a) (hni : 0 ≤ ni) (hαn0 : 0 ≤ αn) (hαn : αn ≤ Kν * ni)
    (hs : 0 ≤ s) (hP : 0 ≤ P) (hK₁ : 0 ≤ K₁)
    (hK₂ : (1 + 4 * d ^ 2 * sd * C₁) * K₁ * P ≤ Q)
    (hK₃ : Kν * ((12 * d + 24 * d * C₁ + 8 * d * sd * (6 * d + 4) * C₁) * (2 * Cm)) ≤ Q) :
    e + 2 * d * (d * sd * r * e) + αn * ((12 * d + 24 * d * q + 4 * d * sd * (6 * d + 4) * r) * κ)
      ≤ Q * (ρ * (s + ni * a)) := by
  have hρ0 : 0 ≤ ρ := by linarith
  have h1 : 2 * d * (d * sd * r * e) ≤ 4 * d ^ 2 * sd * C₁ * ρ * e := by
    have : 2 * d * (d * sd * r * e) = (2 * d * d * sd * e) * r := by ring
    rw [this]
    calc (2 * d * d * sd * e) * r ≤ (2 * d * d * sd * e) * (2 * C₁ * ρ) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  have h2 : e + 4 * d ^ 2 * sd * C₁ * ρ * e ≤ ρ * (1 + 4 * d ^ 2 * sd * C₁) * e := by
    have : e ≤ ρ * e := le_mul_of_one_le_left he0 hρ
    nlinarith only [this]
  have h3 : ρ * (1 + 4 * d ^ 2 * sd * C₁) * e ≤ ρ * Q * s := by
    calc ρ * (1 + 4 * d ^ 2 * sd * C₁) * e ≤ ρ * (1 + 4 * d ^ 2 * sd * C₁) * (K₁ * P * s) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = ρ * s * ((1 + 4 * d ^ 2 * sd * C₁) * K₁ * P) := by ring
      _ ≤ ρ * s * Q := mul_le_mul_of_nonneg_left hK₂ (by positivity)
      _ = ρ * Q * s := by ring
  have h4 : 12 * d + 24 * d * q + 4 * d * sd * (6 * d + 4) * r ≤
      ρ * (12 * d + 24 * d * C₁ + 8 * d * sd * (6 * d + 4) * C₁) := by
    have a1 : 12 * d ≤ ρ * (12 * d) := le_mul_of_one_le_left (by positivity) hρ
    have a2 : 24 * d * q ≤ 24 * d * (C₁ * ρ) := mul_le_mul_of_nonneg_left hq (by positivity)
    have a3 : 4 * d * sd * (6 * d + 4) * r ≤ 4 * d * sd * (6 * d + 4) * (2 * C₁ * ρ) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    nlinarith only [a1, a2, a3]
  have h5 : αn * ((12 * d + 24 * d * q + 4 * d * sd * (6 * d + 4) * r) * κ) ≤
      Q * (ρ * (ni * a)) := by
    calc _ ≤ (Kν * ni) * ((ρ * (12 * d + 24 * d * C₁ + 8 * d * sd * (6 * d + 4) * C₁)) *
          (2 * Cm * a)) := by
          apply mul_le_mul hαn _ (by positivity) (by positivity)
          exact mul_le_mul h4 hκ hκ0 (by positivity)
      _ = (ρ * (ni * a)) * (Kν * ((12 * d + 24 * d * C₁ + 8 * d * sd * (6 * d + 4) * C₁) *
          (2 * Cm))) := by ring
      _ ≤ (ρ * (ni * a)) * Q := mul_le_mul_of_nonneg_left hK₃ (by positivity)
      _ = _ := by ring
  have : Q * (ρ * (s + ni * a)) = ρ * Q * s + Q * (ρ * (ni * a)) := by ring
  rw [this]
  linarith only [h1, h2, h3, h5]

set_option maxHeartbeats 4000000 in
private theorem FC_P15 (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t → t ≤ 1 →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ) + τe) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ : ℂ, (z₁ = z ∨ z₁ = star z) →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
        1 - ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₁) ≠ 0 ∧
        ‖(∫ h, ntr ((res (Matrix.of h + lam D N A) z₁ - MExt (lam D N A) z₁) * B)
              ∂(ouMatLaw D N L t)) -
            ((Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 *
              FC_lead15M (MExt (lam D N A) z₁) B‖ ≤
          (N : ℝ) ^ τ' * (min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) *
            ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) * (z.im ^ 2)⁻¹ +
              (N : ℝ)⁻¹ * opNorm A)) := by
  intro τ' hτ'
  have hD1 : 1 ≤ D := by omega
  obtain ⟨τ'', hτ''0, hτ''1, hτ''2⟩ : ∃ τ'' : ℝ, 0 < τ'' ∧ τ'' < 1 / 3 ∧ 2 * τ'' < τ' :=
    ⟨min (τ' / 4) (1 / 12), by positivity, by
      have := min_le_right (τ' / 4) (1 / 12); linarith, by
      have := min_le_left (τ' / 4) (1 / 12); linarith⟩
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  obtain ⟨Kc, hKc0, hcore⟩ := FC_core D C 24 160 (by norm_num)
  obtain ⟨Kν, hKν⟩ := ccum_entry_le C 2 2
  have hKν0 : ∀ L : EntryLaws C, ‖ccum (L.νo : Measure ℂ) 2 2‖ ≤ |Kν| :=
    fun L => (hKν L).1.trans (le_abs_self _)
  obtain ⟨Cm, hCm0, hMf⟩ := FC_Mfacts τ hτ
  have hc0 : 0 < c⁻¹ := inv_pos.2 (by linarith)
  have hc1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  obtain ⟨C₁, hC₁, N₁, hsame⟩ := one_minus_Mhat_same D hD δA εg c⁻¹ τ hδA hεg hεg₂ hc0 hc1 hτ
  obtain ⟨N₂, hinv⟩ := oneSubMhatP_inv_le D hD δA τ hδA hτ
  obtain ⟨N₃, hgood⟩ := FC_good15 D hD1 δA τ hδA hτ C' τ'' hτ''0
  obtain ⟨K₁, hK₁0, N₄, hE1⟩ := FC_E1 D hD1 c hc Kc |Kν| τ'' hKc0 (abs_nonneg _) hτ''0
  obtain ⟨N₅, hN₅⟩ := FC_ev_ge hδA 20
  obtain ⟨N₆, hN₆⟩ := FC_ev_ge hεg c
  obtain ⟨N₇, hN₇⟩ := FC_ev_pow (show τ'' - 1 / 3 < 0 by linarith) (2 * c)
  set K₂ := (1 + 4 * D ^ 2 * Real.sqrt D * C₁) * K₁ with hK₂
  set K₃ := |Kν| * ((12 * D + 24 * D * C₁ + 8 * D * Real.sqrt D * (6 * D + 4) * C₁) * (2 * Cm))
    with hK₃
  obtain ⟨N₈, hN₈⟩ := FC_ev_ge (show 0 < τ' - 2 * τ'' by linarith) K₂
  obtain ⟨N₉, hN₉⟩ := FC_ev_ge hτ' K₃
  refine ⟨max (max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max N₇ N₈))) (max N₉ 2),
    fun N hN L t ht0 ht1 A hA z hz hzim hη hq1 hq2 z₁ h₁ B hB => ?_⟩
  have hN1 : 1 ≤ N := by
    have := (le_max_right N₉ 2).trans ((le_max_right _ _).trans hN); omega
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx0 : (0 : ℝ) < N := by linarith
  have hNi : ∀ {a b : ℕ}, a ≤ b → b ≤ N → a ≤ N := fun h1 h2 => h1.trans h2
  have gN₁ : N₁ ≤ N := by omega
  have gN₂ : N₂ ≤ N := by omega
  have gN₃ : N₃ ≤ N := by omega
  have gN₄ : N₄ ≤ N := by omega
  have gN₅ : N₅ ≤ N := by omega
  have gN₆ : N₆ ≤ N := by omega
  have gN₇ : N₇ ≤ N := by omega
  have gN₈ : N₈ ≤ N := by omega
  have gN₉ : N₉ ≤ N := by omega
  obtain ⟨hzn, hzl'⟩ := hz
  have hlam : opNorm (lam D N A) ≤ 1 / 10 := by
    have h20 := hN₅ N gN₅
    have : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
      rw [Real.rpow_neg hx0.le]
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h20
    linarith [opNorm_lam_le D N A]
  obtain ⟨-, hmz, -⟩ := hMf D N hD1 hN1 A hlam z hzn hzim z (Or.inl rfl)
  obtain ⟨hM1, hm1, hκ⟩ := hMf D N hD1 hN1 A hlam z hzn hzim z₁ h₁
  set m := mExt (lam D N A) z with hm
  have hmpos : 0 < m.im := by
    have h0 : 0 < c⁻¹ * (N : ℝ) ^ (-εg) := by positivity
    have := lt_of_lt_of_le h0 hq1
    by_contra hneg
    push_neg at hneg
    have : z.im / m.im ≤ 0 := div_nonpos_of_nonneg_of_nonpos hzim.le hneg
    linarith
  have hmle : m.im ≤ 1 := (Complex.im_le_norm m).trans hmz
  have hη1 : z.im ≤ 1 := by
    have hq := hq2
    rw [div_le_iff₀ hmpos] at hq
    have hc6 := hN₆ N gN₆
    have : c * (N : ℝ) ^ (-εg) ≤ 1 := by
      rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv]
      exact (div_le_one (by positivity)).2 hc6
    have hp : 0 ≤ c * (N : ℝ) ^ (-εg) := by positivity
    nlinarith
  have hmS : m = mSol (lam D N A) z := if_pos hzim
  obtain ⟨-, hne, hRinv, hsinv⟩ := hsame N gN₁ A hA z hzn hzim
    (by rw [← hmS]; exact hq1) (by rw [← hmS, inv_inv]; exact hq2) z₁ h₁
  rw [← hmS] at hRinv hsinv
  set θ := Real.exp (-t) with hθ
  have hθ0 : 0 ≤ θ := (Real.exp_pos _).le
  have hθ1 : θ ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  obtain ⟨hdet, hRle⟩ := hinv N gN₂ A hA z hzn hzim z₁ z₁ h₁ h₁ θ hθ0 hθ1
  refine ⟨hne, ?_⟩
  set ρ := min m.im⁻¹ ((N : ℝ) ^ εg) with hρ
  have hρ1 : 1 ≤ ρ := le_min ((one_le_inv₀ hmpos).2 hmle) (Real.one_le_rpow hx hεg.le)
  set M := MExt (lam D N A) z₁ with hMdef
  have habs : |z₁.im| = z.im := by
    rcases h₁ with rfl | rfl
    · exact abs_of_pos hzim
    · simp only [Complex.star_def, Complex.conj_im, abs_neg]; exact abs_of_pos hzim
  have hz₁dom : z₁ ∈ specDom τ N := by
    refine ⟨?_, ?_⟩
    · rcases h₁ with rfl | rfl
      · exact hzn
      · rw [Complex.star_def, Complex.norm_conj]; exact hzn
    · rw [habs]; rw [abs_of_pos hzim] at hzl'; exact hzl'
  have him₁ : z₁.im ≠ 0 := by
    intro h0; rw [h0, abs_zero] at habs; linarith
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = 3 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(30 : ℝ)) +
      2 * D * (N : ℝ) ^ (-(30 : ℝ)) := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hεd]; positivity
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = (N : ℝ) ^ τ'' * psiIso (lam D N A) N z₁ := ⟨_, rfl⟩
  obtain ⟨δa, hδad⟩ : ∃ δa : ℝ, δa = (N : ℝ) ^ τ'' * (1 / ((N : ℝ) * |z₁.im|)) := ⟨_, rfl⟩
  have hηl : c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im := by
    have : (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 3 : ℝ) + τe) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    exact (mul_le_mul_of_nonneg_left this hc0.le).trans hη
  have hδ0 : 0 ≤ δ := by rw [hδd, psiIso]; positivity
  have hδle : δ ≤ (N : ℝ) ^ τ'' * (Real.sqrt (1 / (N * z.im)) + 1 / (N * z.im)) := by
    rw [hδd, psiIso, habs]
    gcongr
    · exact (Complex.abs_im_le_norm _).trans hm1
  have hδ1 : δ ≤ 1 := by
    refine hδle.trans ?_
    have h7 := hN₇ N gN₇
    rw [Real.rpow_zero] at h7
    calc (N : ℝ) ^ τ'' * (Real.sqrt (1 / (N * z.im)) + 1 / (N * z.im)) ≤
          (N : ℝ) ^ τ'' * (2 * c * (N : ℝ) ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left (FC_delta_le N hN1 c hc z.im hzim hηl)
            (Real.rpow_nonneg hx0.le _)
      _ = 2 * c * (N : ℝ) ^ (τ'' - 1 / 3) := by
          rw [show τ'' - 1 / 3 = τ'' + (-(1 / 3 : ℝ)) by ring, Real.rpow_add hx0]; ring
      _ ≤ 1 := h7
  have hδa0 : 0 ≤ δa := by rw [hδad]; positivity
  have hδa' : δa = (N : ℝ) ^ τ'' * (1 / (N * z.im)) := by rw [hδad, habs]
  set kk := Nat.log 2 (D * N) + 1 with hkk
  have hkk' : D * N ≤ 2 ^ kk := (Nat.lt_pow_succ_log_self (by norm_num) _).le
  obtain ⟨e, hed⟩ : ∃ e : ℝ, e = 2 / ((D : ℝ) * N) * (Kc * FC_err D N 1 24 160 kk z.im 1 ε) +
      2 * |Kν| * ((108 * δ + 4 * (z.im)⁻¹ ^ 4 * ε) / N + 3 / N ^ 2) +
      (2 * D ^ 2 * δa ^ 2 + 18 * D ^ 2 * (z.im)⁻¹ ^ 2 * ε) := ⟨_, rfl⟩
  have hμ := hC' N L t ht0
  have hT : ∀ B' : Matrix (Idx D N) (Idx D N) ℂ, opNorm B' ≤ 1 →
      ‖(∫ h, ntr ((res (Matrix.of h + lam D N A) z₁ - M) * B') ∂(ouMatLaw D N L t)) -
        ((Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 * FC_leadM M B' -
        ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) *
          ∫ h, ntr ((res (Matrix.of h + lam D N A) z₁ - M) * Ea D N c) ∂(ouMatLaw D N L t)) *
            ntr (Ea D N x * M * B' * M)‖ ≤ e := by
    intro B' hB'
    have hX : opNorm ((1 / 2 : ℂ) • (B' * M)) ≤ 1 := by
      rw [opNorm_smul]
      have h1 := opNorm_mul_le B' M
      have h2 : opNorm B' * opNorm M ≤ 1 * (5 / 4) :=
        mul_le_mul hB' hM1 (FC_opNorm_nonneg _) zero_le_one
      have h3 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [h3]
      linarith
    obtain ⟨S, hSc, hSg⟩ := hgood N gN₃ θ hθ0 hθ1 _ hμ A hA _ hX
    rw [← hεd] at hSc
    have hchOK : FC_chOK (lam D N A) z [(1, lam D N A, z₁)] := by
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨rfl, h₁, FC_opNorm_one⟩
    have hG := FC_good_one (lam D N A) (lam_isHermitian D N A) z hzim z₁ h₁ M _ hM1 hX δ hδ1 S
      (fun h hh _ => by rw [hδd]; exact (hSg h hh).1 z₁ hz₁dom) 1
    have hc' := hcore N hN1 L t ht0 (lam D N A) (lam_isHermitian D N A) z hzim hη1
      [(1, lam D N A, z₁)] hchOK (Or.inl rfl) _ hX S ε hε0 hSc 1 le_rfl hG kk hkk'
    have := FC_P15_step1 D N hD hN1 L t ht0 hμ A z hzim hη1 z₁ h₁ hM1 B' hB' 24 160 _ hc'
      S ε hε0 hSc δ δa hδ0 hδ1 hδa0 (fun h hh _ => by rw [hδd]; exact (hSg h hh).1 z₁ hz₁dom)
      (fun h hh _ c => by rw [hδad]; exact (hSg h hh).2.1 c z₁ hz₁dom)
      (fun h hh _ x => by rw [hδad]; exact (hSg h hh).2.2 x z₁ hz₁dom) |Kν| (hKν0 L)
    rw [hed]
    exact this
  have hE := hE1 N gN₄ z.im δ δa ε hzim hη1 hηl hδ0 hδle hδa' hε0 hεd.le
  rw [← hed] at hE
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hT B hB)
  have hsol := FC_solve D N hD1 θ hθ0 hθ1 M hM1 (Mhat (lam D N A) z₁ z₁) (fun a x => rfl) hdet
    (fun B' => ∫ h, ntr ((res (Matrix.of h + lam D N A) z₁ - M) * B') ∂(ouMatLaw D N L t))
    (FC_leadM M) (((Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2) e hT B hB
  have hR1 := FC_R1 D hD N A z₁ him₁ θ hdet hne
  have hLt := FC_Ltrue D N hD1 hN1 θ hθ0 hθ1 M hM1 (mExt (lam D N A) z₁) hm1 _ hκ
    (Mhat (lam D N A) z₁ z₁) _ hR1 rfl B hB
  obtain ⟨R, hRd⟩ : ∃ R, R = (1 - Mhat (lam D N A) z₁ z₁ * PTheta D θ)⁻¹ := ⟨_, rfl⟩
  rw [← hRd] at hsol hLt hRle
  obtain ⟨α, hαd⟩ : ∃ α : ℂ, α = ((Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 :=
    ⟨_, rfl⟩
  rw [← hαd] at hsol
  rw [← hαd]
  obtain ⟨TB, hTB⟩ : ∃ TB : ℂ, TB = ∫ h, ntr ((res (Matrix.of h + lam D N A) z₁ - M) * B)
      ∂(ouMatLaw D N L t) := ⟨_, rfl⟩
  rw [← hTB] at hsol ⊢
  obtain ⟨Y, hYd⟩ : ∃ Y : ℂ, Y = FC_leadM M B + ∑ x, ∑ c, PTheta D θ x c *
      (R *ᵥ fun a => (D : ℂ) * FC_leadM M (Ea D N a)) c * ntr (Ea D N x * M * B * M) := ⟨_, rfl⟩
  rw [← hYd] at hsol hLt
  have hsplit : TB - α * FC_lead15M M B = (TB - α * Y) + α * (Y - FC_lead15M M B) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hα : ‖α‖ ≤ |Kν| * (N : ℝ)⁻¹ := by
    rw [hαd, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Real.exp (-(2 * t)) / N| ≤ (N : ℝ)⁻¹ := by
      rw [abs_of_nonneg (by positivity), div_eq_mul_inv]
      exact mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.2 (by linarith))
    calc |Real.exp (-(2 * t)) / N| * ‖ccum (L.νo : Measure ℂ) 2 2‖ ≤
          (N : ℝ)⁻¹ * |Kν| := mul_le_mul h1 (hKν0 L) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hρmin : ρ = min m.im⁻¹ ((N : ℝ) ^ εg) := hρ
  have hr : opNorm R ≤ 2 * C₁ * ρ := by
    calc opNorm R ≤ 2 * opNorm (1 - Mhat (lam D N A) z₁ z₁)⁻¹ := hRle
      _ ≤ 2 * (C₁ * ρ) := by gcongr
      _ = 2 * C₁ * ρ := by ring
  have hq : ‖(1 - ntr (M * M))⁻¹‖ ≤ C₁ * ρ := by rw [norm_inv]; exact hsinv
  have hκ' : Cm * opNorm (lam D N A) ≤ 2 * Cm * opNorm A := by
    have := opNorm_lam_le D N A
    calc Cm * opNorm (lam D N A) ≤ Cm * (2 * opNorm A) := mul_le_mul_of_nonneg_left this hCm0.le
      _ = _ := by ring
  have hK₂' : (1 + 4 * (D : ℝ) ^ 2 * Real.sqrt D * C₁) * K₁ * (N : ℝ) ^ (2 * τ'') ≤
      (N : ℝ) ^ τ' := by
    have h8 := hN₈ N gN₈
    calc (1 + 4 * (D : ℝ) ^ 2 * Real.sqrt D * C₁) * K₁ * (N : ℝ) ^ (2 * τ'') =
          K₂ * (N : ℝ) ^ (2 * τ'') := by rw [hK₂]
      _ ≤ (N : ℝ) ^ (τ' - 2 * τ'') * (N : ℝ) ^ (2 * τ'') :=
          mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg hx0.le _)
      _ = (N : ℝ) ^ τ' := by rw [← Real.rpow_add hx0]; ring_nf
  have hK₃' := hN₉ N gN₉
  rw [hK₃] at hK₃'
  have hfin := FC_arith D (Real.sqrt D) C₁ Cm |Kν| ρ (opNorm R) ‖(1 - ntr (M * M))⁻¹‖ e
    (Cm * opNorm (lam D N A)) (opNorm A) (N : ℝ)⁻¹
    ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) * (z.im)⁻¹ ^ 2)
    ((N : ℝ) ^ (2 * τ'')) ((N : ℝ) ^ τ') K₁ ‖α‖ (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    hC₁.le hCm0.le (abs_nonneg _) hρ1 (FC_opNorm_nonneg _) hr (norm_nonneg _) hq he0
    hE (mul_nonneg hCm0.le (FC_opNorm_nonneg _)) hκ'
    (FC_opNorm_nonneg _) (by positivity) (norm_nonneg _) hα (by positivity)
    (Real.rpow_nonneg hx0.le _) hK₁0 hK₂' hK₃'
  have hsq : ((z.im) ^ 2)⁻¹ = (z.im)⁻¹ ^ 2 := by rw [inv_pow]
  rw [hsq]
  have hfin' : (N : ℝ) ^ τ' * (ρ * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ +
      (N : ℝ) ^ (-(2 : ℝ)) * (z.im)⁻¹ ^ 2 + (N : ℝ)⁻¹ * opNorm A)) =
      (N : ℝ) ^ τ' * (ρ * (((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ +
      (N : ℝ) ^ (-(2 : ℝ)) * (z.im)⁻¹ ^ 2) + (N : ℝ)⁻¹ * opNorm A)) := by ring
  rw [hfin']
  refine le_trans ?_ hfin
  have h2 := mul_le_mul_of_nonneg_left hLt (norm_nonneg α)
  calc ‖TB - α * Y‖ + ‖α‖ * ‖Y - FC_lead15M M B‖ ≤
      (e + 2 * D * (D * Real.sqrt D * opNorm R * e)) + ‖α‖ *
        ((12 * D + 24 * D * ‖(1 - ntr (M * M))⁻¹‖ + 4 * D * Real.sqrt D * (6 * D + 4) *
          opNorm R) * (Cm * opNorm (lam D N A))) := add_le_add hsol h2
    _ = _ := by ring

end

section

private theorem FC_varProf_symm (D N : ℕ) (θ : ℝ) (i j : Idx D N) :
    varProf D N θ i j = varProf D N θ j i := by
  unfold varProf; simp only [eq_comm]

private theorem FC_ntr_sTheta_symm (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ)
    (X Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr (sTheta D N θ X * Y) = ntr (sTheta D N θ Y * X) := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have h1 := FC_sum_varProf D N hD hN θ X Y
  have h2 := FC_sum_varProf D N hD hN θ Y X
  have e : ∑ i, ∑ j, (varProf D N θ i j : ℂ) * (X i i * Y j j) =
      ∑ i, ∑ j, (varProf D N θ i j : ℂ) * (Y i i * X j j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [FC_varProf_symm]; ring
  rw [e, h2] at h1
  have hDN : ((D : ℂ) * N) ≠ 0 := mul_ne_zero hD0 hN0
  exact (mul_left_cancel₀ hDN h1).symm

private theorem FC_chain2 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (Λ E : Matrix (Idx D N) (Idx D N) ℂ)
    (ξ₁ ξ₂ : ℂ) : chainB h [(1, Λ, ξ₂), (E, Λ, ξ₁)] =
      res (Matrix.of h + Λ) ξ₂ * (E * res (Matrix.of h + Λ) ξ₁) := by
  simp [chainB]

private theorem FC_point2 {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (z₁ z₂ : ℂ) (a : Fin D)
    (B : Matrix (Idx D N) (Idx D N) ℂ) :
    underTwoB Λ θ h z₁ z₂ a B =
      (2 : ℂ) / ((D : ℂ) * N) * (∑ i, (∑ j, (chainB h [(1, Λ, z₂), (B, Λ, z₁)] *
          ((1 / 2 : ℂ) • (Ea D N a * MExt Λ z₂))) i j * starRingEnd ℂ (h i j))) +
        2 * ntr (sTheta D N θ (res (Matrix.of h + Λ) z₂) * (res (Matrix.of h + Λ) z₂ *
          (B * (res (Matrix.of h + Λ) z₁ * ((1 / 2 : ℂ) • (Ea D N a * MExt Λ z₂)))))) +
        2 * ntr (sTheta D N θ (res (Matrix.of h + Λ) z₂ * (B * res (Matrix.of h + Λ) z₁)) *
          (res (Matrix.of h + Λ) z₁ * ((1 / 2 : ℂ) • (Ea D N a * MExt Λ z₂)))) := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [FC_chain2]
  unfold underTwoB hgUnder
  generalize res (Matrix.of h + Λ) z₁ = G₁
  generalize res (Matrix.of h + Λ) z₂ = G₂
  generalize MExt Λ z₂ = M₂
  rw [show G₁ * Ea D N a * M₂ = G₁ * (Ea D N a * M₂) from Matrix.mul_assoc _ _ _]
  generalize Ea D N a * M₂ = W
  have hs : ∀ Y : Matrix (Idx D N) (Idx D N) ℂ, Y * ((1 / 2 : ℂ) • W) = (1 / 2 : ℂ) • (Y * W) :=
    fun Y => Matrix.mul_smul _ _ _
  have ha : ntr (G₁ * W * (Matrix.of h * G₂) * B) =
      (2 : ℂ) / ((D : ℂ) * N) * ∑ i, ∑ j, (G₂ * (B * G₁) * ((1 / 2 : ℂ) • W)) i j *
        starRingEnd ℂ (h i j) := by
    have e1 : ntr (G₁ * W * (Matrix.of h * G₂) * B) = ntr (Matrix.of h * (G₂ * (B * G₁) * W)) := by
      unfold ntr
      rw [show G₁ * W * (Matrix.of h * G₂) * B = (G₁ * W) * (Matrix.of h * G₂ * B) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [e1, FC_ntr_HGX h hh, hs]
    simp only [Matrix.smul_apply, smul_eq_mul]
    have e2 : ∑ i, ∑ j, 1 / 2 * (G₂ * (B * G₁) * W) i j * starRingEnd ℂ (h i j) =
        1 / 2 * ∑ i, ∑ j, (G₂ * (B * G₁) * W) i j * starRingEnd ℂ (h i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    field_simp
  have hb : ntr (G₁ * W * (sTheta D N θ G₂ * G₂) * B) =
      2 * ntr (sTheta D N θ G₂ * (G₂ * (B * (G₁ * ((1 / 2 : ℂ) • W))))) := by
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, FC_ntr_smul]
    have : ntr (G₁ * W * (sTheta D N θ G₂ * G₂) * B) =
        ntr (sTheta D N θ G₂ * (G₂ * (B * (G₁ * W)))) := by
      unfold ntr
      rw [show G₁ * W * (sTheta D N θ G₂ * G₂) * B = (G₁ * W) * (sTheta D N θ G₂ * G₂ * B) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [this]; ring
  have hc : ntr (G₁ * sTheta D N θ (G₁ * W) * G₂ * B) =
      2 * ntr (sTheta D N θ (G₂ * (B * G₁)) * (G₁ * ((1 / 2 : ℂ) • W))) := by
    have e1 : ntr (G₁ * sTheta D N θ (G₁ * W) * G₂ * B) =
        ntr (sTheta D N θ (G₁ * W) * (G₂ * (B * G₁))) := by
      unfold ntr
      rw [show G₁ * sTheta D N θ (G₁ * W) * G₂ * B = G₁ * (sTheta D N θ (G₁ * W) * G₂ * B) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [e1, FC_ntr_sTheta_symm D N hD hN, Matrix.mul_smul, Matrix.mul_smul, FC_ntr_smul]
    ring
  have e : G₁ * W * (Matrix.of h * G₂ + sTheta D N θ G₂ * G₂) * B =
      G₁ * W * (Matrix.of h * G₂) * B + G₁ * W * (sTheta D N θ G₂ * G₂) * B := by
    rw [Matrix.mul_add, Matrix.add_mul]
  rw [e, FC_ntr_add, ha, hb, hc]

end

section

private theorem FC_D210 : FC_Dpq 2 1 0 = [[((0, 1, false, false), false, false),
    ((0, 2, true, true), true, true)], [((0, 2, false, false), false, false),
    ((1, 2, true, true), true, true)]] := by decide

private theorem FC_D201 : FC_Dpq 2 0 1 = [[((0, 1, false, false), false, true),
    ((0, 2, true, true), false, true)], [((0, 2, false, false), false, true),
    ((1, 2, true, true), false, true)]] := by decide

section FC_two
variable {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (Λ E : Matrix (Idx D N) (Idx D N) ℂ) (ξ₁ ξ₂ : ℂ)
  (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N)

private theorem FC_eval210 : FC_evalPoly h [(1, Λ, ξ₂), (E, Λ, ξ₁)] X i j (FC_Dpq 2 1 0) =
    res (Matrix.of h + Λ) ξ₂ i i * (res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ *
      X))) j j + (res (Matrix.of h + Λ) ξ₂ * (E * res (Matrix.of h + Λ) ξ₁)) i i *
        (res (Matrix.of h + Λ) ξ₁ * X) j j := by
  rw [FC_D210]
  simp [FC_evalPoly, FC_evalMono, FC_evalFac, FC_seg2a, FC_seg2b, FC_seg2c, FC_idx]

private theorem FC_eval201 : FC_evalPoly h [(1, Λ, ξ₂), (E, Λ, ξ₁)] X i j (FC_Dpq 2 0 1) =
    res (Matrix.of h + Λ) ξ₂ i j * (res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ *
      X))) i j + (res (Matrix.of h + Λ) ξ₂ * (E * res (Matrix.of h + Λ) ξ₁)) i j *
        (res (Matrix.of h + Λ) ξ₁ * X) i j := by
  rw [FC_D201]
  simp [FC_evalPoly, FC_evalMono, FC_evalFac, FC_seg2a, FC_seg2b, FC_seg2c, FC_idx]

end FC_two

private theorem FC_cont_sThetaG {α : Type*} [TopologicalSpace α] (D N : ℕ) (hD : 1 ≤ D) (θ : ℝ)
    (Y Z : α → Matrix (Idx D N) (Idx D N) ℂ) (hY : Continuous Y) (hZ : Continuous Z) :
    Continuous (fun p => ntr (sTheta D N θ (Y p) * Z p)) := by
  have e : (fun p => ntr (sTheta D N θ (Y p) * Z p)) = fun p =>
      ∑ x, ∑ c, PTheta D θ x c * ((D : ℂ) * ntr (Y p * Ea D N c)) * ntr (Ea D N x * Z p) := by
    funext p; exact FC_ntr_sTheta D N hD θ (Y p) (Z p)
  rw [e]
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun c _ => ?_
  have h1 : Continuous fun p => ntr (Y p * Ea D N c) := by
    unfold ntr; exact continuous_const.mul (hY.matrix_mul continuous_const).matrix_trace
  have h2 : Continuous fun p => ntr (Ea D N x * Z p) := by
    unfold ntr; exact continuous_const.mul (continuous_const.matrix_mul hZ).matrix_trace
  exact (continuous_const.mul (continuous_const.mul h1)).mul h2

private theorem FC_second2 (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) {C' : ℕ → ℝ} (θ : ℝ)
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C' θ μ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (ξ₁ ξ₂ : ℂ) (h₁ : ξ₁ = z ∨ ξ₁ = star z) (h₂ : ξ₂ = z ∨ ξ₂ = star z)
    (E X : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i, ∑ j, (FC_f μ [(1, Λ, ξ₂), (E, Λ, ξ₁)] X i j 1 0 +
      FC_f μ [(1, Λ, ξ₂), (E, Λ, ξ₁)] X i j 0 1) =
      -(((D : ℂ) * N) * ∫ h, (ntr (sTheta D N θ (res (Matrix.of h + Λ) ξ₂) *
        (res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ * X)))) +
        ntr (sTheta D N θ (res (Matrix.of h + Λ) ξ₂ * (E * res (Matrix.of h + Λ) ξ₁)) *
          (res (Matrix.of h + Λ) ξ₁ * X))) ∂μ) := by
  have hprob := hμ.prob
  have hlen : ([(1, Λ, ξ₂), (E, Λ, ξ₁)] : FC_Ch D N).length = 2 := rfl
  have hint : ∀ i j, Integrable (fun h => res (Matrix.of h + Λ) ξ₂ i i *
      (res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ * X))) j j +
      (res (Matrix.of h + Λ) ξ₂ * (E * res (Matrix.of h + Λ) ξ₁)) i i *
        (res (Matrix.of h + Λ) ξ₁ * X) j j) μ := by
    intro i j
    refine FC_int_cont2 hμ.herm Λ hΛ z hz ξ₁ ξ₂ h₁ h₂ (fun p => p.2 i i *
      (p.2 * (E * (p.1 * X))) j j + (p.2 * (E * p.1)) i i * (p.1 * X) j j) ?_
    exact ((continuous_snd.matrix_elem i i).mul ((continuous_snd.matrix_mul
      (continuous_const.matrix_mul (continuous_fst.matrix_mul continuous_const))).matrix_elem j j)).add
      (((continuous_snd.matrix_mul (continuous_const.matrix_mul continuous_fst)).matrix_elem i i).mul
        ((continuous_fst.matrix_mul continuous_const).matrix_elem j j))
  have hterm : ∀ i j, FC_f μ [(1, Λ, ξ₂), (E, Λ, ξ₁)] X i j 1 0 +
      FC_f μ [(1, Λ, ξ₂), (E, Λ, ξ₁)] X i j 0 1 =
      -((varProf D N θ i j : ℂ) * ∫ h, (res (Matrix.of h + Λ) ξ₂ i i *
        (res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ * X))) j j +
        (res (Matrix.of h + Λ) ξ₂ * (E * res (Matrix.of h + Λ) ξ₁)) i i *
          (res (Matrix.of h + Λ) ξ₁ * X) j j) ∂μ) := by
    intro i j
    obtain ⟨-, c11, -, c02⟩ := llClass_ccum_low D N C' θ μ hμ i j
    unfold FC_f
    simp only [hlen, FC_eval210, FC_eval201, zero_add, Nat.factorial, Nat.mul_one,
      Nat.cast_one, div_one, pow_one, c11, c02]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      ring
    · simp only [hij, ↓reduceIte, zero_mul, add_zero]
      ring
  simp only [hterm, Finset.sum_neg_distrib]
  congr 1
  have e : ∀ i j, (varProf D N θ i j : ℂ) * ∫ h, (res (Matrix.of h + Λ) ξ₂ i i *
      (res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ * X))) j j +
      (res (Matrix.of h + Λ) ξ₂ * (E * res (Matrix.of h + Λ) ξ₁)) i i *
        (res (Matrix.of h + Λ) ξ₁ * X) j j) ∂μ = ∫ h, (varProf D N θ i j : ℂ) *
      (res (Matrix.of h + Λ) ξ₂ i i *
        (res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ * X))) j j +
        (res (Matrix.of h + Λ) ξ₂ * (E * res (Matrix.of h + Λ) ξ₁)) i i *
          (res (Matrix.of h + Λ) ξ₁ * X) j j) ∂μ := fun i j =>
    (integral_const_mul _ _).symm
  simp only [e]
  rw [← integral_const_mul]
  have hsum : ∀ i, ∑ j, ∫ h, (varProf D N θ i j : ℂ) * (res (Matrix.of h + Λ) ξ₂ i i *
        (res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ * X))) j j +
        (res (Matrix.of h + Λ) ξ₂ * (E * res (Matrix.of h + Λ) ξ₁)) i i *
          (res (Matrix.of h + Λ) ξ₁ * X) j j) ∂μ = ∫ h, ∑ j, (varProf D N θ i j : ℂ) *
      (res (Matrix.of h + Λ) ξ₂ i i *
        (res (Matrix.of h + Λ) ξ₂ * (E * (res (Matrix.of h + Λ) ξ₁ * X))) j j +
        (res (Matrix.of h + Λ) ξ₂ * (E * res (Matrix.of h + Λ) ξ₁)) i i *
          (res (Matrix.of h + Λ) ξ₁ * X) j j) ∂μ := fun i =>
    (integral_finsetSum _ fun j _ => (hint i j).const_mul _).symm
  simp only [hsum]
  rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [mul_add, Finset.sum_add_distrib]
  rw [FC_sum_varProf D N hD hN θ _ _, FC_sum_varProf D N hD hN θ _ _]

end

section

private theorem FC_int2 (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) {C' : ℕ → ℝ} (θ : ℝ)
    {μ : Measure (Idx D N → Idx D N → ℂ)} (hμ : LLClass D N C' θ μ)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (a : Fin D)
    (B : Matrix (Idx D N) (Idx D N) ℂ) :
    ∫ h, underTwoB Λ θ h z₁ z₂ a B ∂μ =
      (2 : ℂ) / ((D : ℂ) * N) * ((∑ i, ∑ j, ∫ h, (chainB h [(1, Λ, z₂), (B, Λ, z₁)] *
          ((1 / 2 : ℂ) • (Ea D N a * MExt Λ z₂))) i j * starRingEnd ℂ (h i j) ∂μ) -
        ∑ i, ∑ j, (FC_f μ [(1, Λ, z₂), (B, Λ, z₁)] ((1 / 2 : ℂ) • (Ea D N a * MExt Λ z₂)) i j 1 0 +
          FC_f μ [(1, Λ, z₂), (B, Λ, z₁)] ((1 / 2 : ℂ) • (Ea D N a * MExt Λ z₂)) i j 0 1)) := by
  have hprob := hμ.prob
  set X : Matrix (Idx D N) (Idx D N) ℂ := (1 / 2 : ℂ) • (Ea D N a * MExt Λ z₂) with hX
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hpt : ∀ᵐ h ∂μ, underTwoB Λ θ h z₁ z₂ a B =
      (2 : ℂ) / ((D : ℂ) * N) * (∑ i, (∑ j, (chainB h [(1, Λ, z₂), (B, Λ, z₁)] * X) i j *
        starRingEnd ℂ (h i j))) +
      2 * ntr (sTheta D N θ (res (Matrix.of h + Λ) z₂) * (res (Matrix.of h + Λ) z₂ *
          (B * (res (Matrix.of h + Λ) z₁ * X)))) +
      2 * ntr (sTheta D N θ (res (Matrix.of h + Λ) z₂ * (B * res (Matrix.of h + Λ) z₁)) *
          (res (Matrix.of h + Λ) z₁ * X)) := by
    filter_upwards [hμ.herm] with h hh
    exact FC_point2 hD hN θ Λ h hh z₁ z₂ a B
  rw [integral_congr_ae hpt]
  have hc : ∀ h, chainB h [(1, Λ, z₂), (B, Λ, z₁)] =
      res (Matrix.of h + Λ) z₂ * (B * res (Matrix.of h + Λ) z₁) := fun h => FC_chain2 h Λ B z₁ z₂
  have hF : ∀ i j, Integrable (fun h => (chainB h [(1, Λ, z₂), (B, Λ, z₁)] * X) i j *
      starRingEnd ℂ (h i j)) μ := by
    intro i j
    simp only [hc]
    refine Integrable.bdd_mul (c := (z.im)⁻¹ * (opNorm B * ((z.im)⁻¹ * opNorm X))) ?_ ?_ ?_
    · have := (hμ.integrable 1 i j)
      have hm : AEStronglyMeasurable (fun h : Idx D N → Idx D N → ℂ => starRingEnd ℂ (h i j)) μ :=
        (Complex.continuous_conj.comp ((continuous_apply j).comp (continuous_apply i))
          ).aestronglyMeasurable
      refine ⟨hm, ?_⟩
      have h2 := this.2
      simpa [HasFiniteIntegral, Complex.norm_conj] using h2
    · exact (FC_int_cont2 hμ.herm Λ hΛ z hz z₁ z₂ h₁ h₂ (fun p => (p.2 * (B * p.1) * X) i j)
        ((continuous_snd.matrix_mul (continuous_const.matrix_mul continuous_fst)).matrix_mul
          continuous_const |>.matrix_elem i j)).aestronglyMeasurable
    · filter_upwards [hμ.herm] with h hh
      have g1 := FC_opNorm_res _ (hh.add hΛ) z hz z₁ h₁
      have g2 := FC_opNorm_res _ (hh.add hΛ) z hz z₂ h₂
      refine FC_entry_le_inv _ _ ?_ i j
      refine (opNorm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (FC_opNorm_nonneg _)).trans ?_
      have g3 : opNorm (B * res (Matrix.of h + Λ) z₁) ≤ opNorm B * (z.im)⁻¹ :=
        (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left g1 (FC_opNorm_nonneg _))
      calc opNorm (res (Matrix.of h + Λ) z₂) * opNorm (B * res (Matrix.of h + Λ) z₁) * opNorm X ≤
            (z.im)⁻¹ * (opNorm B * (z.im)⁻¹) * opNorm X := by
            gcongr
            · exact FC_opNorm_nonneg _
            · exact FC_opNorm_nonneg _
        _ = _ := by ring
  have hS1 : Integrable (fun h => ntr (sTheta D N θ (res (Matrix.of h + Λ) z₂) *
      (res (Matrix.of h + Λ) z₂ * (B * (res (Matrix.of h + Λ) z₁ * X))))) μ :=
    FC_int_cont2 hμ.herm Λ hΛ z hz z₁ z₂ h₁ h₂ (fun p => ntr (sTheta D N θ p.2 *
      (p.2 * (B * (p.1 * X))))) (FC_cont_sThetaG D N hD θ _ _ continuous_snd
        (continuous_snd.matrix_mul (continuous_const.matrix_mul
          (continuous_fst.matrix_mul continuous_const))))
  have hS2 : Integrable (fun h => ntr (sTheta D N θ (res (Matrix.of h + Λ) z₂ *
      (B * res (Matrix.of h + Λ) z₁)) * (res (Matrix.of h + Λ) z₁ * X))) μ :=
    FC_int_cont2 hμ.herm Λ hΛ z hz z₁ z₂ h₁ h₂ (fun p => ntr (sTheta D N θ (p.2 * (B * p.1)) *
      (p.1 * X))) (FC_cont_sThetaG D N hD θ _ _
        (continuous_snd.matrix_mul (continuous_const.matrix_mul continuous_fst))
        (continuous_fst.matrix_mul continuous_const))
  have hI1 : Integrable (fun h => (2 : ℂ) / ((D : ℂ) * N) * ∑ i, ∑ j,
      (chainB h [(1, Λ, z₂), (B, Λ, z₁)] * X) i j * starRingEnd ℂ (h i j)) μ :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hF i j).const_mul _
  rw [integral_add (f := fun h => (2 : ℂ) / ((D : ℂ) * N) * (∑ i, (∑ j,
      (chainB h [(1, Λ, z₂), (B, Λ, z₁)] * X) i j * starRingEnd ℂ (h i j))) +
      2 * ntr (sTheta D N θ (res (Matrix.of h + Λ) z₂) * (res (Matrix.of h + Λ) z₂ *
          (B * (res (Matrix.of h + Λ) z₁ * X))))) (hI1.add (hS1.const_mul _)) (hS2.const_mul _),
    integral_add hI1 (hS1.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hF i j]
  simp only [integral_finsetSum _ fun j _ => hF _ j]
  rw [FC_second2 D N hD hN θ hμ Λ hΛ z hz z₁ z₂ h₁ h₂ B X, integral_add hS1 hS2]
  field_simp
  ring

end

section

private theorem FC_D221 : (FC_Dpq 2 2 1).filter (fun m => FC_offc m == 0) =
    [[((0, 1, false, false), false, false), ((0, 1, true, false), true, true),
      ((0, 1, true, false), false, false), ((0, 2, true, true), true, true)],
     [((0, 1, false, false), false, false), ((0, 1, true, false), true, true),
      ((0, 2, true, false), false, false), ((1, 2, true, true), true, true)],
     [((0, 1, false, false), false, false), ((0, 1, true, false), true, true),
      ((0, 1, true, false), false, false), ((0, 2, true, true), true, true)],
     [((0, 1, false, false), false, false), ((0, 1, true, false), true, true),
      ((0, 2, true, false), false, false), ((1, 2, true, true), true, true)],
     [((0, 1, false, false), false, false), ((0, 2, true, false), true, true),
      ((1, 2, true, false), false, false), ((1, 2, true, true), true, true)],
     [((0, 2, false, false), false, false), ((1, 2, true, false), true, true),
      ((1, 2, true, false), false, false), ((1, 2, true, true), true, true)],
     [((0, 1, false, false), false, false), ((0, 2, true, false), true, true),
      ((1, 2, true, false), false, false), ((1, 2, true, true), true, true)],
     [((0, 2, false, false), false, false), ((1, 2, true, false), true, true),
      ((1, 2, true, false), false, false), ((1, 2, true, true), true, true)]] := by decide

private def FC_T4 {ι : Type*} [Fintype ι] (G₁ G₂ E X : Matrix ι ι ℂ) (i j : ι) : ℂ :=
  G₂ i i ^ 2 * G₂ j j * (G₂ * (E * (G₁ * X))) j j +
    G₂ i i * G₂ j j * (G₂ * (E * G₁)) i i * (G₁ * X) j j +
    G₂ i i * (G₂ * (E * G₁)) j j * G₁ i i * (G₁ * X) j j +
    (G₂ * (E * G₁)) i i * G₁ j j * G₁ i i * (G₁ * X) j j

private theorem FC_eval221 {D N : ℕ} (h : Idx D N → Idx D N → ℂ) (Λ E : Matrix (Idx D N) (Idx D N) ℂ)
    (ξ₁ ξ₂ : ℂ) (X : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) :
    FC_evalPoly h [(1, Λ, ξ₂), (E, Λ, ξ₁)] X i j
      ((FC_Dpq 2 2 1).filter (fun m => FC_offc m == 0)) =
    2 * FC_T4 (res (Matrix.of h + Λ) ξ₁) (res (Matrix.of h + Λ) ξ₂) E X i j := by
  rw [FC_D221]
  simp [FC_evalPoly, FC_evalMono, FC_evalFac, FC_seg2a, FC_seg2b, FC_seg2c, FC_idx, FC_T4]
  ring

private theorem FC_lead2_eq (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) (t : ℝ)
    (Λ E : Matrix (Idx D N) (Idx D N) ℂ) (ξ₁ ξ₂ : ℂ) (X : Matrix (Idx D N) (Idx D N) ℂ) :
    FC_lead (ouMatLaw D N L t) [(1, Λ, ξ₂), (E, Λ, ξ₁)] X =
      -(((Real.exp (-(2 * t)) / (N : ℝ) ^ 2 : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2) *
        ∑ i, ∑ j, (if i.1 = j.1 ∧ i ≠ j then ∫ h, FC_T4 (res (Matrix.of h + Λ) ξ₁)
          (res (Matrix.of h + Λ) ξ₂) E X i j ∂(ouMatLaw D N L t) else 0) := by
  unfold FC_lead
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlen : ([(1, Λ, ξ₂), (E, Λ, ξ₁)] : FC_Ch D N).length = 2 := rfl
  by_cases hij : i ≠ j
  · rw [if_pos hij]
    simp only [hlen, FC_eval221]
    by_cases hb : i.1 = j.1
    · rw [(ouMatLaw_ccum D N L t i j).2 hb hij, if_pos ⟨hb, hij⟩, integral_const_mul]
      norm_num
      ring
    · rw [(ouMatLaw_ccum D N L t i j).1 hb 2 (1 + 1) (by norm_num), if_neg (fun h => hb h.1)]
      simp
  · rw [if_neg hij, if_neg (fun h => hij h.2)]; simp

end

section

private def FC_T4M {ι : Type*} [Fintype ι] (G₁ G₂ M₁ M₂ E X : Matrix ι ι ℂ) (i j : ι) : ℂ :=
  (M₂ i i * M₂ i i) * ((G₂ * (E * (G₁ * X))) j j * M₂ j j) +
    ((G₂ * (E * G₁)) i i * M₂ i i) * ((M₁ * X) j j * M₂ j j) +
    (M₁ i i * M₂ i i) * ((G₂ * (E * G₁)) j j * (M₁ * X) j j) +
    ((G₂ * (E * G₁)) i i * M₁ i i) * ((M₁ * X) j j * M₁ j j)

private theorem FC_blk_tr (D N : ℕ) (W : Matrix (Idx D N) (Idx D N) ℂ) (c : Idx D N → ℂ) (y : Fin D) :
    ∑ i, (if i.1 = y then W i i * c i else 0) = ((D : ℂ) * N) * ntr (W * diagonal c * Ea D N y) := by
  have hc : ((D : ℂ) * N) = 0 ∨ ((D : ℂ) * N) ≠ 0 := Classical.em _
  rw [FC_ntr_Ea]
  simp only [Matrix.mul_diagonal]
  rcases hc with h0 | h0
  · have hD : D = 0 ∨ N = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    rcases hD with rfl | rfl
    · exact (Fin.elim0 y)
    · simp [Finset.univ_eq_empty]
  · rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]

private theorem FC_blk_prod {D N : ℕ} (f g : Idx D N → ℂ) :
    ∑ i, ∑ j, (if i.1 = j.1 then f i * g j else 0) =
      ∑ y : Fin D, (∑ i, if i.1 = y then f i else 0) * (∑ j, if j.1 = y then g j else 0) := by
  have hm : ∀ y : Fin D, (∑ i, if i.1 = y then f i else 0) * (∑ j, if j.1 = y then g j else 0) =
      ∑ i, ∑ j, (if i.1 = y then f i else 0) * (if j.1 = y then g j else 0) :=
    fun y => Finset.sum_mul_sum _ _ _ _
  conv_rhs => rw [Finset.sum_congr rfl fun y _ => hm y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single i.1]
  · by_cases hb : i.1 = j.1
    · rw [if_pos hb, if_pos rfl, if_pos hb.symm]
    · rw [if_neg hb, if_pos rfl, if_neg (Ne.symm hb), mul_zero]
  · intro y _ hy; rw [if_neg (Ne.symm hy), zero_mul]
  · simp

private theorem FC_fact (D N : ℕ) (G₁ G₂ M₁ M₂ E X : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i, ∑ j, (if i.1 = j.1 then FC_T4M G₁ G₂ M₁ M₂ E X i j else 0) =
      ((D : ℂ) * N) ^ 2 * ∑ y : Fin D,
        (ntr (diagonal (diag M₂) * diagonal (diag M₂) * Ea D N y) *
            ntr (G₂ * (E * (G₁ * X)) * diagonal (diag M₂) * Ea D N y) +
          ntr (G₂ * (E * G₁) * diagonal (diag M₂) * Ea D N y) *
            ntr (M₁ * X * diagonal (diag M₂) * Ea D N y) +
          ntr (M₁ * diagonal (diag M₂) * Ea D N y) *
            ntr (G₂ * (E * G₁) * diagonal (diag (M₁ * X)) * Ea D N y) +
          ntr (G₂ * (E * G₁) * diagonal (diag M₁) * Ea D N y) *
            ntr (M₁ * X * diagonal (diag M₁) * Ea D N y)) := by
  have e : ∀ i j, (if i.1 = j.1 then FC_T4M G₁ G₂ M₁ M₂ E X i j else 0) =
      (if i.1 = j.1 then (M₂ i i * M₂ i i) * ((G₂ * (E * (G₁ * X))) j j * M₂ j j) else 0) +
      (if i.1 = j.1 then ((G₂ * (E * G₁)) i i * M₂ i i) * ((M₁ * X) j j * M₂ j j) else 0) +
      (if i.1 = j.1 then (M₁ i i * M₂ i i) * ((G₂ * (E * G₁)) j j * (M₁ * X) j j) else 0) +
      (if i.1 = j.1 then ((G₂ * (E * G₁)) i i * M₁ i i) * ((M₁ * X) j j * M₁ j j) else 0) := by
    intro i j; unfold FC_T4M; split_ifs <;> simp
  simp only [e, Finset.sum_add_distrib, FC_blk_prod]
  have t : ∀ (W : Matrix (Idx D N) (Idx D N) ℂ) (c : Idx D N → ℂ) (y : Fin D),
      (∑ i, if i.1 = y then W i i * c i else 0) = ((D : ℂ) * N) * ntr (W * diagonal c * Ea D N y) :=
    FC_blk_tr D N
  have t1 : ∀ y : Fin D, (∑ i, if i.1 = y then M₂ i i * M₂ i i else 0) =
      ((D : ℂ) * N) * ntr (diagonal (diag M₂) * diagonal (diag M₂) * Ea D N y) := by
    intro y
    rw [← t]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.diagonal_apply]
  have t2 : ∀ (W : Matrix (Idx D N) (Idx D N) ℂ) (y : Fin D),
      (∑ i, if i.1 = y then W i i * M₂ i i else 0) =
        ((D : ℂ) * N) * ntr (W * diagonal (diag M₂) * Ea D N y) := fun W y => t W _ y
  have t3 : ∀ (W : Matrix (Idx D N) (Idx D N) ℂ) (y : Fin D),
      (∑ i, if i.1 = y then W i i * M₁ i i else 0) =
        ((D : ℂ) * N) * ntr (W * diagonal (diag M₁) * Ea D N y) := fun W y => t W _ y
  have t4 : ∀ y : Fin D, (∑ i, if i.1 = y then M₁ i i * M₂ i i else 0) =
      ((D : ℂ) * N) * ntr (M₁ * diagonal (diag M₂) * Ea D N y) := fun y => t M₁ _ y
  have t5 : ∀ y : Fin D, (∑ i, if i.1 = y then (G₂ * (E * G₁)) i i * (M₁ * X) i i else 0) =
      ((D : ℂ) * N) * ntr (G₂ * (E * G₁) * diagonal (diag (M₁ * X)) * Ea D N y) :=
    fun y => t _ _ y
  simp only [t1, t2, t3, t4, t5, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

private theorem FC_diag_Ea_comm (D N : ℕ) (v : Idx D N → ℂ) (y : Fin D) :
    diagonal v * Ea D N y = Ea D N y * diagonal v := by
  unfold Ea; rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext p; ring

private theorem FC_lead14_eq (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (θ : ℝ) (z₁ z₂ : ℂ)
    (a b : Fin D) :
    lead14 Λ θ z₁ z₂ a b = 2 * (D : ℂ) * ∑ y : Fin D,
      (ntr (diagonal (diag (MExt Λ z₂)) * diagonal (diag (MExt Λ z₂)) * Ea D N y) *
          (∑ w, (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ b w * ntr (MExt Λ z₂ * Ea D N w * MExt Λ z₁ *
            ((1 / 2 : ℂ) • (Ea D N a * MExt Λ z₂) * diagonal (diag (MExt Λ z₂)) * Ea D N y))) +
        (∑ w, (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ b w * ntr (MExt Λ z₂ * Ea D N w * MExt Λ z₁ *
            (diagonal (diag (MExt Λ z₂)) * Ea D N y))) *
          ntr (MExt Λ z₁ * ((1 / 2 : ℂ) • (Ea D N a * MExt Λ z₂)) * diagonal (diag (MExt Λ z₂)) *
            Ea D N y) +
        ntr (MExt Λ z₁ * diagonal (diag (MExt Λ z₂)) * Ea D N y) *
          (∑ w, (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ b w * ntr (MExt Λ z₂ * Ea D N w * MExt Λ z₁ *
            (diagonal (diag (MExt Λ z₁ * ((1 / 2 : ℂ) • (Ea D N a * MExt Λ z₂)))) * Ea D N y))) +
        (∑ w, (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ b w * ntr (MExt Λ z₂ * Ea D N w * MExt Λ z₁ *
            (diagonal (diag (MExt Λ z₁)) * Ea D N y))) *
          ntr (MExt Λ z₁ * ((1 / 2 : ℂ) • (Ea D N a * MExt Λ z₂)) * diagonal (diag (MExt Λ z₁)) *
            Ea D N y)) := by
  unfold lead14 KThetaB
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  generalize MExt Λ z₁ = M₁
  generalize MExt Λ z₂ = M₂
  generalize (1 - Mhat Λ z₂ z₁ * PTheta D θ)⁻¹ = R
  have hc := FC_diag_Ea_comm D N
  have e1 : ∀ w, ntr (M₂ * Ea D N w * M₁ * ((1 / 2 : ℂ) • (Ea D N a * M₂) * diagonal (diag M₂) *
      Ea D N y)) = (1 / 2 : ℂ) * ntr (M₂ * Ea D N w * M₁ * Ea D N a * (M₂ * diagonal (diag M₂) *
        Ea D N y)) := by
    intro w
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, FC_ntr_smul]
    simp only [Matrix.mul_assoc]
  have e2 : ∀ (v : Idx D N → ℂ) w, ntr (M₂ * Ea D N w * M₁ * (diagonal v * Ea D N y)) =
      ntr (M₂ * Ea D N w * M₁ * Ea D N y * diagonal v) := by
    intro v w; rw [hc v y]; simp only [Matrix.mul_assoc]
  have e3 : diagonal (diag (M₁ * ((1 / 2 : ℂ) • (Ea D N a * M₂)))) =
      (1 / 2 : ℂ) • diagonal (diag (M₁ * Ea D N a * M₂)) := by
    ext p q
    by_cases hpq : p = q
    · subst hpq; simp [Matrix.diagonal_apply, Matrix.mul_smul, Matrix.mul_assoc]
    · simp [Matrix.diagonal_apply, hpq]
  have e4 : ∀ (B : Matrix (Idx D N) (Idx D N) ℂ), ntr (M₁ * ((1 / 2 : ℂ) • (Ea D N a * M₂)) * B *
      Ea D N y) = (1 / 2 : ℂ) * ntr (M₁ * Ea D N a * M₂ * B * Ea D N y) := by
    intro B
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, FC_ntr_smul]
    simp only [Matrix.mul_assoc]
  simp only [e1, e2, e3, e4]
  have e5 : ∀ w, ntr (M₂ * Ea D N w * M₁ * Ea D N y * ((1 / 2 : ℂ) •
      diagonal (diag (M₁ * Ea D N a * M₂)))) = (1 / 2 : ℂ) * ntr (M₂ * Ea D N w * M₁ * Ea D N y *
        diagonal (diag (M₁ * Ea D N a * M₂))) := by
    intro w; rw [Matrix.mul_smul, FC_ntr_smul]
  have e6 : ∀ w, ntr (M₂ * Ea D N w * M₁ * ((1 / 2 : ℂ) • diagonal (diag (M₁ * Ea D N a * M₂)) *
      Ea D N y)) = (1 / 2 : ℂ) * ntr (M₂ * Ea D N w * M₁ * Ea D N y *
        diagonal (diag (M₁ * Ea D N a * M₂))) := by
    intro w
    rw [Matrix.smul_mul, Matrix.mul_smul, FC_ntr_smul, e2]
  simp only [e6, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

end

section

private theorem FC_tri3 (a b c a' b' c' : ℂ) (δ : ℝ) (ha : ‖a‖ ≤ 3) (hb : ‖b‖ ≤ 3) (hc : ‖c‖ ≤ 3)
    (ha' : ‖a'‖ ≤ 3) (hb' : ‖b'‖ ≤ 3) (hda : ‖a - a'‖ ≤ δ) (hdb : ‖b - b'‖ ≤ δ)
    (hdc : ‖c - c'‖ ≤ δ) : ‖a * b * c - a' * b' * c'‖ ≤ 27 * δ := by
  have e : a * b * c - a' * b' * c' = (a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c') := by
    ring
  rw [e]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hda
  have t1 : ‖(a - a') * b * c‖ ≤ δ * 3 * 3 := by
    rw [norm_mul, norm_mul]; gcongr
  have t2 : ‖a' * (b - b') * c‖ ≤ 3 * δ * 3 := by
    rw [norm_mul, norm_mul]; gcongr
  have t3 : ‖a' * b' * (c - c')‖ ≤ 3 * 3 * δ := by
    rw [norm_mul, norm_mul]; gcongr
  calc _ ≤ ‖(a - a') * b * c‖ + ‖a' * (b - b') * c‖ + ‖a' * b' * (c - c')‖ := norm_add₃_le
    _ ≤ _ := by linarith

private theorem FC_mul4_le (a b c w : ℂ) (K W : ℝ) (ha : ‖a‖ ≤ K) (hb : ‖b‖ ≤ K) (hc : ‖c‖ ≤ K)
    (hw : ‖w‖ ≤ W) : ‖a * b * c * w‖ ≤ K ^ 3 * W := by
  have hK : 0 ≤ K := (norm_nonneg _).trans ha
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖a‖ * ‖b‖ * ‖c‖ * ‖w‖ ≤ K * K * K * W := by gcongr
    _ = _ := by ring

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem FC_T4_diff (G₁ G₂ M₁ M₂ E X : Matrix ι ι ℂ) (δ W : ℝ) (hW : 0 ≤ W)
    (d1 : ∀ x y, ‖G₁ x y - M₁ x y‖ ≤ δ) (d2 : ∀ x y, ‖G₂ x y - M₂ x y‖ ≤ δ)
    (d3 : ∀ x y, ‖(G₁ * X) x y - (M₁ * X) x y‖ ≤ δ)
    (b1 : ∀ x y, ‖G₁ x y‖ ≤ 3) (b2 : ∀ x y, ‖G₂ x y‖ ≤ 3) (b3 : ∀ x y, ‖(G₁ * X) x y‖ ≤ 3)
    (c1 : ∀ x y, ‖M₁ x y‖ ≤ 3) (c2 : ∀ x y, ‖M₂ x y‖ ≤ 3) (c3 : ∀ x y, ‖(M₁ * X) x y‖ ≤ 3)
    (hY : ∀ x y, ‖(G₂ * (E * G₁)) x y‖ ≤ W) (hZ : ∀ x y, ‖(G₂ * (E * (G₁ * X))) x y‖ ≤ W)
    (i j : ι) : ‖FC_T4 G₁ G₂ E X i j - FC_T4M G₁ G₂ M₁ M₂ E X i j‖ ≤ 108 * δ * W := by
  have e : FC_T4 G₁ G₂ E X i j - FC_T4M G₁ G₂ M₁ M₂ E X i j =
      (G₂ i i * G₂ i i * G₂ j j - M₂ i i * M₂ i i * M₂ j j) * (G₂ * (E * (G₁ * X))) j j +
      (G₂ i i * G₂ j j * (G₁ * X) j j - M₂ i i * M₂ j j * (M₁ * X) j j) * (G₂ * (E * G₁)) i i +
      (G₂ i i * G₁ i i * (G₁ * X) j j - M₂ i i * M₁ i i * (M₁ * X) j j) * (G₂ * (E * G₁)) j j +
      (G₁ j j * G₁ i i * (G₁ * X) j j - M₁ j j * M₁ i i * (M₁ * X) j j) * (G₂ * (E * G₁)) i i := by
    unfold FC_T4 FC_T4M; ring
  rw [e]
  have t : ∀ (u v : ℂ), ‖u‖ ≤ 27 * δ → ‖v‖ ≤ W → ‖u * v‖ ≤ 27 * δ * W := by
    intro u v hu hv
    rw [norm_mul]; exact mul_le_mul hu hv (norm_nonneg _) ((norm_nonneg _).trans hu)
  have s1 := t _ _ (FC_tri3 _ _ _ _ _ _ δ (b2 i i) (b2 i i) (b2 j j) (c2 i i) (c2 i i)
    (d2 i i) (d2 i i) (d2 j j)) (hZ j j)
  have s2 := t _ _ (FC_tri3 _ _ _ _ _ _ δ (b2 i i) (b2 j j) (b3 j j) (c2 i i) (c2 j j)
    (d2 i i) (d2 j j) (d3 j j)) (hY i i)
  have s3 := t _ _ (FC_tri3 _ _ _ _ _ _ δ (b2 i i) (b1 i i) (b3 j j) (c2 i i) (c1 i i)
    (d2 i i) (d1 i i) (d3 j j)) (hY j j)
  have s4 := t _ _ (FC_tri3 _ _ _ _ _ _ δ (b1 j j) (b1 i i) (b3 j j) (c1 j j) (c1 i i)
    (d1 j j) (d1 i i) (d3 j j)) (hY i i)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_add₃_le) le_rfl
    _ ≤ _ := by linarith

private theorem FC_T4_le (G₁ G₂ E X : Matrix ι ι ℂ) (K W : ℝ)
    (b1 : ∀ x y, ‖G₁ x y‖ ≤ K) (b2 : ∀ x y, ‖G₂ x y‖ ≤ K) (b3 : ∀ x y, ‖(G₁ * X) x y‖ ≤ K)
    (hY : ∀ x y, ‖(G₂ * (E * G₁)) x y‖ ≤ W) (hZ : ∀ x y, ‖(G₂ * (E * (G₁ * X))) x y‖ ≤ W)
    (i j : ι) : ‖FC_T4 G₁ G₂ E X i j‖ ≤ 4 * (K ^ 3 * W) := by
  unfold FC_T4
  have e1 : G₂ i i ^ 2 * G₂ j j * (G₂ * (E * (G₁ * X))) j j =
      G₂ i i * G₂ i i * G₂ j j * (G₂ * (E * (G₁ * X))) j j := by ring
  have e2 : G₂ i i * G₂ j j * (G₂ * (E * G₁)) i i * (G₁ * X) j j =
      G₂ i i * G₂ j j * (G₁ * X) j j * (G₂ * (E * G₁)) i i := by ring
  have e3 : G₂ i i * (G₂ * (E * G₁)) j j * G₁ i i * (G₁ * X) j j =
      G₂ i i * G₁ i i * (G₁ * X) j j * (G₂ * (E * G₁)) j j := by ring
  have e4 : (G₂ * (E * G₁)) i i * G₁ j j * G₁ i i * (G₁ * X) j j =
      G₁ j j * G₁ i i * (G₁ * X) j j * (G₂ * (E * G₁)) i i := by ring
  rw [e1, e2, e3, e4]
  have s1 := FC_mul4_le _ _ _ _ K W (b2 i i) (b2 i i) (b2 j j) (hZ j j)
  have s2 := FC_mul4_le _ _ _ _ K W (b2 i i) (b2 j j) (b3 j j) (hY i i)
  have s3 := FC_mul4_le _ _ _ _ K W (b2 i i) (b1 i i) (b3 j j) (hY j j)
  have s4 := FC_mul4_le _ _ _ _ K W (b1 j j) (b1 i i) (b3 j j) (hY i i)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_add₃_le) le_rfl
    _ ≤ _ := by linarith

private theorem FC_T4M_le (G₁ G₂ M₁ M₂ E X : Matrix ι ι ℂ) (K W : ℝ)
    (c1 : ∀ x y, ‖M₁ x y‖ ≤ K) (c2 : ∀ x y, ‖M₂ x y‖ ≤ K) (c3 : ∀ x y, ‖(M₁ * X) x y‖ ≤ K)
    (hY : ∀ x y, ‖(G₂ * (E * G₁)) x y‖ ≤ W) (hZ : ∀ x y, ‖(G₂ * (E * (G₁ * X))) x y‖ ≤ W)
    (i j : ι) : ‖FC_T4M G₁ G₂ M₁ M₂ E X i j‖ ≤ 4 * (K ^ 3 * W) := by
  unfold FC_T4M
  have e1 : (M₂ i i * M₂ i i) * ((G₂ * (E * (G₁ * X))) j j * M₂ j j) =
      M₂ i i * M₂ i i * M₂ j j * (G₂ * (E * (G₁ * X))) j j := by ring
  have e2 : ((G₂ * (E * G₁)) i i * M₂ i i) * ((M₁ * X) j j * M₂ j j) =
      M₂ i i * M₂ j j * (M₁ * X) j j * (G₂ * (E * G₁)) i i := by ring
  have e3 : (M₁ i i * M₂ i i) * ((G₂ * (E * G₁)) j j * (M₁ * X) j j) =
      M₂ i i * M₁ i i * (M₁ * X) j j * (G₂ * (E * G₁)) j j := by ring
  have e4 : ((G₂ * (E * G₁)) i i * M₁ i i) * ((M₁ * X) j j * M₁ j j) =
      M₁ j j * M₁ i i * (M₁ * X) j j * (G₂ * (E * G₁)) i i := by ring
  rw [e1, e2, e3, e4]
  have s1 := FC_mul4_le _ _ _ _ K W (c2 i i) (c2 i i) (c2 j j) (hZ j j)
  have s2 := FC_mul4_le _ _ _ _ K W (c2 i i) (c2 j j) (c3 j j) (hY i i)
  have s3 := FC_mul4_le _ _ _ _ K W (c2 i i) (c1 i i) (c3 j j) (hY j j)
  have s4 := FC_mul4_le _ _ _ _ K W (c1 j j) (c1 i i) (c3 j j) (hY i i)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_add₃_le) le_rfl
    _ ≤ _ := by linarith

end

end

section

private theorem FC_exp_close {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : Ω → ℂ) (hF : Integrable F μ) (c : ℂ) (e₀ K ε : ℝ) (he₀ : 0 ≤ e₀) (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (hb : ∀ᵐ x ∂μ, ‖F x‖ ≤ K) (hp : μ {x | e₀ < ‖F x - c‖} ≤ ENNReal.ofReal ε) :
    ‖(∫ x, F x ∂μ) - c‖ ≤ e₀ + (K + ‖c‖) * ε := by
  have e : (∫ x, F x ∂μ) - c = ∫ x, (F x - c) ∂μ := by
    rw [integral_sub hF (integrable_const _), integral_const]; simp
  rw [e]
  refine FC_int_split _ (hF.sub (integrable_const _)).aestronglyMeasurable {x | ‖F x - c‖ ≤ e₀}
    e₀ (K + ‖c‖) ε he₀ (by positivity) (Filter.Eventually.of_forall fun x hx => hx) ?_ ?_ hε
  · filter_upwards [hb] with x hx
    exact (norm_sub_le _ _).trans (by linarith)
  · have : {x | ‖F x - c‖ ≤ e₀}ᶜ = {x | e₀ < ‖F x - c‖} := by
      ext x; simp
    rw [this]; exact hp

private theorem FC_int_lin {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {D : ℕ} (K : ℂ)
    (c1 c2 c3 c4 : Fin D → ℂ) (F1 F2 F3 F4 : Fin D → Ω → ℂ)
    (h1 : ∀ y, Integrable (F1 y) μ) (h2 : ∀ y, Integrable (F2 y) μ)
    (h3 : ∀ y, Integrable (F3 y) μ) (h4 : ∀ y, Integrable (F4 y) μ) :
    ∫ x, K * ∑ y, (c1 y * F1 y x + F2 y x * c2 y + c3 y * F3 y x + F4 y x * c4 y) ∂μ =
      K * ∑ y, (c1 y * ∫ x, F1 y x ∂μ + (∫ x, F2 y x ∂μ) * c2 y + c3 y * ∫ x, F3 y x ∂μ +
        (∫ x, F4 y x ∂μ) * c4 y) := by
  have hi : ∀ y, Integrable (fun x => c1 y * F1 y x + F2 y x * c2 y + c3 y * F3 y x +
      F4 y x * c4 y) μ := fun y =>
    ((((h1 y).const_mul _).add ((h2 y).mul_const _)).add ((h3 y).const_mul _)).add
      ((h4 y).mul_const _)
  rw [integral_const_mul, integral_finsetSum _ fun y _ => hi y]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  have a1 : Integrable (fun x => c1 y * F1 y x) μ := (h1 y).const_mul _
  have a2 : Integrable (fun x => F2 y x * c2 y) μ := (h2 y).mul_const _
  have a3 : Integrable (fun x => c3 y * F3 y x) μ := (h3 y).const_mul _
  have a4 : Integrable (fun x => F4 y x * c4 y) μ := (h4 y).mul_const _
  rw [integral_add (f := fun x => c1 y * F1 y x + F2 y x * c2 y + c3 y * F3 y x)
      ((a1.add a2).add a3) a4,
    integral_add (f := fun x => c1 y * F1 y x + F2 y x * c2 y) (a1.add a2) a3,
    integral_add a1 a2, integral_const_mul, integral_mul_const, integral_const_mul,
    integral_mul_const]

end

section

private theorem FC_cont_T4M {ι : Type*} [Fintype ι] [DecidableEq ι] (M₁ M₂ E X : Matrix ι ι ℂ)
    (i j : ι) : Continuous fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => FC_T4M p.1 p.2 M₁ M₂ E X i j := by
  unfold FC_T4M
  have hY : ∀ x y : ι, Continuous fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => (p.2 * (E * p.1)) x y :=
    fun x y => (continuous_snd.matrix_mul (continuous_const.matrix_mul continuous_fst)).matrix_elem x y
  have hZ : ∀ x y : ι, Continuous fun p : Matrix ι ι ℂ × Matrix ι ι ℂ =>
      (p.2 * (E * (p.1 * X))) x y := fun x y =>
    (continuous_snd.matrix_mul (continuous_const.matrix_mul
      (continuous_fst.matrix_mul continuous_const))).matrix_elem x y
  exact (((continuous_const.mul ((hZ j j).mul continuous_const)).add
    (((hY i i).mul continuous_const).mul continuous_const)).add
      (continuous_const.mul ((hY j j).mul continuous_const))).add
        (((hY i i).mul continuous_const).mul continuous_const)

private theorem FC_cont_T4 {ι : Type*} [Fintype ι] [DecidableEq ι] (E X : Matrix ι ι ℂ) (i j : ι) :
    Continuous fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => FC_T4 p.1 p.2 E X i j := by
  unfold FC_T4
  fun_prop

private theorem FC_int_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : Ω → ℂ) (hf : AEStronglyMeasurable f μ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ K) : ‖∫ x, f x ∂μ‖ ≤ K := by
  have := FC_int_split f hf Set.univ K K 0 hK hK (hb.mono fun x hx _ => hx) hb (by simp) le_rfl
  simpa using this

set_option maxHeartbeats 4000000 in
private theorem FC_P14_step (D N : ℕ) (hD : 2 ≤ D) (hN : 1 ≤ N) {C : ℕ → ℝ} (L : EntryLaws C)
    (t : ℝ) (ht : 0 ≤ t) {C' : ℕ → ℝ} (hμ : LLClass D N C' (Real.exp (-t)) (ouMatLaw D N L t))
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im) (hz1 : z.im ≤ 1) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (a b : Fin D)
    (hM₁ : opNorm (MExt (lam D N A) z₁) ≤ 5 / 4) (hM₂ : opNorm (MExt (lam D N A) z₂) ≤ 5 / 4)
    (Kc : ℝ)
    (hcore : ‖(∑ i, ∑ j, ∫ h, (chainB h [(1, lam D N A, z₂), (Ea D N b, lam D N A, z₁)] *
          ((1 / 2 : ℂ) • (Ea D N a * MExt (lam D N A) z₂))) i j * starRingEnd ℂ (h i j)
            ∂(ouMatLaw D N L t)) -
        (∑ i, ∑ j, (FC_f (ouMatLaw D N L t) [(1, lam D N A, z₂), (Ea D N b, lam D N A, z₁)]
          ((1 / 2 : ℂ) • (Ea D N a * MExt (lam D N A) z₂)) i j 1 0 +
          FC_f (ouMatLaw D N L t) [(1, lam D N A, z₂), (Ea D N b, lam D N A, z₁)]
            ((1 / 2 : ℂ) • (Ea D N a * MExt (lam D N A) z₂)) i j 0 1)) -
        FC_lead (ouMatLaw D N L t) [(1, lam D N A, z₂), (Ea D N b, lam D N A, z₁)]
          ((1 / 2 : ℂ) • (Ea D N a * MExt (lam D N A) z₂))‖ ≤ Kc)
    (S : Set (Idx D N → Idx D N → ℂ)) (ε : ℝ) (hε : 0 ≤ ε)
    (hSc : ouMatLaw D N L t Sᶜ ≤ ENNReal.ofReal ε) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hiso : ∀ h ∈ S, (Matrix.of h).IsHermitian →
      FC_iso (res (Matrix.of h + lam D N A) z₁) (MExt (lam D N A) z₁)
        ((1 / 2 : ℂ) • (Ea D N a * MExt (lam D N A) z₂)) δ ∧
      FC_iso (res (Matrix.of h + lam D N A) z₂) (MExt (lam D N A) z₂)
        ((1 / 2 : ℂ) • (Ea D N a * MExt (lam D N A) z₂)) δ)
    (eB : ℝ) (heB : 0 ≤ eB)
    (hBB : ∀ B' : Matrix (Idx D N) (Idx D N) ℂ, opNorm B' ≤ 1 →
      ‖(∫ h, ntr (res (Matrix.of h + lam D N A) z₂ * Ea D N b * res (Matrix.of h + lam D N A) z₁ *
          B') ∂(ouMatLaw D N L t)) -
        ∑ w, (1 - Mhat (lam D N A) z₂ z₁ * PTheta D (Real.exp (-t)))⁻¹ b w *
          ntr (MExt (lam D N A) z₂ * Ea D N w * MExt (lam D N A) z₁ * B')‖ ≤ eB)
    (Kν : ℝ) (hKν : ‖ccum (L.νo : Measure ℂ) 2 2‖ ≤ Kν) :
    ‖-(D : ℂ) * (∫ h, underTwoB (lam D N A) (Real.exp (-t)) h z₁ z₂ a (Ea D N b)
          ∂(ouMatLaw D N L t)) -
        ((D * Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 *
          lead14 (lam D N A) (Real.exp (-t)) z₁ z₂ a b‖ ≤
      2 / N * Kc + 2 * Kν / N ^ 3 * (D * N ^ 2 * (324 * δ * (z.im)⁻¹ + 12 * (z.im)⁻¹ ^ 5 * ε) +
        8 * D * N * (z.im)⁻¹ ^ 2 + 16 * D ^ 3 * N ^ 2 * eB) := by
  have hprob := hμ.prob
  have hD1 : 1 ≤ D := by omega
  have hΛ := lam_isHermitian D N A
  have hηi : 0 ≤ (z.im)⁻¹ := inv_nonneg.2 hz.le
  have hη1 : 1 ≤ (z.im)⁻¹ := one_le_inv₀ hz |>.2 hz1
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hDr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < N := by linarith
  have hKν0 : 0 ≤ Kν := (norm_nonneg _).trans hKν
  rw [FC_int2 D N hD1 hN (Real.exp (-t)) hμ (lam D N A) hΛ z hz z₁ z₂ h₁ h₂ a (Ea D N b)]
  set μ := ouMatLaw D N L t
  set Λ := lam D N A
  set M₁ := MExt Λ z₁ with hM₁d
  set M₂ := MExt Λ z₂ with hM₂d
  set E := Ea D N b with hEd
  set X : Matrix (Idx D N) (Idx D N) ℂ := (1 / 2 : ℂ) • (Ea D N a * M₂) with hXd
  set I1 := ∑ i, ∑ j, ∫ h, (chainB h [(1, Λ, z₂), (E, Λ, z₁)] * X) i j *
    starRingEnd ℂ (h i j) ∂μ
  set Sec := ∑ i, ∑ j, (FC_f μ [(1, Λ, z₂), (E, Λ, z₁)] X i j 1 0 +
    FC_f μ [(1, Λ, z₂), (E, Λ, z₁)] X i j 0 1)
  set Ld := FC_lead μ [(1, Λ, z₂), (E, Λ, z₁)] X
  set α' : ℂ := ((Real.exp (-(2 * t)) / (N : ℝ) ^ 2 : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2
    with hα'd
  set R := (1 - Mhat Λ z₂ z₁ * PTheta D (Real.exp (-t)))⁻¹ with hRd
  have hM10 := FC_opNorm_nonneg M₁
  have hM20 := FC_opNorm_nonneg M₂
  have hE1 : opNorm E ≤ 1 := FC_opNorm_Ea D N b
  have hX58 : opNorm X ≤ 5 / 8 := by
    rw [hXd, opNorm_smul]
    have h1 := opNorm_mul_le (Ea D N a) M₂
    have h2 : opNorm (Ea D N a) * opNorm M₂ ≤ 1 * (5 / 4) :=
      mul_le_mul (FC_opNorm_Ea D N a) hM₂ hM20 zero_le_one
    have h3 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h3]; linarith
  have hX1 : opNorm X ≤ 1 := by linarith
  have hX0 := FC_opNorm_nonneg X
  have hLd : Ld = -α' * ∑ i, ∑ j, (if i.1 = j.1 ∧ i ≠ j then ∫ h, FC_T4 (res (Matrix.of h + Λ) z₁)
      (res (Matrix.of h + Λ) z₂) E X i j ∂μ else 0) := FC_lead2_eq D N L t Λ E z₁ z₂ X
  have hiT : ∀ i j, Integrable (fun h => FC_T4 (res (Matrix.of h + Λ) z₁)
      (res (Matrix.of h + Λ) z₂) E X i j) μ := fun i j =>
    FC_int_cont2 hμ.herm Λ hΛ z hz z₁ z₂ h₁ h₂ (fun p => FC_T4 p.1 p.2 E X i j) (FC_cont_T4 E X i j)
  have hiTM : ∀ i j, Integrable (fun h => FC_T4M (res (Matrix.of h + Λ) z₁)
      (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j) μ := fun i j =>
    FC_int_cont2 hμ.herm Λ hΛ z hz z₁ z₂ h₁ h₂ (fun p => FC_T4M p.1 p.2 M₁ M₂ E X i j)
      (FC_cont_T4M M₁ M₂ E X i j)
  have hiR : ∀ B' : Matrix (Idx D N) (Idx D N) ℂ, Integrable (fun h =>
      ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ * B')) μ := fun B' =>
    FC_int_cont2 hμ.herm Λ hΛ z hz z₁ z₂ h₁ h₂ (fun p => ntr (p.2 * E * p.1 * B')) (by
      unfold ntr
      exact continuous_const.mul ((((continuous_snd.matrix_mul continuous_const).matrix_mul
        continuous_fst).matrix_mul continuous_const).matrix_trace))
  have hMe1 : ∀ x y, ‖M₁ x y‖ ≤ 5 / 4 := fun x y => (norm_apply_le_opNorm M₁ x y).trans hM₁
  have hMe2 : ∀ x y, ‖M₂ x y‖ ≤ 5 / 4 := fun x y => (norm_apply_le_opNorm M₂ x y).trans hM₂
  have hM1X' : opNorm M₁ * opNorm X ≤ 5 / 4 * 1 := mul_le_mul hM₁ hX1 hX0 (by norm_num)
  have hM1X : ∀ x y, ‖(M₁ * X) x y‖ ≤ 5 / 4 := fun x y =>
    (norm_apply_le_opNorm _ x y).trans ((opNorm_mul_le _ _).trans (by linarith))
  have hcr : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      (∀ x y, ‖res (Matrix.of h + Λ) z₁ x y‖ ≤ (z.im)⁻¹) ∧
      (∀ x y, ‖res (Matrix.of h + Λ) z₂ x y‖ ≤ (z.im)⁻¹) ∧
      (∀ x y, ‖(res (Matrix.of h + Λ) z₁ * X) x y‖ ≤ (z.im)⁻¹) ∧
      (∀ x y, ‖(res (Matrix.of h + Λ) z₂ * (E * res (Matrix.of h + Λ) z₁)) x y‖ ≤ (z.im)⁻¹ ^ 2) ∧
      (∀ x y, ‖(res (Matrix.of h + Λ) z₂ * (E * (res (Matrix.of h + Λ) z₁ * X))) x y‖ ≤
        (z.im)⁻¹ ^ 2) := by
    intro h hh
    have g1 := FC_opNorm_res _ (hh.add hΛ) z hz z₁ h₁
    have g2 := FC_opNorm_res _ (hh.add hΛ) z hz z₂ h₂
    have g10 := FC_opNorm_nonneg (res (Matrix.of h + Λ) z₁)
    have g20 := FC_opNorm_nonneg (res (Matrix.of h + Λ) z₂)
    have k1 : opNorm (res (Matrix.of h + Λ) z₁ * X) ≤ (z.im)⁻¹ := by
      refine (opNorm_mul_le _ _).trans ?_
      calc _ ≤ (z.im)⁻¹ * 1 := mul_le_mul g1 hX1 hX0 hηi
        _ = _ := mul_one _
    have k2 : opNorm (E * res (Matrix.of h + Λ) z₁) ≤ (z.im)⁻¹ := by
      refine (opNorm_mul_le _ _).trans ?_
      calc _ ≤ 1 * (z.im)⁻¹ := mul_le_mul hE1 g1 g10 zero_le_one
        _ = _ := one_mul _
    have k3 : opNorm (E * (res (Matrix.of h + Λ) z₁ * X)) ≤ (z.im)⁻¹ := by
      refine (opNorm_mul_le _ _).trans ?_
      calc _ ≤ 1 * (z.im)⁻¹ := mul_le_mul hE1 k1 (FC_opNorm_nonneg _) zero_le_one
        _ = _ := one_mul _
    refine ⟨fun x y => FC_entry_le_inv _ _ g1 x y, fun x y => FC_entry_le_inv _ _ g2 x y,
      fun x y => FC_entry_le_inv _ _ k1 x y, fun x y => FC_entry_le_inv _ _ ?_ x y,
      fun x y => FC_entry_le_inv _ _ ?_ x y⟩
    · refine (opNorm_mul_le _ _).trans ?_
      calc _ ≤ (z.im)⁻¹ * (z.im)⁻¹ := mul_le_mul g2 k2 (FC_opNorm_nonneg _) hηi
        _ = _ := by ring
    · refine (opNorm_mul_le _ _).trans ?_
      calc _ ≤ (z.im)⁻¹ * (z.im)⁻¹ := mul_le_mul g2 k3 (FC_opNorm_nonneg _) hηi
        _ = _ := by ring
  have hG2 := FC_good_two Λ hΛ z hz hz1 z₁ z₂ h₁ h₂ E hE1 M₁ M₂ X hM₁ hM₂ hX1 δ hδ S hiso
  have hgood : ∀ h ∈ S, (Matrix.of h).IsHermitian → ∀ i j,
      ‖FC_T4 (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) E X i j -
        FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j‖ ≤
          324 * δ * (z.im)⁻¹ := by
    intro h hS hh i j
    obtain ⟨i1, i2⟩ := hiso h hS hh
    obtain ⟨b1, b3, -⟩ := FC_iso_bounds _ (hh.add hΛ) z hz z₁ h₁ M₁ X hM₁ hX1 δ hδ i1
    obtain ⟨b2, -⟩ := FC_iso_bounds _ (hh.add hΛ) z hz z₂ h₂ M₂ X hM₂ hX1 δ hδ i2
    have hY : ∀ x y, ‖(res (Matrix.of h + Λ) z₂ * (E * res (Matrix.of h + Λ) z₁)) x y‖ ≤
        3 * (z.im)⁻¹ := by
      intro x y
      have := hG2.sup h hS hh (0, 2, false, false) (show FC_segOK 2 (0, 2, false, false) by decide) x y
      rw [FC_seg2b] at this
      simpa using this
    have hZ : ∀ x y, ‖(res (Matrix.of h + Λ) z₂ * (E * (res (Matrix.of h + Λ) z₁ * X))) x y‖ ≤
        3 * (z.im)⁻¹ := by
      intro x y
      have := hG2.sup h hS hh (0, 2, false, true) (show FC_segOK 2 (0, 2, false, true) by decide) x y
      rw [FC_seg2b] at this
      simpa using this
    have := FC_T4_diff (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) M₁ M₂ E X δ
      (3 * (z.im)⁻¹) (by positivity) i1.1 i2.1 i1.2.1 b1 b2 b3
      (fun x y => (hMe1 x y).trans (by norm_num)) (fun x y => (hMe2 x y).trans (by norm_num))
      (fun x y => (hM1X x y).trans (by norm_num)) hY hZ i j
    linarith
  have hcrude : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → ∀ i j,
      ‖FC_T4 (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) E X i j -
        FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j‖ ≤
          12 * (z.im)⁻¹ ^ 5 ∧
      ‖FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j‖ ≤
          8 * (z.im)⁻¹ ^ 2 := by
    intro h hh i j
    obtain ⟨c1, c2, c3, c4, c5⟩ := hcr h hh
    have t1 := FC_T4_le _ _ E X _ _ c1 c2 c3 c4 c5 i j
    have t2 := FC_T4M_le (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) M₁ M₂ E X _ _
      hMe1 hMe2 hM1X c4 c5 i j
    have hq : ((5 : ℝ) / 4) ^ 3 ≤ 2 := by norm_num
    have hq2 : 0 ≤ (z.im)⁻¹ ^ 2 := by positivity
    have t2' : ‖FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j‖ ≤
        8 * (z.im)⁻¹ ^ 2 := by nlinarith
    refine ⟨?_, t2'⟩
    have e1 : (z.im)⁻¹ ^ 2 ≤ (z.im)⁻¹ ^ 5 := pow_le_pow_right₀ hη1 (by norm_num)
    have e2 : 4 * ((z.im)⁻¹ ^ 3 * (z.im)⁻¹ ^ 2) = 4 * (z.im)⁻¹ ^ 5 := by ring
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ 4 * ((z.im)⁻¹ ^ 3 * (z.im)⁻¹ ^ 2) + 8 * (z.im)⁻¹ ^ 2 := add_le_add t1 t2'
      _ ≤ _ := by linarith
  have hdiff : ∀ i j, ‖∫ h, (FC_T4 (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) E X i j -
      FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j) ∂μ‖ ≤
        324 * δ * (z.im)⁻¹ + 12 * (z.im)⁻¹ ^ 5 * ε := by
    intro i j
    refine FC_int_split _ ((hiT i j).sub (hiTM i j)).aestronglyMeasurable S _ _ ε (by positivity)
      (by positivity) ?_ ?_ hSc hε
    · filter_upwards [hμ.herm] with h hh hS
      exact hgood h hS hh i j
    · filter_upwards [hμ.herm] with h hh
      exact (hcrude h hh i j).1
  have hdiag : ∀ i, ‖∫ h, FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂)
      M₁ M₂ E X i i ∂μ‖ ≤ 8 * (z.im)⁻¹ ^ 2 := by
    intro i
    refine FC_int_le _ (hiTM i i).aestronglyMeasurable _ (by positivity) ?_
    filter_upwards [hμ.herm] with h hh
    exact (hcrude h hh i i).2
  obtain ⟨W1, hW1⟩ : ∃ W1 : ℂ, W1 = ∑ i, ∑ j, (if i.1 = j.1 ∧ i ≠ j then
      ∫ h, (FC_T4 (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) E X i j -
        FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j) ∂μ
      else 0) := ⟨_, rfl⟩
  obtain ⟨Wd, hWd⟩ : ∃ Wd : ℂ, Wd = ∑ i, ∫ h, FC_T4M (res (Matrix.of h + Λ) z₁)
      (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i i ∂μ := ⟨_, rfl⟩
  have hsplit : ∑ i, ∑ j, (if i.1 = j.1 ∧ i ≠ j then ∫ h, FC_T4 (res (Matrix.of h + Λ) z₁)
      (res (Matrix.of h + Λ) z₂) E X i j ∂μ else 0) = W1 + (∑ i, (∑ j, (if i.1 = j.1 then
        ∫ h, FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j ∂μ
        else 0))) - Wd := by
    have per : ∀ i j, (if i.1 = j.1 ∧ i ≠ j then ∫ h, FC_T4 (res (Matrix.of h + Λ) z₁)
        (res (Matrix.of h + Λ) z₂) E X i j ∂μ else 0) =
        (if i.1 = j.1 ∧ i ≠ j then ∫ h, (FC_T4 (res (Matrix.of h + Λ) z₁)
          (res (Matrix.of h + Λ) z₂) E X i j - FC_T4M (res (Matrix.of h + Λ) z₁)
            (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j) ∂μ else 0) +
        (if i.1 = j.1 then ∫ h, FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂)
          M₁ M₂ E X i j ∂μ else 0) -
        (if i = j then ∫ h, FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂)
          M₁ M₂ E X i j ∂μ else 0) := by
      intro i j
      by_cases hij : i = j
      · subst hij; simp
      · by_cases hb : i.1 = j.1
        · simp only [hb, hij, ne_eq, not_false_eq_true, and_self, ↓reduceIte, sub_zero]
          rw [integral_sub (hiT i j) (hiTM i j)]; ring
        · simp [hb, hij]
    simp only [per, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    rw [hW1, hWd]
  obtain ⟨Ssum, hSsum⟩ : ∃ Ssum : ℂ, Ssum = ∑ y : Fin D,
      (ntr (diagonal (diag M₂) * diagonal (diag M₂) * Ea D N y) *
          (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
            (X * diagonal (diag M₂) * Ea D N y)) ∂μ) +
        (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
            (diagonal (diag M₂) * Ea D N y)) ∂μ) * ntr (M₁ * X * diagonal (diag M₂) * Ea D N y) +
        ntr (M₁ * diagonal (diag M₂) * Ea D N y) *
          (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
            (diagonal (diag (M₁ * X)) * Ea D N y)) ∂μ) +
        (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
            (diagonal (diag M₁) * Ea D N y)) ∂μ) * ntr (M₁ * X * diagonal (diag M₁) * Ea D N y)) :=
    ⟨_, rfl⟩
  have hSsame : ∑ i, ∑ j, (if i.1 = j.1 then ∫ h, FC_T4M (res (Matrix.of h + Λ) z₁)
      (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j ∂μ else 0) = ((D : ℂ) * N) ^ 2 * Ssum := by
    have e1 : ∀ i j, (if i.1 = j.1 then ∫ h, FC_T4M (res (Matrix.of h + Λ) z₁)
        (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j ∂μ else 0) = ∫ h, (if i.1 = j.1 then
          FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j
          else 0) ∂μ := by
      intro i j; split_ifs <;> simp
    have hi : ∀ i j, Integrable (fun h => if i.1 = j.1 then FC_T4M (res (Matrix.of h + Λ) z₁)
        (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j else 0) μ := by
      intro i j; split_ifs
      · exact hiTM i j
      · exact integrable_zero _ _ _
    simp only [e1]
    simp only [← integral_finsetSum _ fun j _ => hi _ j]
    rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
    have hpt : ∀ h : Idx D N → Idx D N → ℂ, ∑ i, ∑ j, (if i.1 = j.1 then
        FC_T4M (res (Matrix.of h + Λ) z₁) (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j else 0) =
        ((D : ℂ) * N) ^ 2 * ∑ y : Fin D,
          (ntr (diagonal (diag M₂) * diagonal (diag M₂) * Ea D N y) *
              ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
                (X * diagonal (diag M₂) * Ea D N y)) +
            ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
                (diagonal (diag M₂) * Ea D N y)) * ntr (M₁ * X * diagonal (diag M₂) * Ea D N y) +
            ntr (M₁ * diagonal (diag M₂) * Ea D N y) *
              ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
                (diagonal (diag (M₁ * X)) * Ea D N y)) +
            ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
                (diagonal (diag M₁) * Ea D N y)) * ntr (M₁ * X * diagonal (diag M₁) * Ea D N y)) := by
      intro h
      rw [FC_fact]
      simp only [Matrix.mul_assoc]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [FC_int_lin (μ := μ) (((D : ℂ) * N) ^ 2)
      (fun y => ntr (diagonal (diag M₂) * diagonal (diag M₂) * Ea D N y))
      (fun y => ntr (M₁ * X * diagonal (diag M₂) * Ea D N y))
      (fun y => ntr (M₁ * diagonal (diag M₂) * Ea D N y))
      (fun y => ntr (M₁ * X * diagonal (diag M₁) * Ea D N y))
      (fun y h => ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
        (X * diagonal (diag M₂) * Ea D N y)))
      (fun y h => ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
        (diagonal (diag M₂) * Ea D N y)))
      (fun y h => ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
        (diagonal (diag (M₁ * X)) * Ea D N y)))
      (fun y h => ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
        (diagonal (diag M₁) * Ea D N y)))
      (fun y => hiR _) (fun y => hiR _) (fun y => hiR _) (fun y => hiR _), hSsum]
  obtain ⟨Asum, hAsum⟩ : ∃ Asum : ℂ, Asum = ∑ y : Fin D,
      (ntr (diagonal (diag M₂) * diagonal (diag M₂) * Ea D N y) *
          (∑ w, R b w * ntr (M₂ * Ea D N w * M₁ * (X * diagonal (diag M₂) * Ea D N y))) +
        (∑ w, R b w * ntr (M₂ * Ea D N w * M₁ * (diagonal (diag M₂) * Ea D N y))) *
          ntr (M₁ * X * diagonal (diag M₂) * Ea D N y) +
        ntr (M₁ * diagonal (diag M₂) * Ea D N y) *
          (∑ w, R b w * ntr (M₂ * Ea D N w * M₁ * (diagonal (diag (M₁ * X)) * Ea D N y))) +
        (∑ w, R b w * ntr (M₂ * Ea D N w * M₁ * (diagonal (diag M₁) * Ea D N y))) *
          ntr (M₁ * X * diagonal (diag M₁) * Ea D N y)) := ⟨_, rfl⟩
  have hlead : lead14 Λ (Real.exp (-t)) z₁ z₂ a b = 2 * (D : ℂ) * Asum := by
    rw [hAsum]; exact FC_lead14_eq D N Λ (Real.exp (-t)) z₁ z₂ a b
  have hdec : -(D : ℂ) * ((2 : ℂ) / ((D : ℂ) * N) * (I1 - Sec)) -
      ((D * Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 *
        lead14 Λ (Real.exp (-t)) z₁ z₂ a b =
      -((2 : ℂ) / N * (I1 - Sec - Ld)) +
        (2 : ℂ) / N * α' * (W1 - Wd + ((D : ℂ) * N) ^ 2 * (Ssum - Asum)) := by
    rw [hlead]
    have hLd' : Ld = -α' * (W1 + ((D : ℂ) * N) ^ 2 * Ssum - Wd) := by rw [hLd, hsplit, hSsame]
    rw [hLd', hα'd]
    push_cast
    field_simp
    ring
  rw [hdec]
  have hα' : ‖(2 : ℂ) / N * α'‖ ≤ 2 * Kν / N ^ 3 := by
    rw [norm_mul, hα'd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hn : ‖(2 : ℂ) / N‖ = 2 / N := by
      rw [norm_div, Complex.norm_ofNat, Complex.norm_natCast]
    rw [hn]
    calc 2 / (N : ℝ) * (Real.exp (-(2 * t)) / (N : ℝ) ^ 2 * ‖ccum (L.νo : Measure ℂ) 2 2‖) ≤
        2 / (N : ℝ) * (1 / (N : ℝ) ^ 2 * Kν) := by gcongr
      _ = 2 * Kν / N ^ 3 := by field_simp
  have hcore' : ‖-((2 : ℂ) / N * (I1 - Sec - Ld))‖ ≤ 2 / N * Kc := by
    rw [norm_neg, norm_mul]
    have hn : ‖(2 : ℂ) / N‖ = 2 / N := by
      rw [norm_div, Complex.norm_ofNat, Complex.norm_natCast]
    rw [hn]
    exact mul_le_mul_of_nonneg_left hcore (by positivity)
  have hB1 : 0 ≤ 324 * δ * (z.im)⁻¹ + 12 * (z.im)⁻¹ ^ 5 * ε := by positivity
  have hW1b : ‖W1‖ ≤ D * N ^ 2 * (324 * δ * (z.im)⁻¹ + 12 * (z.im)⁻¹ ^ 5 * ε) := by
    rw [hW1]
    calc _ ≤ ∑ i, ∑ j, ‖(if i.1 = j.1 ∧ i ≠ j then ∫ h, (FC_T4 (res (Matrix.of h + Λ) z₁)
          (res (Matrix.of h + Λ) z₂) E X i j - FC_T4M (res (Matrix.of h + Λ) z₁)
            (res (Matrix.of h + Λ) z₂) M₁ M₂ E X i j) ∂μ else 0)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then (1 : ℝ) else 0) *
          (324 * δ * (z.im)⁻¹ + 12 * (z.im)⁻¹ ^ 5 * ε) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hb : i.1 = j.1
          · by_cases hij : i = j
            · simp only [hij, ne_eq, not_true_eq_false, and_false, ↓reduceIte, norm_zero, true_and]
              simpa using hB1
            · simp only [hb, hij, ne_eq, not_false_eq_true, and_self, ↓reduceIte, one_mul]
              exact hdiff i j
          · simp [hb]
      _ = (∑ i : Idx D N, ∑ j : Idx D N, (if i.1 = j.1 then (1 : ℝ) else 0)) *
          (324 * δ * (z.im)⁻¹ + 12 * (z.im)⁻¹ ^ 5 * ε) := by
          rw [Finset.sum_mul]; simp only [Finset.sum_mul]
      _ = _ := by rw [FC_card_same]; ring
  have hWdb : ‖Wd‖ ≤ D * N * (8 * (z.im)⁻¹ ^ 2) := by
    rw [hWd]
    calc _ ≤ ∑ i : Idx D N, 8 * (z.im)⁻¹ ^ 2 :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hdiag i)
      _ = _ := by simp
  have hBB2 : ∀ B' : Matrix (Idx D N) (Idx D N) ℂ, opNorm B' ≤ 2 →
      ‖(∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ * B') ∂μ) -
        ∑ w, R b w * ntr (M₂ * Ea D N w * M₁ * B')‖ ≤ 2 * eB := by
    intro B' hB'
    have hB'' : opNorm ((1 / 2 : ℂ) • B') ≤ 1 := by
      rw [opNorm_smul]; norm_num; linarith
    have h1 := hBB _ hB''
    have e : (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
        ((1 / 2 : ℂ) • B')) ∂μ) - ∑ w, R b w * ntr (M₂ * Ea D N w * M₁ * ((1 / 2 : ℂ) • B')) =
        (1 / 2 : ℂ) * ((∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ * B') ∂μ) -
          ∑ w, R b w * ntr (M₂ * Ea D N w * M₁ * B')) := by
      simp only [Matrix.mul_smul, FC_ntr_smul]
      rw [integral_const_mul, mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [e, norm_mul] at h1
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this] at h1
    linarith
  have hmn : ∀ (P Q : Matrix (Idx D N) (Idx D N) ℂ) (p q : ℝ), opNorm P ≤ p → opNorm Q ≤ q →
      opNorm (P * Q) ≤ p * q := fun P Q p q hP hQ =>
    (opNorm_mul_le _ _).trans (mul_le_mul hP hQ (FC_opNorm_nonneg _)
      ((FC_opNorm_nonneg _).trans hP))
  have hdM1 : opNorm (diagonal (diag M₁)) ≤ 5 / 4 := (FC_dg_le M₁ 0).2.trans hM₁
  have hdM2 : opNorm (diagonal (diag M₂)) ≤ 5 / 4 := (FC_dg_le M₂ 0).2.trans hM₂
  have hM1Xn : opNorm (M₁ * X) ≤ 5 / 4 * (5 / 8) := hmn _ _ _ _ hM₁ hX58
  have hdMX : opNorm (diagonal (diag (M₁ * X))) ≤ 5 / 4 * (5 / 8) := (FC_dg_le _ 0).2.trans hM1Xn
  have hEy := FC_opNorm_Ea D N
  have hc2 : ∀ (P : Matrix (Idx D N) (Idx D N) ℂ) (p : ℝ), opNorm P ≤ p → p ≤ 2 →
      ∀ y, ‖ntr (P * Ea D N y)‖ ≤ 2 := fun P p hP hp y =>
    (FC_ntr_le _).trans ((hmn _ _ _ _ hP (hEy y)).trans (by linarith))
  have hSA : ‖Ssum - Asum‖ ≤ D * (16 * eB) := by
    rw [hSsum, hAsum, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ y : Fin D, 16 * eB := (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
      _ = _ := by simp
    have k1 := hBB2 (X * diagonal (diag M₂) * Ea D N y)
      (hmn _ _ _ _ (hmn _ _ _ _ hX58 hdM2) (hEy y) |>.trans (by norm_num))
    have k2 := hBB2 (diagonal (diag M₂) * Ea D N y)
      (hmn _ _ _ _ hdM2 (hEy y) |>.trans (by norm_num))
    have k3 := hBB2 (diagonal (diag (M₁ * X)) * Ea D N y)
      (hmn _ _ _ _ hdMX (hEy y) |>.trans (by norm_num))
    have k4 := hBB2 (diagonal (diag M₁) * Ea D N y)
      (hmn _ _ _ _ hdM1 (hEy y) |>.trans (by norm_num))
    have q1 := hc2 _ _ (hmn _ _ _ _ hdM2 hdM2) (by norm_num) y
    have q2 := hc2 _ _ (hmn _ _ _ _ hM1Xn hdM2) (by norm_num) y
    have q3 := hc2 _ _ (hmn _ _ _ _ hM₁ hdM2) (by norm_num) y
    have q4 := hc2 _ _ (hmn _ _ _ _ hM1Xn hdM1) (by norm_num) y

    set u1 := (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
      (X * diagonal (diag M₂) * Ea D N y)) ∂μ) - ∑ w, R b w * ntr (M₂ * Ea D N w * M₁ *
        (X * diagonal (diag M₂) * Ea D N y))
    set u2 := (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
      (diagonal (diag M₂) * Ea D N y)) ∂μ) - ∑ w, R b w * ntr (M₂ * Ea D N w * M₁ *
        (diagonal (diag M₂) * Ea D N y))
    set u3 := (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
      (diagonal (diag (M₁ * X)) * Ea D N y)) ∂μ) - ∑ w, R b w * ntr (M₂ * Ea D N w * M₁ *
        (diagonal (diag (M₁ * X)) * Ea D N y))
    set u4 := (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
      (diagonal (diag M₁) * Ea D N y)) ∂μ) - ∑ w, R b w * ntr (M₂ * Ea D N w * M₁ *
        (diagonal (diag M₁) * Ea D N y))
    have e : ntr (diagonal (diag M₂) * diagonal (diag M₂) * Ea D N y) *
          (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
            (X * diagonal (diag M₂) * Ea D N y)) ∂μ) +
        (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
            (diagonal (diag M₂) * Ea D N y)) ∂μ) * ntr (M₁ * X * diagonal (diag M₂) * Ea D N y) +
        ntr (M₁ * diagonal (diag M₂) * Ea D N y) *
          (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
            (diagonal (diag (M₁ * X)) * Ea D N y)) ∂μ) +
        (∫ h, ntr (res (Matrix.of h + Λ) z₂ * E * res (Matrix.of h + Λ) z₁ *
            (diagonal (diag M₁) * Ea D N y)) ∂μ) * ntr (M₁ * X * diagonal (diag M₁) * Ea D N y) -
        (ntr (diagonal (diag M₂) * diagonal (diag M₂) * Ea D N y) *
          (∑ w, R b w * ntr (M₂ * Ea D N w * M₁ * (X * diagonal (diag M₂) * Ea D N y))) +
        (∑ w, R b w * ntr (M₂ * Ea D N w * M₁ * (diagonal (diag M₂) * Ea D N y))) *
          ntr (M₁ * X * diagonal (diag M₂) * Ea D N y) +
        ntr (M₁ * diagonal (diag M₂) * Ea D N y) *
          (∑ w, R b w * ntr (M₂ * Ea D N w * M₁ * (diagonal (diag (M₁ * X)) * Ea D N y))) +
        (∑ w, R b w * ntr (M₂ * Ea D N w * M₁ * (diagonal (diag M₁) * Ea D N y))) *
          ntr (M₁ * X * diagonal (diag M₁) * Ea D N y)) =
        ntr (diagonal (diag M₂) * diagonal (diag M₂) * Ea D N y) * u1 +
          u2 * ntr (M₁ * X * diagonal (diag M₂) * Ea D N y) +
          ntr (M₁ * diagonal (diag M₂) * Ea D N y) * u3 +
          u4 * ntr (M₁ * X * diagonal (diag M₁) * Ea D N y) := by
      simp only [u1, u2, u3, u4]; ring
    rw [e]
    have t : ∀ (c u : ℂ), ‖c‖ ≤ 2 → ‖u‖ ≤ 2 * eB → ‖c * u‖ ≤ 4 * eB := fun c u hc hu => by
      rw [norm_mul]; nlinarith [norm_nonneg c, norm_nonneg u]
    have t' : ∀ (c u : ℂ), ‖c‖ ≤ 2 → ‖u‖ ≤ 2 * eB → ‖u * c‖ ≤ 4 * eB := fun c u hc hu => by
      rw [mul_comm]; exact t c u hc hu
    have s1 := t _ _ q1 k1
    have s2 := t' _ _ q2 k2
    have s3 := t _ _ q3 k3
    have s4 := t' _ _ q4 k4
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_add₃_le) le_rfl
      _ ≤ _ := by linarith
  have hDN : ‖((D : ℂ) * N) ^ 2‖ = ((D : ℝ) * N) ^ 2 := by
    rw [norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hin : ‖W1 - Wd + ((D : ℂ) * N) ^ 2 * (Ssum - Asum)‖ ≤
      D * N ^ 2 * (324 * δ * (z.im)⁻¹ + 12 * (z.im)⁻¹ ^ 5 * ε) + 8 * D * N * (z.im)⁻¹ ^ 2 +
        16 * D ^ 3 * N ^ 2 * eB := by
    have h3 : ‖((D : ℂ) * N) ^ 2 * (Ssum - Asum)‖ ≤ ((D : ℝ) * N) ^ 2 * (D * (16 * eB)) := by
      rw [norm_mul, hDN]; exact mul_le_mul_of_nonneg_left hSA (by positivity)
    calc _ ≤ ‖W1 - Wd‖ + ‖((D : ℂ) * N) ^ 2 * (Ssum - Asum)‖ := norm_add_le _ _
      _ ≤ ‖W1‖ + ‖Wd‖ + ‖((D : ℂ) * N) ^ 2 * (Ssum - Asum)‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ _ := by nlinarith [hW1b, hWdb, h3]
  calc _ ≤ ‖-((2 : ℂ) / N * (I1 - Sec - Ld))‖ +
        ‖(2 : ℂ) / N * α' * (W1 - Wd + ((D : ℂ) * N) ^ 2 * (Ssum - Asum))‖ := norm_add_le _ _
    _ ≤ 2 / N * Kc + 2 * Kν / N ^ 3 * (D * N ^ 2 * (324 * δ * (z.im)⁻¹ +
          12 * (z.im)⁻¹ ^ 5 * ε) + 8 * D * N * (z.im)⁻¹ ^ 2 + 16 * D ^ 3 * N ^ 2 * eB) := by
        rw [norm_mul]
        exact add_le_add hcore' (mul_le_mul hα' hin (norm_nonneg _) (by positivity))

end

section

private theorem FC_err12 (D N : ℕ) (l k kk : ℕ) (η ε : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 ≤ ε) :
    FC_err D N 2 l k kk η η⁻¹ ε ≤ η⁻¹ * FC_err D N 1 l k kk η 1 ε := by
  have hi : 1 ≤ η⁻¹ := one_le_inv₀ hη |>.2 hη1
  unfold FC_err
  simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.sub_self, pow_zero, mul_one]
  have a5 : 0 ≤ ((D : ℝ) * N) ^ 2 * η⁻¹ ^ (l + 2) * ε := by positivity
  have a6 : 0 ≤ ((D : ℝ) * N) ^ 3 * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * η⁻¹) ^ (2 + l + 1) +
      (1 + η⁻¹) ^ (2 + l + 1) * Real.sqrt (0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (η / 24)) ^ (-(k : ℝ)))) := by
    positivity
  have b5 := le_mul_of_one_le_left a5 hi
  have b6 := le_mul_of_one_le_left a6 hi
  nlinarith [b5, b6]

set_option maxHeartbeats 1000000 in
private theorem FC_E2 (D : ℕ) (hD : 1 ≤ D) (c : ℝ) (hc : 1 ≤ c) (Kc Kν CR τ'' τ' εg : ℝ)
    (hKc : 0 ≤ Kc) (hKν : 0 ≤ Kν) (hCR : 0 ≤ CR) (hτ'' : 0 < τ'') (hτ' : 2 * τ'' < τ')
    (hεg0 : 0 ≤ εg) (hεg : εg ≤ 1 / 2) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ η δ ε r eB : ℝ, 0 < η → η ≤ 1 → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ η → 0 ≤ δ →
      δ ≤ (N : ℝ) ^ τ'' * (Real.sqrt (1 / (N * η)) + 1 / (N * η)) → 0 ≤ ε →
      ε ≤ 3 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(30 : ℝ)) + 2 * D * (N : ℝ) ^ (-(30 : ℝ)) →
      0 ≤ r → r ≤ CR * (N : ℝ) ^ εg → 0 ≤ eB →
      eB ≤ (N : ℝ) ^ τ'' * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ * r) + (η⁻¹ ^ 2 + 2 * D * r) *
        (N : ℝ) ^ (-(30 : ℝ)) →
        2 / N * (Kc * FC_err D N 2 24 160 (Nat.log 2 (D * N) + 1) η η⁻¹ ε) +
          2 * Kν / N ^ 3 * (D * N ^ 2 * (324 * δ * η⁻¹ + 12 * η⁻¹ ^ 5 * ε) +
            8 * D * N * η⁻¹ ^ 2 + 16 * D ^ 3 * N ^ 2 * eB) ≤
        (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (η ^ 2)⁻¹) := by
  obtain ⟨K₁, hK₁0, N₁, hE1⟩ := FC_E1 D hD c hc Kc Kν τ'' hKc hKν hτ''
  obtain ⟨N₂, hN₂⟩ := FC_ev_pow (show (1 / 3 : ℝ) < 1 / 2 by norm_num) c
  obtain ⟨N₃, hN₃⟩ := FC_ev_pow (show (5 / 3 + 2 - 31 : ℝ) < -2 by norm_num) (5 * D ^ 2 * c ^ 5)
  set K₂ := 2 * D * K₁ + 1296 * Kν * D + 24 * Kν * D + 16 * Kν * D +
    32 * Kν * D ^ 3 * (CR + 1 + 2 * D * CR) with hK₂
  obtain ⟨N₄, hN₄⟩ := FC_ev_ge (show 0 < τ' - 2 * τ'' by linarith) K₂
  refine ⟨max (max N₁ N₂) (max (max N₃ N₄) 1), fun N hN η δ ε r eB hη hη1 hηl hδ0 hδ hε0 hε hr0
    hr heB0 heB => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx0 : (0 : ℝ) < N := by linarith
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hc0 : 0 < c := by linarith
  have hηi1 : 1 ≤ η⁻¹ := one_le_inv₀ hη |>.2 hη1
  have hηi0 : 0 ≤ η⁻¹ := by linarith
  have hηi : η⁻¹ ≤ c * (N : ℝ) ^ (1 / 3 : ℝ) := by
    have h1 : 0 < c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
    have := inv_anti₀ h1 hηl
    rw [mul_inv, inv_inv, Real.rpow_neg hx0.le, inv_inv] at this
    exact this
  have hη2 : (η ^ 2)⁻¹ = η⁻¹ ^ 2 := by rw [inv_pow]
  rw [hη2]
  obtain ⟨hS1, hS2, hS3, hS4⟩ := FC_s_facts N hN1 η hη hη1
  set s₂ := (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ ^ 2 with hs₂
  have hp32 : 0 ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hp2 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hs₂0 : 0 ≤ s₂ := by positivity
  have hsq1 : (1 : ℝ) ≤ η⁻¹ ^ 2 := one_le_pow₀ hηi1
  have h232 : (N : ℝ) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hN2s : (N : ℝ) ^ (-(2 : ℝ)) ≤ s₂ := by
    have : (N : ℝ) ^ (-(3 / 2 : ℝ)) * 1 ≤ s₂ := mul_le_mul_of_nonneg_left hsq1 hp32
    linarith
  have hN2s' : (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2 ≤ s₂ := mul_le_mul_of_nonneg_right h232 (by positivity)
  set Q := (N : ℝ) ^ τ'' with hQ
  set P := (N : ℝ) ^ (2 * τ'') with hP
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hx hτ''.le
  have hQP : Q ≤ P := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hP1 : 1 ≤ P := hQ1.trans hQP
  have hηh : η⁻¹ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := hηi.trans (hN₂ N (by omega))
  have hηh' : (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
    calc (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ≤ (N : ℝ) ^ (-(2 : ℝ)) * (N : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hηh hp2
      _ = _ := by rw [← Real.rpow_add hx0]; norm_num
  have hE := hE1 N (by omega) η 0 ((N : ℝ) ^ τ'' * (1 / (N * η))) ε hη hη1 hηl le_rfl
    (by positivity) rfl hε0 hε
  have hFC1 : 2 / ((D : ℝ) * N) * (Kc * FC_err D N 1 24 160 (Nat.log 2 (D * N) + 1) η 1 ε) ≤
      K₁ * P * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2) := by
    have a2 : 0 ≤ 2 * Kν * ((108 * 0 + 4 * η⁻¹ ^ 4 * ε) / N + 3 / N ^ 2) := by positivity
    have a3 : 0 ≤ 2 * (D : ℝ) ^ 2 * ((N : ℝ) ^ τ'' * (1 / (N * η))) ^ 2 +
        18 * D ^ 2 * η⁻¹ ^ 2 * ε := by positivity
    linarith
  have hF12 := FC_err12 D N 24 160 (Nat.log 2 (D * N) + 1) η ε hη hη1 hε0
  have hFC0 := FC_err_nonneg D N 1 24 160 (Nat.log 2 (D * N) + 1) η 1 ε hη zero_le_one hε0
  have P1 : 2 / N * (Kc * FC_err D N 2 24 160 (Nat.log 2 (D * N) + 1) η η⁻¹ ε) ≤
      2 * D * K₁ * P * s₂ := by
    have hDN : (0 : ℝ) < D * N := by positivity
    calc 2 / N * (Kc * FC_err D N 2 24 160 (Nat.log 2 (D * N) + 1) η η⁻¹ ε) ≤
          2 / N * (Kc * (η⁻¹ * FC_err D N 1 24 160 (Nat.log 2 (D * N) + 1) η 1 ε)) := by
          gcongr
      _ = D * η⁻¹ * (2 / ((D : ℝ) * N) * (Kc * FC_err D N 1 24 160 (Nat.log 2 (D * N) + 1)
            η 1 ε)) := by field_simp
      _ ≤ D * η⁻¹ * (K₁ * P * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ +
            (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2)) := mul_le_mul_of_nonneg_left hFC1 (by positivity)
      _ = D * K₁ * P * (s₂ + (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ * η⁻¹ ^ 2) := by rw [hs₂]; ring
      _ ≤ D * K₁ * P * (s₂ + s₂) := by
          gcongr
          rw [hs₂]
          exact mul_le_mul_of_nonneg_right hηh' (by positivity)
      _ = 2 * D * K₁ * P * s₂ := by ring
  have hsq : Real.sqrt (1 / (N * η)) / N ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ := by
    have e1 : Real.sqrt (1 / (N * η)) = Real.sqrt ((N : ℝ)⁻¹) * Real.sqrt η⁻¹ := by
      rw [one_div, mul_inv, Real.sqrt_mul (inv_nonneg.2 hx0.le)]
    have e2 : Real.sqrt ((N : ℝ)⁻¹) / N = (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hx0.le, div_eq_mul_inv,
        ← Real.rpow_neg_one (N : ℝ), ← Real.rpow_add hx0]
      norm_num
    have e3 : Real.sqrt η⁻¹ ≤ η⁻¹ := by
      calc Real.sqrt η⁻¹ ≤ Real.sqrt (η⁻¹ ^ 2) :=
            Real.sqrt_le_sqrt (le_self_pow₀ hηi1 (by norm_num))
        _ = η⁻¹ := Real.sqrt_sq (by positivity)
    calc Real.sqrt (1 / (N * η)) / N = Real.sqrt ((N : ℝ)⁻¹) / N * Real.sqrt η⁻¹ := by
          rw [e1]; ring
      _ ≤ _ := by
          rw [e2]
          exact mul_le_mul_of_nonneg_left e3 hp32
  have hlin : 1 / (N * η) / N = (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.rpow_two]
    field_simp
  have hδN : δ * η⁻¹ / N ≤ 2 * (P * s₂) := by
    calc δ * η⁻¹ / N ≤ Q * (Real.sqrt (1 / (N * η)) + 1 / (N * η)) * η⁻¹ / N := by
          gcongr
      _ = Q * ((Real.sqrt (1 / (N * η)) / N) * η⁻¹ + (1 / (N * η) / N) * η⁻¹) := by ring
      _ ≤ Q * (s₂ + s₂) := by
          gcongr
          · calc Real.sqrt (1 / (N * η)) / N * η⁻¹ ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * η⁻¹ * η⁻¹ :=
                  mul_le_mul_of_nonneg_right hsq hηi0
              _ = s₂ := by rw [hs₂]; ring
          · rw [hlin]
            calc (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ * η⁻¹ = (N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2 := by ring
              _ ≤ s₂ := hN2s'
      _ ≤ 2 * (P * s₂) := by nlinarith
  have hε' : ε ≤ 5 * D ^ 2 * (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-(30 : ℝ)) := by
    have hp30 : 0 ≤ (N : ℝ) ^ (-(30 : ℝ)) := Real.rpow_nonneg hx0.le _
    have hx2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) ^ 2 := by rw [← Real.rpow_natCast]; norm_num
    rw [hx2]
    have hD2 : (D : ℝ) ≤ D ^ 2 := by
      have := mul_le_mul_of_nonneg_left hD1 (show (0 : ℝ) ≤ D by positivity)
      rw [sq]; linarith only [this]
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hx
    have h1 : 2 * (D : ℝ) ≤ 2 * D ^ 2 * N ^ 2 := by
      have := mul_le_mul hD2 hN2 zero_le_one (by positivity)
      linarith only [this]
    have h3 := mul_le_mul_of_nonneg_right h1 hp30
    calc ε ≤ 3 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(30 : ℝ)) + 2 * D * (N : ℝ) ^ (-(30 : ℝ)) := hε
      _ ≤ 3 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(30 : ℝ)) +
          2 * D ^ 2 * N ^ 2 * (N : ℝ) ^ (-(30 : ℝ)) := by linarith only [h3]
      _ = _ := by ring
  have hη5 : η⁻¹ ^ 5 ≤ c ^ 5 * (N : ℝ) ^ ((5 : ℝ) / 3) := by
    calc η⁻¹ ^ 5 ≤ (c * (N : ℝ) ^ (1 / 3 : ℝ)) ^ 5 := pow_le_pow_left₀ hηi0 hηi 5
      _ = _ := by
          rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 3 : ℝ)), ← Real.rpow_mul hx0.le]
          norm_num
  have hε5 : η⁻¹ ^ 5 * ε / N ≤ s₂ := by
    have h := hN₃ N (by omega)
    have h1 : η⁻¹ ^ 5 * ε / N ≤ (c ^ 5 * (N : ℝ) ^ ((5 : ℝ) / 3)) *
        (5 * D ^ 2 * (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-(30 : ℝ))) / N := by
      gcongr
    have e : (c ^ 5 * (N : ℝ) ^ ((5 : ℝ) / 3)) *
        (5 * D ^ 2 * (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-(30 : ℝ))) / N =
        5 * D ^ 2 * c ^ 5 * (N : ℝ) ^ (5 / 3 + 2 - 31 : ℝ) := by
      rw [show (5 / 3 + 2 - 31 : ℝ) = (5 : ℝ) / 3 + (2 + (-(30 : ℝ) + (-1))) by norm_num,
        Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_neg_one]
      field_simp
    linarith
  have hr' : (N : ℝ) ^ (-(2 : ℝ)) * r ≤ CR * (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
    calc (N : ℝ) ^ (-(2 : ℝ)) * r ≤ (N : ℝ) ^ (-(2 : ℝ)) * (CR * (N : ℝ) ^ εg) :=
          mul_le_mul_of_nonneg_left hr hp2
      _ = CR * (N : ℝ) ^ (εg - 2) := by
          rw [show εg - 2 = -(2 : ℝ) + εg by ring, Real.rpow_add hx0]; ring
      _ ≤ CR * (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
          gcongr
          linarith
  have hr31 : r * (N : ℝ) ^ (-(31 : ℝ)) ≤ CR * s₂ := by
    calc r * (N : ℝ) ^ (-(31 : ℝ)) ≤ (CR * (N : ℝ) ^ εg) * (N : ℝ) ^ (-(31 : ℝ)) :=
          mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hx0.le _)
      _ = CR * (N : ℝ) ^ (εg - 31) := by
          rw [show εg - 31 = εg + (-(31 : ℝ)) by ring, Real.rpow_add hx0]; ring
      _ ≤ CR * (N : ℝ) ^ (-(3 / 2 : ℝ)) := by
          gcongr
          linarith
      _ ≤ CR * s₂ := by
          gcongr
          rw [hs₂]
          exact le_mul_of_one_le_right hp32 hsq1
  have h31 : (N : ℝ) ^ (-(31 : ℝ)) ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have heBN : eB / N ≤ (CR + 1 + 2 * D * CR) * (P * s₂) := by
    have hN31 : (N : ℝ) ^ (-(30 : ℝ)) / N = (N : ℝ) ^ (-(31 : ℝ)) := by
      rw [show (-(31 : ℝ)) = -(30 : ℝ) + (-1) by norm_num, Real.rpow_add hx0, Real.rpow_neg_one]
      ring
    have hNi : (N : ℝ)⁻¹ / N = (N : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hx0.le, Real.rpow_two]; field_simp
    calc eB / N ≤ (Q * ((N : ℝ)⁻¹ * (η ^ 2)⁻¹ * r) + (η⁻¹ ^ 2 + 2 * D * r) *
          (N : ℝ) ^ (-(30 : ℝ))) / N := by gcongr
      _ = Q * (η⁻¹ ^ 2 * ((N : ℝ) ^ (-(2 : ℝ)) * r)) + η⁻¹ ^ 2 * (N : ℝ) ^ (-(31 : ℝ)) +
          2 * D * (r * (N : ℝ) ^ (-(31 : ℝ))) := by
          rw [← hN31, ← hNi, inv_pow]; ring
      _ ≤ Q * (η⁻¹ ^ 2 * (CR * (N : ℝ) ^ (-(3 / 2 : ℝ)))) + η⁻¹ ^ 2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) +
          2 * D * (CR * s₂) := by
          gcongr
      _ = Q * (CR * s₂) + s₂ + 2 * D * (CR * s₂) := by rw [hs₂]; ring
      _ ≤ P * (CR * s₂) + P * s₂ + P * (2 * D * (CR * s₂)) := by
          have a1 : 0 ≤ CR * s₂ := by positivity
          have a2 : 0 ≤ 2 * D * (CR * s₂) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hQP a1, le_mul_of_one_le_left hs₂0 hP1,
            le_mul_of_one_le_left a2 hP1]
      _ = _ := by ring
  have hPs : 0 ≤ P * s₂ := by positivity
  have hsP : s₂ ≤ P * s₂ := le_mul_of_one_le_left hs₂0 hP1
  have hT : 2 * Kν / N ^ 3 * (D * N ^ 2 * (324 * δ * η⁻¹ + 12 * η⁻¹ ^ 5 * ε) +
        8 * D * N * η⁻¹ ^ 2 + 16 * D ^ 3 * N ^ 2 * eB) =
      2 * Kν * D * 324 * (δ * η⁻¹ / N) + 24 * Kν * D * (η⁻¹ ^ 5 * ε / N) +
        16 * Kν * D * ((N : ℝ) ^ (-(2 : ℝ)) * η⁻¹ ^ 2) + 32 * Kν * D ^ 3 * (eB / N) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_two]
    field_simp
    ring
  rw [hT]
  have b2 := mul_le_mul_of_nonneg_left hδN (show 0 ≤ 2 * Kν * D * 324 by positivity)
  have b3 := mul_le_mul_of_nonneg_left (hε5.trans hsP) (show 0 ≤ 24 * Kν * D by positivity)
  have b4 := mul_le_mul_of_nonneg_left (hN2s'.trans hsP) (show 0 ≤ 16 * Kν * D by positivity)
  have b5 := mul_le_mul_of_nonneg_left heBN (show 0 ≤ 32 * Kν * D ^ 3 by positivity)
  have hfin : K₂ * P ≤ (N : ℝ) ^ τ' := by
    calc K₂ * P ≤ (N : ℝ) ^ (τ' - 2 * τ'') * P :=
          mul_le_mul_of_nonneg_right (hN₄ N (by omega)) (by linarith)
      _ = (N : ℝ) ^ τ' := by rw [hP, ← Real.rpow_add hx0]; ring_nf
  have hsum : 2 * D * K₁ * P * s₂ + (2 * Kν * D * 324 * (2 * (P * s₂)) + 24 * Kν * D * (P * s₂) +
      16 * Kν * D * (P * s₂) + 32 * Kν * D ^ 3 * ((CR + 1 + 2 * D * CR) * (P * s₂))) =
      K₂ * P * s₂ := by rw [hK₂]; ring
  calc _ ≤ 2 * D * K₁ * P * s₂ + (2 * Kν * D * 324 * (2 * (P * s₂)) + 24 * Kν * D * (P * s₂) +
      16 * Kν * D * (P * s₂) + 32 * Kν * D ^ 3 * ((CR + 1 + 2 * D * CR) * (P * s₂))) := by
        linarith only [P1, b2, b3, b4, b5]
    _ = K₂ * P * s₂ := hsum
    _ ≤ (N : ℝ) ^ τ' * s₂ := mul_le_mul_of_nonneg_right hfin hs₂0

end

section

private theorem FC_Rnorm (D : ℕ) (hD : 2 ≤ D) (δA τ εg c : ℝ) (hδA : 0 < δA) (hτ : 0 < τ)
    (hεg : 0 < εg) (hεg₂ : εg < δA / 4) (hc : 1 ≤ c) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
          opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ ≤ CR * (N : ℝ) ^ εg := by
  have hc0 : 0 < c⁻¹ := inv_pos.2 (by linarith)
  have hc1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  obtain ⟨C₁, hC₁, N₁, hsame⟩ := one_minus_Mhat_same D hD δA εg c⁻¹ τ hδA hεg hεg₂ hc0 hc1 hτ
  obtain ⟨Cc, hCc, N₂, hconj⟩ := one_minus_Mhat_conj D hD δA τ hδA hτ
  obtain ⟨N₃, hinv⟩ := oneSubMhatP_inv_le D hD δA τ hδA hτ
  refine ⟨2 * (C₁ + Cc * c), by positivity, max (max N₁ N₂) (max N₃ 1),
    fun N hN A hA z hzn hz hq1 hq2 z₁ z₂ h₁ h₂ θ h0 h1 => ?_⟩
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hx0 : (0 : ℝ) < N := by linarith
  have hmS : mExt (lam D N A) z = mSol (lam D N A) z := if_pos hz
  obtain ⟨hdet, hR⟩ := hinv N (by omega) A hA z hzn hz z₁ z₂ h₁ h₂ θ h0 h1
  refine ⟨hdet, ?_⟩
  have hNe : 1 ≤ (N : ℝ) ^ εg := Real.one_le_rpow hx hεg.le
  have hmpos : 0 < (mSol (lam D N A) z).im := by
    have h0 : 0 < c⁻¹ * (N : ℝ) ^ (-εg) := by positivity
    have := lt_of_lt_of_le h0 hq1
    rw [hmS] at this
    by_contra hneg
    push_neg at hneg
    have : z.im / (mSol (lam D N A) z).im ≤ 0 := div_nonpos_of_nonneg_of_nonpos hz.le hneg
    linarith
  have hratio : (mSol (lam D N A) z).im / z.im ≤ c * (N : ℝ) ^ εg := by
    have h := hq1
    rw [hmS] at h
    have hpos : 0 < c⁻¹ * (N : ℝ) ^ (-εg) := by positivity
    have := inv_anti₀ hpos h
    rw [inv_div, mul_inv, inv_inv, Real.rpow_neg hx0.le, inv_inv] at this
    exact this
  have key : opNorm (1 - Mhat (lam D N A) z₁ z₂)⁻¹ ≤ (C₁ + Cc * c) * (N : ℝ) ^ εg := by
    have hC1' : C₁ * (N : ℝ) ^ εg ≤ (C₁ + Cc * c) * (N : ℝ) ^ εg := by
      have : 0 ≤ Cc * c * (N : ℝ) ^ εg := by positivity
      nlinarith
    have hCc' : Cc * ((mSol (lam D N A) z).im / z.im) ≤ (C₁ + Cc * c) * (N : ℝ) ^ εg := by
      have := mul_le_mul_of_nonneg_left hratio hCc.le
      have : 0 ≤ C₁ * (N : ℝ) ^ εg := by positivity
      nlinarith
    obtain ⟨c1, c2, c3⟩ := hconj N (by omega) A hA z hzn hz
    have hs : ∀ w : ℂ, (w = z ∨ w = star z) →
        opNorm (1 - Mhat (lam D N A) w w)⁻¹ ≤ (C₁ + Cc * c) * (N : ℝ) ^ εg := by
      intro w hw
      obtain ⟨-, -, hb, -⟩ := hsame N (by omega) A hA z hzn hz (by rw [← hmS]; exact hq1)
        (by rw [← hmS, inv_inv]; exact hq2) w hw
      exact hb.trans ((mul_le_mul_of_nonneg_left (min_le_right _ _) hC₁.le).trans hC1')
    rcases h₁ with e1 | e1 <;> rcases h₂ with e2 | e2
    · rw [e1, e2]; exact hs z (Or.inl rfl)
    · rw [e1, e2, c1]; exact c3.trans hCc'
    · rw [e1, e2, c2]; exact c3.trans hCc'
    · rw [e1, e2]; exact hs (star z) (Or.inr rfl)
  calc _ ≤ 2 * opNorm (1 - Mhat (lam D N A) z₁ z₂)⁻¹ := hR
    _ ≤ 2 * ((C₁ + Cc * c) * (N : ℝ) ^ εg) := by gcongr
    _ = _ := by ring

end

section

set_option maxHeartbeats 4000000 in
private theorem FC_P14 (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t → t ≤ 1 →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ) + τe) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ a b : Fin D,
        (1 - Mhat (lam D N A) z₁ z₂ * PTheta D (Real.exp (-t))).det ≠ 0 ∧
        (1 - Mhat (lam D N A) z₂ z₁ * PTheta D (Real.exp (-t))).det ≠ 0 ∧
        ‖-(D : ℂ) * (∫ h, underTwoB (lam D N A) (Real.exp (-t)) h z₁ z₂ a (Ea D N b)
              ∂(ouMatLaw D N L t)) -
            ((D * Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 *
              lead14 (lam D N A) (Real.exp (-t)) z₁ z₂ a b‖ ≤
          (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im ^ 2)⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) *
            (z.im ^ 2)⁻¹ * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D (Real.exp (-t)))⁻¹) := by
  intro τ' hτ'
  have hD1 : 1 ≤ D := by omega
  obtain ⟨τ'', hτ''0, hτ''1, hτ''2⟩ : ∃ τ'' : ℝ, 0 < τ'' ∧ τ'' < 1 / 3 ∧ 2 * τ'' < τ' :=
    ⟨min (τ' / 4) (1 / 12), by positivity, by
      have := min_le_right (τ' / 4) (1 / 12); linarith, by
      have := min_le_left (τ' / 4) (1 / 12); linarith⟩
  obtain ⟨C', hC'⟩ := llClass_ouLaw D C
  obtain ⟨Kc, hKc0, hcore⟩ := FC_core D C 24 160 (by norm_num)
  obtain ⟨Kν, hKν⟩ := ccum_entry_le C 2 2
  have hKν0 : ∀ L : EntryLaws C, ‖ccum (L.νo : Measure ℂ) 2 2‖ ≤ |Kν| :=
    fun L => (hKν L).1.trans (le_abs_self _)
  obtain ⟨Cm, hCm0, hMf⟩ := FC_Mfacts τ hτ
  have hc0 : 0 < c⁻¹ := inv_pos.2 (by linarith)
  obtain ⟨CR, hCR0, N₁, hRn⟩ := FC_Rnorm D hD δA τ εg c hδA hτ hεg hεg₂ hc
  obtain ⟨N₂, hinv⟩ := oneSubMhatP_inv_le D hD δA τ hδA hτ
  obtain ⟨N₃, hgood⟩ := FC_good15 D hD1 δA τ hδA hτ C' τ'' hτ''0
  obtain ⟨N₄, hE2⟩ := FC_E2 D hD1 c hc Kc |Kν| CR τ'' τ' εg hKc0 (abs_nonneg _) hCR0 hτ''0 hτ''2
    hεg.le (by linarith)
  obtain ⟨N₅, hN₅⟩ := FC_ev_ge hδA 20
  obtain ⟨N₆, hN₆⟩ := FC_ev_ge hεg c
  obtain ⟨N₇, hN₇⟩ := FC_ev_pow (show τ'' - 1 / 3 < 0 by linarith) (2 * c)
  obtain ⟨N₈, hBBp⟩ := lemma_G_large_BB D hD δA τ εg c hδA hτ hεg hεg₂ hc C' τ'' hτ''0 30
    (by norm_num)
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max N₇ (max N₈ 2))),
    fun N hN L t ht0 ht1 A hA z hz hzim hη hq1 hq2 z₁ z₂ h₁ h₂ a b => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx0 : (0 : ℝ) < N := by linarith
  have gN₁ : N₁ ≤ N := by omega
  have gN₂ : N₂ ≤ N := by omega
  have gN₃ : N₃ ≤ N := by omega
  have gN₄ : N₄ ≤ N := by omega
  have gN₅ : N₅ ≤ N := by omega
  have gN₆ : N₆ ≤ N := by omega
  have gN₇ : N₇ ≤ N := by omega
  have gN₈ : N₈ ≤ N := by omega
  obtain ⟨hzn, hzl'⟩ := hz
  have hlam : opNorm (lam D N A) ≤ 1 / 10 := by
    have h20 := hN₅ N gN₅
    have : (N : ℝ) ^ (-δA) ≤ 1 / 20 := by
      rw [Real.rpow_neg hx0.le, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h20
    linarith [opNorm_lam_le D N A]
  obtain ⟨-, hmz, -⟩ := hMf D N hD1 hN1 A hlam z hzn hzim z (Or.inl rfl)
  obtain ⟨hM1, hm1, -⟩ := hMf D N hD1 hN1 A hlam z hzn hzim z₁ h₁
  obtain ⟨hM2, hm2, -⟩ := hMf D N hD1 hN1 A hlam z hzn hzim z₂ h₂
  set m := mExt (lam D N A) z with hm
  have hmpos : 0 < m.im := by
    have h0 : 0 < c⁻¹ * (N : ℝ) ^ (-εg) := by positivity
    have := lt_of_lt_of_le h0 hq1
    by_contra hneg
    push_neg at hneg
    have : z.im / m.im ≤ 0 := div_nonpos_of_nonneg_of_nonpos hzim.le hneg
    linarith
  have hη1 : z.im ≤ 1 := by
    have hq := hq2
    rw [div_le_iff₀ hmpos] at hq
    have hc6 := hN₆ N gN₆
    have : c * (N : ℝ) ^ (-εg) ≤ 1 := by
      rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv]
      exact (div_le_one (by positivity)).2 hc6
    have hmle : m.im ≤ 1 := (Complex.im_le_norm m).trans hmz
    have hp : 0 ≤ c * (N : ℝ) ^ (-εg) := by positivity
    nlinarith
  set θ := Real.exp (-t) with hθ
  have hθ0 : 0 ≤ θ := (Real.exp_pos _).le
  have hθ1 : θ ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  obtain ⟨hdet12, -⟩ := hinv N gN₂ A hA z hzn hzim z₁ z₂ h₁ h₂ θ hθ0 hθ1
  obtain ⟨hdet21, -⟩ := hinv N gN₂ A hA z hzn hzim z₂ z₁ h₂ h₁ θ hθ0 hθ1
  refine ⟨hdet12, hdet21, ?_⟩
  have hηl : c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ z.im := by
    have : (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 3 : ℝ) + τe) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    exact (mul_le_mul_of_nonneg_left this hc0.le).trans hη
  have habs : ∀ w : ℂ, (w = z ∨ w = star z) → |w.im| = z.im := by
    intro w hw
    rcases hw with e | e
    · rw [e]; exact abs_of_pos hzim
    · rw [e]; simp only [Complex.star_def, Complex.conj_im, abs_neg]; exact abs_of_pos hzim
  have hdom : ∀ w : ℂ, (w = z ∨ w = star z) → w ∈ specDom τ N := by
    intro w hw
    refine ⟨?_, ?_⟩
    · rcases hw with e | e
      · rw [e]; exact hzn
      · rw [e, Complex.star_def, Complex.norm_conj]; exact hzn
    · rw [habs w hw]; rw [abs_of_pos hzim] at hzl'; exact hzl'
  set M₂ := MExt (lam D N A) z₂ with hM₂d
  set X : Matrix (Idx D N) (Idx D N) ℂ := (1 / 2 : ℂ) • (Ea D N a * M₂) with hXd
  have hX1 : opNorm X ≤ 1 := by
    rw [hXd, opNorm_smul]
    have h1 := opNorm_mul_le (Ea D N a) M₂
    have h2 : opNorm (Ea D N a) * opNorm M₂ ≤ 1 * (5 / 4) :=
      mul_le_mul (FC_opNorm_Ea D N a) hM2 (FC_opNorm_nonneg _) zero_le_one
    have h3 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h3]; linarith
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = 3 * ((D : ℝ) * N) ^ 2 * (N : ℝ) ^ (-(30 : ℝ)) +
      2 * D * (N : ℝ) ^ (-(30 : ℝ)) := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hεd]; positivity
  have hμ := hC' N L t ht0
  obtain ⟨S, hSc, hSg⟩ := hgood N gN₃ θ hθ0 hθ1 _ hμ A hA X hX1
  rw [← hεd] at hSc
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = (N : ℝ) ^ τ'' * (Real.sqrt (1 / (N * z.im)) + 1 / (N * z.im)) :=
    ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδd]; positivity
  have hpsi : ∀ w : ℂ, (w = z ∨ w = star z) → (N : ℝ) ^ τ'' * psiIso (lam D N A) N w ≤ δ := by
    intro w hw
    obtain ⟨-, hmw, -⟩ := hMf D N hD1 hN1 A hlam z hzn hzim w hw
    rw [hδd, psiIso, habs w hw]
    gcongr
    exact (Complex.abs_im_le_norm _).trans hmw
  have hδ1 : δ ≤ 1 := by
    have h7 := hN₇ N gN₇
    rw [Real.rpow_zero] at h7
    rw [hδd]
    calc (N : ℝ) ^ τ'' * (Real.sqrt (1 / (N * z.im)) + 1 / (N * z.im)) ≤
          (N : ℝ) ^ τ'' * (2 * c * (N : ℝ) ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left (FC_delta_le N hN1 c hc z.im hzim hηl)
            (Real.rpow_nonneg hx0.le _)
      _ = 2 * c * (N : ℝ) ^ (τ'' - 1 / 3) := by
          rw [show τ'' - 1 / 3 = τ'' + (-(1 / 3 : ℝ)) by ring, Real.rpow_add hx0]; ring
      _ ≤ 1 := h7
  have hiso_mono : ∀ (G M : Matrix (Idx D N) (Idx D N) ℂ) (r₁ r₂ : ℝ), r₁ ≤ r₂ →
      FC_iso G M X r₁ → FC_iso G M X r₂ := by
    intro G M r₁ r₂ hr ⟨i1, i2, i3⟩
    exact ⟨fun x y => (i1 x y).trans hr, fun x y => (i2 x y).trans hr, fun y => (i3 y).trans hr⟩
  have hiso : ∀ h ∈ S, (Matrix.of h).IsHermitian →
      FC_iso (res (Matrix.of h + lam D N A) z₁) (MExt (lam D N A) z₁) X δ ∧
      FC_iso (res (Matrix.of h + lam D N A) z₂) (MExt (lam D N A) z₂) X δ := fun h hh _ =>
    ⟨hiso_mono _ _ _ _ (hpsi z₁ h₁) ((hSg h hh).1 z₁ (hdom z₁ h₁)),
      hiso_mono _ _ _ _ (hpsi z₂ h₂) ((hSg h hh).1 z₂ (hdom z₂ h₂))⟩
  set kk := Nat.log 2 (D * N) + 1 with hkk
  have hkk' : D * N ≤ 2 ^ kk := (Nat.lt_pow_succ_log_self (by norm_num) _).le
  have hchOK : FC_chOK (lam D N A) z [(1, lam D N A, z₂), (Ea D N b, lam D N A, z₁)] := by
    intro g hg
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
    rcases hg with hg | hg <;> subst hg
    · exact ⟨rfl, h₂, FC_opNorm_one⟩
    · exact ⟨rfl, h₁, FC_opNorm_Ea D N b⟩
  have hG := FC_good_two (lam D N A) (lam_isHermitian D N A) z hzim hη1 z₁ z₂ h₁ h₂ (Ea D N b)
    (FC_opNorm_Ea D N b) (MExt (lam D N A) z₁) M₂ X hM1 hM2 hX1 δ hδ1 S hiso
  have hηi1 : 1 ≤ (z.im)⁻¹ := one_le_inv₀ hzim |>.2 hη1
  have hc' := hcore N hN1 L t ht0 (lam D N A) (lam_isHermitian D N A) z hzim hη1
    [(1, lam D N A, z₂), (Ea D N b, lam D N A, z₁)] hchOK (Or.inr rfl) X hX1 S ε hε0 hSc
    (z.im)⁻¹ hηi1 hG kk hkk'
  set r := opNorm (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ with hr
  have hr0 : 0 ≤ r := FC_opNorm_nonneg _
  have hrb : r ≤ CR * (N : ℝ) ^ εg := (hRn N gN₁ A hA z hzn hzim hq1 hq2 z₂ z₁ h₂ h₁ θ hθ0 hθ1).2
  obtain ⟨eB, heBd⟩ : ∃ eB : ℝ, eB = (N : ℝ) ^ τ'' * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ * r) +
      ((z.im)⁻¹ ^ 2 + 2 * D * r) * (N : ℝ) ^ (-(30 : ℝ)) := ⟨_, rfl⟩
  have heB0 : 0 ≤ eB := by rw [heBd]; positivity
  have hBB : ∀ B' : Matrix (Idx D N) (Idx D N) ℂ, opNorm B' ≤ 1 →
      ‖(∫ h, ntr (res (Matrix.of h + lam D N A) z₂ * Ea D N b *
          res (Matrix.of h + lam D N A) z₁ * B') ∂(ouMatLaw D N L t)) -
        ∑ w, (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ b w *
          ntr (MExt (lam D N A) z₂ * Ea D N w * MExt (lam D N A) z₁ * B')‖ ≤ eB := by
    intro B' hB'
    obtain ⟨-, hp⟩ := hBBp N gN₈ θ hθ0 hθ1 _ hμ A hA z ⟨hzn, hzl'⟩ hzim hηl hq1 hq2 z₂ z₁ h₂ h₁
      B' hB' b
    have hprob := hμ.prob
    have hΛ := lam_isHermitian D N A
    have hF : Integrable (fun h => ntr (res (Matrix.of h + lam D N A) z₂ * Ea D N b *
        res (Matrix.of h + lam D N A) z₁ * B')) (ouMatLaw D N L t) :=
      FC_int_cont2 hμ.herm _ hΛ z hzim z₁ z₂ h₁ h₂ (fun p => ntr (p.2 * Ea D N b * p.1 * B')) (by
        unfold ntr
        exact continuous_const.mul ((((continuous_snd.matrix_mul continuous_const).matrix_mul
          continuous_fst).matrix_mul continuous_const).matrix_trace))
    have hcn : ‖∑ w, (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ b w *
        ntr (MExt (lam D N A) z₂ * Ea D N w * MExt (lam D N A) z₁ * B')‖ ≤ 2 * D * r := by
      calc _ ≤ ∑ w : Fin D, r * 2 := (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => by
            rw [norm_mul]
            refine mul_le_mul (norm_apply_le_opNorm _ b w) ?_ (norm_nonneg _) hr0
            refine (FC_ntr_le _).trans ?_
            have e1 := opNorm_mul_le (MExt (lam D N A) z₂ * Ea D N w * MExt (lam D N A) z₁) B'
            have e2 := opNorm_mul_le (MExt (lam D N A) z₂ * Ea D N w) (MExt (lam D N A) z₁)
            have e3 := opNorm_mul_le (MExt (lam D N A) z₂) (Ea D N w)
            have f1 : opNorm (MExt (lam D N A) z₂) * opNorm (Ea D N w) ≤ 5 / 4 * 1 :=
              mul_le_mul hM2 (FC_opNorm_Ea D N w) (FC_opNorm_nonneg _) (by norm_num)
            have f2 : opNorm (MExt (lam D N A) z₂ * Ea D N w) * opNorm (MExt (lam D N A) z₁) ≤
                5 / 4 * (5 / 4) := mul_le_mul (by linarith) hM1 (FC_opNorm_nonneg _) (by norm_num)
            have f3 : opNorm (MExt (lam D N A) z₂ * Ea D N w * MExt (lam D N A) z₁) * opNorm B' ≤
                5 / 4 * (5 / 4) * 1 := mul_le_mul (by linarith) hB' (FC_opNorm_nonneg _)
                  (by norm_num)
            linarith)
        _ = 2 * D * r := by simp; ring
    have hK : ∀ᵐ h ∂(ouMatLaw D N L t), ‖ntr (res (Matrix.of h + lam D N A) z₂ * Ea D N b *
        res (Matrix.of h + lam D N A) z₁ * B')‖ ≤ (z.im)⁻¹ ^ 2 := by
      filter_upwards [hμ.herm] with h hh
      have g1 := FC_opNorm_res _ (hh.add hΛ) z hzim z₁ h₁
      have g2 := FC_opNorm_res _ (hh.add hΛ) z hzim z₂ h₂
      refine (FC_ntr_le _).trans ?_
      have e1 := opNorm_mul_le (res (Matrix.of h + lam D N A) z₂ * Ea D N b *
        res (Matrix.of h + lam D N A) z₁) B'
      have e2 := opNorm_mul_le (res (Matrix.of h + lam D N A) z₂ * Ea D N b)
        (res (Matrix.of h + lam D N A) z₁)
      have e3 := opNorm_mul_le (res (Matrix.of h + lam D N A) z₂) (Ea D N b)
      have hηi0 : 0 ≤ (z.im)⁻¹ := by linarith
      have f1 : opNorm (res (Matrix.of h + lam D N A) z₂) * opNorm (Ea D N b) ≤ (z.im)⁻¹ * 1 :=
        mul_le_mul g2 (FC_opNorm_Ea D N b) (FC_opNorm_nonneg _) hηi0
      have f2 : opNorm (res (Matrix.of h + lam D N A) z₂ * Ea D N b) *
          opNorm (res (Matrix.of h + lam D N A) z₁) ≤ (z.im)⁻¹ * (z.im)⁻¹ :=
        mul_le_mul (by linarith) g1 (FC_opNorm_nonneg _) hηi0
      have f3 : opNorm (res (Matrix.of h + lam D N A) z₂ * Ea D N b *
          res (Matrix.of h + lam D N A) z₁) * opNorm B' ≤ (z.im)⁻¹ * (z.im)⁻¹ * 1 :=
        mul_le_mul (by linarith) hB' (FC_opNorm_nonneg _) (by positivity)
      nlinarith
    have := FC_exp_close _ hF _ ((N : ℝ) ^ τ'' * ((N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ * r))
      ((z.im)⁻¹ ^ 2) ((N : ℝ) ^ (-(30 : ℝ))) (by positivity) (by positivity) (by positivity) hK
      (by simpa only [not_le] using hp)
    rw [heBd]
    refine this.trans ?_
    have : ((z.im)⁻¹ ^ 2 + ‖∑ w, (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ)⁻¹ b w *
        ntr (MExt (lam D N A) z₂ * Ea D N w * MExt (lam D N A) z₁ * B')‖) *
          (N : ℝ) ^ (-(30 : ℝ)) ≤ ((z.im)⁻¹ ^ 2 + 2 * D * r) * (N : ℝ) ^ (-(30 : ℝ)) := by
      gcongr
    linarith
  have hstep := FC_P14_step D N hD hN1 L t ht0 hμ A z hzim hη1 z₁ z₂ h₁ h₂ a b hM1 hM2 _ hc' S ε
    hε0 hSc δ hδ0 hδ1 hiso eB heB0 hBB |Kν| (hKν0 L)
  have hfin := hE2 N gN₄ z.im δ ε r eB hzim hη1 hηl hδ0 hδd.le hε0 hεd.le hr0 hrb heB0 heBd.le
  refine hstep.trans (hfin.trans ?_)
  have : 0 ≤ (N : ℝ) ^ (-(2 : ℝ)) * (z.im ^ 2)⁻¹ *
      opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹ := by
    have := FC_opNorm_nonneg (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ)⁻¹
    positivity
  have hp : 0 ≤ (N : ℝ) ^ τ' := Real.rpow_nonneg hx0.le _
  nlinarith

end

/-- Lemma 3.15 [lem:fourthcumu2] for the law of `H_t` of (4.1) [defVt], `t ∈ [0, 1]`, in the
setting of Lemma 3.7 [lemma_G_large_2]: for `z₁ ∈ {z, z̄}` and deterministic `‖B‖ ≤ 1`,
`1 - ⟨M₁²⟩ ≠ 0` and `|E⟨(G₁ - M₁)B⟩ - e^{-2t} κ₀ N⁻¹ lead15| ≤ N^{τ'} ((Im m)⁻¹ ∧ N^{ε_g})
(N^{-3/2} η⁻¹ + N⁻² η⁻² + N⁻¹ ‖A‖)`, (3.42) [eq:Exp_G1-M1] with `κ^{(2,2)} = e^{-2t} 𝒞^{(2,2)}(νo)`;
the term `N⁻¹ ‖A‖` covers `D = 2`, where `M₁` need not be invariant under the block translation and
`lead15` is then not the exact coefficient. -/
theorem lem_fourthcumu2_theta' (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t → t ≤ 1 →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ) + τe) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ : ℂ, (z₁ = z ∨ z₁ = star z) →
      ∀ B : Matrix (Idx D N) (Idx D N) ℂ, opNorm B ≤ 1 →
        1 - ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₁) ≠ 0 ∧
        ‖(∫ h, ntr ((res (Matrix.of h + lam D N A) z₁ - MExt (lam D N A) z₁) * B)
              ∂(ouMatLaw D N L t)) -
            ((Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 *
              lead15 (lam D N A) z₁ B‖ ≤
          (N : ℝ) ^ τ' * (min ((mExt (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) *
            ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im)⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) * (z.im ^ 2)⁻¹ +
              (N : ℝ)⁻¹ * opNorm A)) := by
  exact FC_P15 D hD δA τ τe εg c hδA hτ hτe hεg hεg₁ hεg₂ hc C

/-- Lemma 3.14 [lem:fourthcumu1] for the law of `H_t` of (4.1) [defVt], `t ∈ [0, 1]`,
`θ = e^{-t}`, in the setting of Lemma 3.7 [lemma_G_large_2]: for `z₁, z₂ ∈ {z, z̄}` and `a, b`,
`1 - M̂₍₁,₂₎P_θ` and `1 - M̂₍₂,₁₎P_θ` are invertible and
`|-D E⟨\underline{G₁E_aM₂HG₂}E_b⟩ - D e^{-2t} κ₀ N⁻¹ lead14| ≤
N^{τ'} (N^{-3/2} η⁻² + N⁻² η⁻² ‖(1 - M̂₍₁,₂₎P_θ)⁻¹‖)`, (3.41) [eq:G1HG2] with
`κ^{(2,2)} = e^{-2t} 𝒞^{(2,2)}(νo)`, `K̃_θ` and the underline for the profile `S_θ`. -/
theorem lem_fourthcumu1_theta (D : ℕ) (hD : 2 ≤ D) (δA τ τe εg c : ℝ) (hδA : 0 < δA)
    (hτ : 0 < τ) (hτe : 0 < τe) (hεg : 0 < εg) (hεg₁ : εg < 1 / 8) (hεg₂ : εg < δA / 4)
    (hc : 1 ≤ c) (C : ℕ → ℝ) :
    ∀ τ' : ℝ, 0 < τ' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t → t ≤ 1 →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z ∈ specDom τ N, 0 < z.im → c⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ) + τe) ≤ z.im →
      c⁻¹ * (N : ℝ) ^ (-εg) ≤ z.im / (mExt (lam D N A) z).im →
      z.im / (mExt (lam D N A) z).im ≤ c * (N : ℝ) ^ (-εg) →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) → ∀ a b : Fin D,
        (1 - Mhat (lam D N A) z₁ z₂ * PTheta D (Real.exp (-t))).det ≠ 0 ∧
        (1 - Mhat (lam D N A) z₂ z₁ * PTheta D (Real.exp (-t))).det ≠ 0 ∧
        ‖-(D : ℂ) * (∫ h, underTwoB (lam D N A) (Real.exp (-t)) h z₁ z₂ a (Ea D N b)
              ∂(ouMatLaw D N L t)) -
            ((D * Real.exp (-(2 * t)) / N : ℝ) : ℂ) * ccum (L.νo : Measure ℂ) 2 2 *
              lead14 (lam D N A) (Real.exp (-t)) z₁ z₂ a b‖ ≤
          (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (z.im ^ 2)⁻¹ + (N : ℝ) ^ (-(2 : ℝ)) *
            (z.im ^ 2)⁻¹ * opNorm (1 - Mhat (lam D N A) z₁ z₂ * PTheta D (Real.exp (-t)))⁻¹) := by
  exact FC_P14 D hD δA τ τe εg c hδA hτ hτe hεg hεg₁ hεg₂ hc C

/-- Circulant identities for `K_θ`, for `z₁, z₂ ∈ {z, z̄}` and `θ ∈ [0, 1]`: with
`K̃_θ(B) = KThetaB Λ θ z₂ z₁ B`, `K̃_{θ,bx}(E_a) = δ_{xa} (K_θ)_{ab}`, `K̃_{θ,bx}(I) = (K_θ)_{xb}`,
`‖M̂ K_θ - (K_θ - M̂)‖ ≤ 1` and `‖P_θ K_θ - K_θ‖ ≤ 1` (the last two vanish at `θ = 1`). -/
theorem KTheta_circ (D : ℕ) (hD : 2 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im → ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) →
      (z₂ = z ∨ z₂ = star z) → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        (1 - Mhat (lam D N A) z₁ z₂ * PTheta D θ).det ≠ 0 ∧
        (1 - Mhat (lam D N A) z₂ z₁ * PTheta D θ).det ≠ 0 ∧
        (∀ a b x : Fin D, KThetaB (lam D N A) θ z₂ z₁ (Ea D N a) b x =
          if x = a then KTheta (lam D N A) θ z₁ z₂ a b else 0) ∧
        (∀ b x : Fin D, KThetaB (lam D N A) θ z₂ z₁ 1 b x = KTheta (lam D N A) θ z₁ z₂ x b) ∧
        opNorm (Mhat (lam D N A) z₁ z₂ * KTheta (lam D N A) θ z₁ z₂ -
          (KTheta (lam D N A) θ z₁ z₂ - Mhat (lam D N A) z₁ z₂)) ≤ 1 ∧
        opNorm (PTheta D θ * KTheta (lam D N A) θ z₁ z₂ - KTheta (lam D N A) θ z₁ z₂) ≤ 1 := by
  exact FC_KTheta_circ D hD δA τ hδA hτ

end RBMTransitionEdge

end
