module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Model.Deterministic
public import RBMTransitionEdge.Det.Core
public import RBMTransitionEdge.Det.Edge
public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.Det.Taylor

@[expose] public section

/-!
# Spectral bounds for `M̂`: Lemma A.1, items (vii)–(xii), and the stability of `1 - M̂`

The resolvent bounds (A.8) [1-M], (A.9) [1-M-2], (A.10) [1-M-3], the flatness (A.11) [flat_M] of
`K = [1 - M̂]⁻¹ M̂`, the spectra (A.14)–(A.18) of `M̂(z, z̄)` and `M̂(z, z)` of Lemma A.1
[lemma_usual_properties_of_m_and_mu], and the bound `‖[1 - M̂(z, z)]⁻¹‖ ≤ C (κ + η)^{-1/2}`.
-/

open MeasureTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

section MS_Tools

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma MS_op_eq (A : Matrix ι ι ℂ) : opNorm A = ‖A‖ := rfl

private lemma MS_op_mul (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [MS_op_eq] using norm_mul_le A B

private lemma MS_op_nonneg (A : Matrix ι ι ℂ) : 0 ≤ opNorm A := norm_nonneg _

private lemma MS_op_conj (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  simpa only [MS_op_eq] using Matrix.l2_opNorm_conjTranspose A

private lemma MS_entry_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [h1, mul_one] at h
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  have h3 : ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)).ofLp i = A i j := by
    simp
  rw [h3] at h2
  exact h2.trans h

private lemma MS_ntr_le [Nonempty ι] (A : Matrix ι ι ℂ) : ‖ntr A‖ ≤ opNorm A := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, opNorm A := Finset.sum_le_sum fun i _ => MS_entry_le A i i
    _ = _ := by simp

/-- `∑ᵢⱼ |Aᵢⱼ|²`. -/
private def MS_S (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq ι] in
private lemma MS_S_nonneg (A : Matrix ι ι ℂ) : 0 ≤ MS_S A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

omit [DecidableEq ι] in
private lemma MS_S_conj (A : Matrix ι ι ℂ) : MS_S Aᴴ = MS_S A := by
  unfold MS_S
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

omit [DecidableEq ι] in
private lemma MS_tr_mul_le (X Y : Matrix ι ι ℂ) :
    ‖(X * Y).trace‖ ≤ Real.sqrt (MS_S X) * Real.sqrt (MS_S Y) := by
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
  have e1 : ∑ p : ι × ι, ‖X p.1 p.2‖ ^ 2 = MS_S X := by
    rw [Fintype.sum_prod_type]; rfl
  have e2 : ∑ p : ι × ι, ‖Y p.2 p.1‖ ^ 2 = MS_S Y := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rw [e1, e2] at h2
  exact h2

private lemma MS_S_mul_le (U B : Matrix ι ι ℂ) : MS_S (U * B) ≤ opNorm U ^ 2 * MS_S B := by
  unfold MS_S
  rw [Finset.sum_comm (f := fun i j => ‖(U * B) i j‖ ^ 2),
    Finset.sum_comm (f := fun i j => ‖B i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := Matrix.l2_opNorm_mulVec U ((EuclideanSpace.equiv ι ℂ).symm (fun i => B i j))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  have e : ∀ i, ((EuclideanSpace.equiv ι ℂ).symm (U *ᵥ ((EuclideanSpace.equiv ι ℂ).symm
      (fun i => B i j)).ofLp)).ofLp i = (U * B) i j := fun i => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [e] at h2
  simpa [MS_op_eq] using h2

/-- `|tr(S^* Y S)| ≤ ‖Y‖ ∑ |S_{ij}|²`. -/
private lemma MS_tr_sandwich (S Y : Matrix ι ι ℂ) :
    ‖(Sᴴ * Y * S).trace‖ ≤ opNorm Y * MS_S S := by
  rw [Matrix.mul_assoc]
  refine (MS_tr_mul_le _ _).trans ?_
  rw [MS_S_conj]
  have h1 : Real.sqrt (MS_S (Y * S)) ≤ opNorm Y * Real.sqrt (MS_S S) := by
    rw [← Real.sqrt_sq (MS_op_nonneg Y), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (MS_S_mul_le Y S)
  calc Real.sqrt (MS_S S) * Real.sqrt (MS_S (Y * S))
      ≤ Real.sqrt (MS_S S) * (opNorm Y * Real.sqrt (MS_S S)) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = opNorm Y * (Real.sqrt (MS_S S) * Real.sqrt (MS_S S)) := by ring
    _ = opNorm Y * MS_S S := by rw [Real.mul_self_sqrt (MS_S_nonneg S)]

omit [DecidableEq ι] in
private lemma MS_trace_mul_conj (Z : Matrix ι ι ℂ) : (Z * Zᴴ).trace = (MS_S Z : ℂ) := by
  unfold MS_S
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

omit [DecidableEq ι] in
private lemma MS_ntr_conj (B : Matrix ι ι ℂ) : ntr Bᴴ = star (ntr B) := by
  simp [ntr, Matrix.trace_conjTranspose]

private lemma MS_ntr_one [Nonempty ι] : ntr (1 : Matrix ι ι ℂ) = 1 := by
  have : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := ι)).ne'
  simp [ntr, Matrix.trace_one, this]

omit [DecidableEq ι] in
private lemma MS_ntr_smul (c : ℂ) (A : Matrix ι ι ℂ) : ntr (c • A) = c * ntr A := by
  simp [ntr, Matrix.trace_smul]; ring

omit [DecidableEq ι] in
private lemma MS_ntr_add (A B : Matrix ι ι ℂ) : ntr (A + B) = ntr A + ntr B := by
  simp [ntr, Matrix.trace_add]; ring

omit [DecidableEq ι] in
private lemma MS_ntr_sub (A B : Matrix ι ι ℂ) : ntr (A - B) = ntr A - ntr B := by
  simp [ntr, Matrix.trace_sub]; ring

omit [DecidableEq ι] in
private lemma MS_ntr_comm (A B : Matrix ι ι ℂ) : ntr (A * B) = ntr (B * A) := by
  simp [ntr, Matrix.trace_mul_comm A B]

end MS_Tools

/-! ### The Fourier basis of `ℂ^D` -/

section MS_Fourier

open scoped Matrix.Norms.L2Operator

/-- The primitive root `ζ = e^{2πi/D}`. -/
private def MS_zeta (D : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / D)

private lemma MS_zeta_prim (D : ℕ) (hD : D ≠ 0) : IsPrimitiveRoot (MS_zeta D) D :=
  Complex.isPrimitiveRoot_exp D hD

private lemma MS_norm_zeta_pow (D : ℕ) (hD : D ≠ 0) (k : ℕ) : ‖MS_zeta D ^ k‖ = 1 := by
  rw [norm_pow, (MS_zeta_prim D hD).norm'_eq_one hD, one_pow]

private lemma MS_star_zeta_pow (D : ℕ) (hD : D ≠ 0) (k : ℕ) :
    star (MS_zeta D ^ k) * MS_zeta D ^ k = 1 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    MS_norm_zeta_pow D hD]
  simp

private lemma MS_fourierVec_eq (D : ℕ) (l a : Fin D) :
    fourierVec D l a = ((Real.sqrt D : ℂ))⁻¹ * MS_zeta D ^ ((l : ℕ) * (a : ℕ)) := by
  unfold fourierVec MS_zeta
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The unitary matrix whose columns are the Fourier vectors `u_l`. -/
private def MS_F (D : ℕ) : Matrix (Fin D) (Fin D) ℂ := Matrix.of fun a l => fourierVec D l a

private lemma MS_sqrt_inv_sq (D : ℕ) :
    star ((Real.sqrt D : ℂ))⁻¹ * ((Real.sqrt D : ℂ))⁻¹ = (D : ℂ)⁻¹ := by
  have h : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt h]
  simp

private lemma MS_F_unitary (D : ℕ) (hD : D ≠ 0) : (MS_F D)ᴴ * MS_F D = 1 := by
  have hζ := MS_zeta_prim D hD
  ext l l'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, MS_F, Matrix.of_apply,
    MS_fourierVec_eq, Matrix.one_apply]
  have e : ∀ a : Fin D, star (((Real.sqrt D : ℂ))⁻¹ * MS_zeta D ^ ((l : ℕ) * (a : ℕ))) *
      (((Real.sqrt D : ℂ))⁻¹ * MS_zeta D ^ ((l' : ℕ) * (a : ℕ))) =
      (D : ℂ)⁻¹ * (star (MS_zeta D ^ (l : ℕ)) * MS_zeta D ^ (l' : ℕ)) ^ (a : ℕ) := by
    intro a
    rw [star_mul', mul_pow, ← star_pow, ← pow_mul, ← pow_mul, ← MS_sqrt_inv_sq D]
    ring
  simp only [e, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun a => (star (MS_zeta D ^ (l : ℕ)) * MS_zeta D ^ (l' : ℕ)) ^ a)]
  by_cases hll : l = l'
  · subst hll
    rw [MS_star_zeta_pow D hD]
    simp [hD]
  · simp only [hll, ↓reduceIte]
    set r := star (MS_zeta D ^ (l : ℕ)) * MS_zeta D ^ (l' : ℕ) with hr
    have hrD : r ^ D = 1 := by
      rw [hr, mul_pow, ← star_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ), mul_comm (l' : ℕ),
        pow_mul, pow_mul, hζ.pow_eq_one, one_pow, one_pow, star_one, one_mul]
    have hr1 : r ≠ 1 := by
      intro h1
      have : MS_zeta D ^ (l' : ℕ) = MS_zeta D ^ (l : ℕ) := by
        have h2 := congrArg (fun x => MS_zeta D ^ (l : ℕ) * x) h1
        simp only [mul_one] at h2
        rw [hr, ← mul_assoc, mul_comm (MS_zeta D ^ (l : ℕ)), MS_star_zeta_pow D hD, one_mul] at h2
        exact h2
      exact hll (Fin.ext (hζ.pow_inj l.isLt l'.isLt this.symm))
    have hg := geom_sum_mul r D
    rw [hrD, sub_self] at hg
    have : ∑ i ∈ Finset.range D, r ^ i = 0 :=
      (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hr1)
    rw [this, mul_zero]

private lemma MS_F_unitary' (D : ℕ) (hD : D ≠ 0) : MS_F D * (MS_F D)ᴴ = 1 :=
  mul_eq_one_comm.mp (MS_F_unitary D hD)

private lemma MS_F_norm (D : ℕ) (hD : D ≠ 0) : ‖MS_F D‖ ≤ 1 := by
  have : Nonempty (Fin D) := ⟨⟨0, Nat.pos_of_ne_zero hD⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (MS_F D)
  rw [MS_F_unitary D hD, norm_one] at h1
  nlinarith [norm_nonneg (MS_F D)]

/-- A matrix with eigenvectors `u_l` and eigenvalues `μ_l` is `F diag(μ) F^*`. -/
private lemma MS_circ (D : ℕ) (hD : D ≠ 0) (B : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ)
    (hB : ∀ l, B *ᵥ fourierVec D l = μ l • fourierVec D l) :
    B = MS_F D * diagonal μ * (MS_F D)ᴴ := by
  have h1 : B * MS_F D = MS_F D * diagonal μ := by
    ext a l
    have := congrFun (hB l) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, MS_F, Matrix.of_apply]
    rw [this, mul_comm]
  calc B = B * (MS_F D * (MS_F D)ᴴ) := by rw [MS_F_unitary' D hD, Matrix.mul_one]
    _ = MS_F D * diagonal μ * (MS_F D)ᴴ := by rw [← Matrix.mul_assoc, h1]

private lemma MS_conjF_norm (D : ℕ) (hD : D ≠ 0) (X : Matrix (Fin D) (Fin D) ℂ) :
    ‖MS_F D * X * (MS_F D)ᴴ‖ = ‖X‖ := by
  have hF := MS_F_norm D hD
  have hF' : ‖(MS_F D)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hF
  apply le_antisymm
  · calc ‖MS_F D * X * (MS_F D)ᴴ‖ ≤ ‖MS_F D‖ * ‖X‖ * ‖(MS_F D)ᴴ‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖X‖ * 1 := by gcongr
      _ = ‖X‖ := by ring
  · have e : X = (MS_F D)ᴴ * (MS_F D * X * (MS_F D)ᴴ) * MS_F D := by
      simp only [← Matrix.mul_assoc, MS_F_unitary D hD, Matrix.one_mul]
      rw [Matrix.mul_assoc, MS_F_unitary D hD, Matrix.mul_one]
    calc ‖X‖ = ‖(MS_F D)ᴴ * (MS_F D * X * (MS_F D)ᴴ) * MS_F D‖ := by rw [← e]
      _ ≤ ‖(MS_F D)ᴴ‖ * ‖MS_F D * X * (MS_F D)ᴴ‖ * ‖MS_F D‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖MS_F D * X * (MS_F D)ᴴ‖ * 1 := by gcongr
      _ = _ := by ring

/-- For `B` with eigenvectors `u_l` and eigenvalues `μ_l ≠ 1`: `1 - B` is invertible,
`(1 - B)⁻¹ = F diag((1 - μ)⁻¹) F^*`, and `‖(1 - B)⁻¹‖ = max_l |1 - μ_l|⁻¹`. -/
private lemma MS_circ_inv (D : ℕ) (hD : D ≠ 0) (B : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ)
    (hB : ∀ l, B *ᵥ fourierVec D l = μ l • fourierVec D l) (hμ : ∀ l, 1 - μ l ≠ 0) :
    (1 - B).det ≠ 0 ∧
      (1 - B)⁻¹ = MS_F D * diagonal (fun l => (1 - μ l)⁻¹) * (MS_F D)ᴴ ∧
      opNorm ((1 - B)⁻¹) = ‖fun l => (1 - μ l)⁻¹‖ := by
  have hc := MS_circ D hD B μ hB
  have h1 : 1 - B = MS_F D * diagonal (fun l => 1 - μ l) * (MS_F D)ᴴ := by
    have : diagonal (fun l => 1 - μ l) = 1 - diagonal μ := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, MS_F_unitary' D hD, ← hc]
  have hinv : (1 - B)⁻¹ = MS_F D * diagonal (fun l => (1 - μ l)⁻¹) * (MS_F D)ᴴ := by
    rw [h1]
    apply Matrix.inv_eq_right_inv
    have e : MS_F D * diagonal (fun l => 1 - μ l) * (MS_F D)ᴴ *
        (MS_F D * diagonal (fun l => (1 - μ l)⁻¹) * (MS_F D)ᴴ) =
        MS_F D * (diagonal (fun l => 1 - μ l) * ((MS_F D)ᴴ * MS_F D) *
          diagonal (fun l => (1 - μ l)⁻¹)) * (MS_F D)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, MS_F_unitary D hD, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    have : (fun l => (1 - μ l) * (1 - μ l)⁻¹) = fun _ => (1 : ℂ) := by
      funext l; exact mul_inv_cancel₀ (hμ l)
    rw [this, Matrix.diagonal_one, Matrix.mul_one, MS_F_unitary' D hD]
  refine ⟨?_, hinv, ?_⟩
  · rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hdet : (MS_F D).det * ((MS_F D)ᴴ).det = 1 := by
      rw [← Matrix.det_mul, MS_F_unitary' D hD, Matrix.det_one]
    have : (MS_F D).det * (∏ l, (1 - μ l)) * ((MS_F D)ᴴ).det = ∏ l, (1 - μ l) := by
      linear_combination (∏ l, (1 - μ l)) * hdet
    rw [this]
    exact Finset.prod_ne_zero_iff.2 fun l _ => hμ l
  · rw [hinv, MS_op_eq, MS_conjF_norm D hD, Matrix.l2_opNorm_diagonal]

/-- The eigenvalue `circEig B l` read off the row `0`: `λ̂_l = Σ_b B_{0b} ζ^{lb}`. -/
private lemma MS_circEig_row (D : ℕ) [NeZero D] (B : Matrix (Fin D) (Fin D) ℂ) (l : Fin D)
    (hB : B *ᵥ fourierVec D l = circEig B l • fourierVec D l) :
    circEig B l = ∑ b : Fin D, B 0 b * MS_zeta D ^ ((l : ℕ) * (b : ℕ)) := by
  have hD : D ≠ 0 := NeZero.ne D
  have := congrFun hB 0
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, MS_fourierVec_eq,
    Fin.val_zero, mul_zero, pow_zero, mul_one] at this
  have hs : ((Real.sqrt D : ℂ))⁻¹ ≠ 0 := by
    refine inv_ne_zero ?_
    rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
    exact_mod_cast Nat.pos_of_ne_zero hD
  have e : ∑ x : Fin D, B 0 x * (((Real.sqrt D : ℂ))⁻¹ * MS_zeta D ^ ((l : ℕ) * (x : ℕ))) =
      ((Real.sqrt D : ℂ))⁻¹ * ∑ b : Fin D, B 0 b * MS_zeta D ^ ((l : ℕ) * (b : ℕ)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [e] at this
  rw [mul_comm (circEig B l)] at this
  exact (mul_left_cancel₀ hs this).symm

/-- `λ̂_0 = D⁻¹ Σ_{a,b} B_{ab}`. -/
private lemma MS_circEig_zero (D : ℕ) [NeZero D] (B : Matrix (Fin D) (Fin D) ℂ) :
    circEig B 0 = (D : ℂ)⁻¹ * ∑ a : Fin D, ∑ b : Fin D, B a b := by
  have hD : D ≠ 0 := NeZero.ne D
  unfold circEig
  simp only [MS_fourierVec_eq, Fin.val_zero, zero_mul, pow_zero, mul_one]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← MS_sqrt_inv_sq D]
  ring

end MS_Fourier

/-! ### The interaction `Λ` and the block projections -/

section MS_Lam

open scoped Matrix.Norms.L2Operator

private lemma MS_fwd_self (D : ℕ) (a : Fin D) : ¬ fwd D a a := by
  unfold fwd; omega

private lemma MS_fwd_not_both (D : ℕ) (a b : Fin D) : ¬ (fwd D a b ∧ fwd D b a) := by
  unfold fwd; omega

private lemma MS_ntr_lam (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : ntr (lam D N A) = 0 := by
  have h : ∀ p : Idx D N, lam D N A p p = 0 := fun p => by simp [lam, MS_fwd_self]
  simp [ntr, Matrix.trace, Matrix.diag, h]

/-- The embedding of `ℂ^N` as the block `a`. -/
private def MS_J (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Fin N) ℂ :=
  Matrix.of fun p i => if p = (a, i) then 1 else 0

private lemma MS_J_conj_mul (D N : ℕ) (a : Fin D) : (MS_J D N a)ᴴ * MS_J D N a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, MS_J, Matrix.of_apply, Matrix.one_apply]
  have : ∀ p : Idx D N, star (if p = (a, i) then (1 : ℂ) else 0) * (if p = (a, j) then 1 else 0) =
      if p = (a, i) then (if i = j then 1 else 0) else 0 := by
    intro p
    by_cases h : p = (a, i)
    · subst h
      by_cases hij : i = j <;> simp [hij]
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma MS_J_norm (D N : ℕ) (hN : 1 ≤ N) (a : Fin D) : ‖MS_J D N a‖ ≤ 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (MS_J D N a)
  rw [MS_J_conj_mul, norm_one] at h1
  have h0 : 0 ≤ ‖MS_J D N a‖ := norm_nonneg _
  nlinarith

private lemma MS_block_norm (D N : ℕ) (hN : 1 ≤ N) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖MS_J D N a * M * (MS_J D N b)ᴴ‖ ≤ ‖M‖ := by
  have ha := MS_J_norm D N hN a
  have hb := MS_J_norm D N hN b
  calc ‖MS_J D N a * M * (MS_J D N b)ᴴ‖ ≤ ‖MS_J D N a * M‖ * ‖(MS_J D N b)ᴴ‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖MS_J D N a‖ * ‖M‖) * ‖(MS_J D N b)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
    _ = ‖M‖ := by ring

private lemma MS_block_apply (D N : ℕ) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ)
    (p q : Idx D N) :
    (MS_J D N a * M * (MS_J D N b)ᴴ) p q = if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = a <;> by_cases h2 : q1 = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, MS_J, Prod.ext_iff, h1, h2]

private lemma MS_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = ∑ a : Fin D, ∑ b : Fin D,
      ((if fwd D a b then MS_J D N a * A * (MS_J D N b)ᴴ else 0) +
        (if fwd D b a then MS_J D N a * Aᴴ * (MS_J D N b)ᴴ else 0)) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.add_apply]
  have e1 : ∀ a b : Fin D, (if fwd D a b then MS_J D N a * A * (MS_J D N b)ᴴ else 0) p q =
      if fwd D a b ∧ p.1 = a ∧ q.1 = b then A p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D a b <;> simp [h, MS_block_apply]
  have e2 : ∀ a b : Fin D, (if fwd D b a then MS_J D N a * Aᴴ * (MS_J D N b)ᴴ else 0) p q =
      if fwd D b a ∧ p.1 = a ∧ q.1 = b then Aᴴ p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D b a <;> simp [h, MS_block_apply]
  simp only [e1, e2, Finset.sum_add_distrib]
  unfold lam
  congr 1
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D p.1 q.1 <;> simp [h]
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D q.1 p.1 <;> simp [h, Matrix.conjTranspose_apply]

/-- `‖Λ‖ ≤ 2 D² ‖A‖`. -/
private lemma MS_opNorm_lam (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := by
  change ‖lam D N A‖ ≤ 2 * (D : ℝ) ^ 2 * ‖A‖
  rw [MS_lam_eq]
  have hb : ∀ a b : Fin D, ‖(if fwd D a b then MS_J D N a * A * (MS_J D N b)ᴴ else 0) +
      (if fwd D b a then MS_J D N a * Aᴴ * (MS_J D N b)ᴴ else 0)‖ ≤ 2 * ‖A‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D a b then MS_J D N a * A * (MS_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact MS_block_norm D N hN a b A
      · simp
    have h2 : ‖(if fwd D b a then MS_J D N a * Aᴴ * (MS_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact (MS_block_norm D N hN a b Aᴴ).trans (by rw [Matrix.l2_opNorm_conjTranspose])
      · simp
    linarith
  calc ‖∑ a : Fin D, ∑ b : Fin D, _‖ ≤ ∑ a : Fin D, ‖∑ b : Fin D, _‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin D, ∑ b : Fin D, 2 * ‖A‖ := by
        refine Finset.sum_le_sum fun a _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb a b)
    _ = 2 * (D : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `‖A‖²_HS ≤ N ‖A‖²`. -/
private lemma MS_S_le_card {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : Matrix ι ι ℂ) :
    MS_S Z ≤ (Fintype.card ι : ℝ) * opNorm Z ^ 2 := by
  have h1 : ∀ q : ι, ∑ p, ‖Z p q‖ ^ 2 ≤ opNorm Z ^ 2 := by
    intro q
    have h := Matrix.l2_opNorm_mulVec Z (EuclideanSpace.single q (1 : ℂ))
    have h0 : ‖EuclideanSpace.single q (1 : ℂ)‖ = 1 := by simp
    rw [h0, mul_one] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [EuclideanSpace.norm_sq_eq] at h2
    have e : ∀ p, ((EuclideanSpace.equiv ι ℂ).symm
        (Z *ᵥ (EuclideanSpace.single q (1 : ℂ)).ofLp)).ofLp p = Z p q := fun p => by simp
    simp only [e] at h2
    exact h2
  unfold MS_S
  rw [Finset.sum_comm]
  calc ∑ y, ∑ x, ‖Z x y‖ ^ 2 ≤ ∑ _y : ι, opNorm Z ^ 2 := Finset.sum_le_sum fun q _ => h1 q
    _ = _ := by simp

private lemma MS_Ea_conj (D N : ℕ) (a : Fin D) : (Ea D N a)ᴴ = Ea D N a := by
  unfold Ea
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.1 = a <;> simp [h]

private lemma MS_Ea_sq (D N : ℕ) (a : Fin D) : Ea D N a * Ea D N a = Ea D N a := by
  unfold Ea
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp

private lemma MS_Ea_mul_ne (D N : ℕ) (a b : Fin D) (hab : a ≠ b) :
    Ea D N a * Ea D N b = 0 := by
  unfold Ea
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext p
  by_cases h : p.1 = a
  · simp [h, hab]
  · simp [h]

private lemma MS_sum_Ea (D N : ℕ) : ∑ a : Fin D, Ea D N a = 1 := by
  ext p q
  rw [Matrix.sum_apply]
  simp only [Ea, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : p = q
  · simp [h]
  · simp [h]

private lemma MS_Ea_norm (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  rw [MS_op_eq]
  unfold Ea
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
  split_ifs <;> simp

private lemma MS_mul_Ea_apply (D N : ℕ) (X : Matrix (Idx D N) (Idx D N) ℂ) (a : Fin D)
    (p q : Idx D N) : (X * Ea D N a) p q = if q.1 = a then X p q else 0 := by
  unfold Ea
  rw [Matrix.mul_diagonal]
  split_ifs <;> simp

/-- The weight `χ_c ∈ {0, 1}` of the block `(c, 0)` of `Λ`. -/
private def MS_chi (D : ℕ) [NeZero D] (c : Fin D) : ℝ :=
  (if fwd D c 0 then 1 else 0) + (if fwd D 0 c then 1 else 0)

/-- `Σ_{i,j} |Λ_{(c,i),(0,j)}|² = χ_c ‖A‖²_HS`. -/
private lemma MS_blk (D N : ℕ) [NeZero D] (A : Matrix (Fin N) (Fin N) ℂ) (c : Fin D) :
    ∑ i : Fin N, ∑ j : Fin N, ‖lam D N A (c, i) (0, j)‖ ^ 2 = MS_chi D c * MS_S A := by
  have hnb := MS_fwd_not_both D c 0
  unfold MS_chi MS_S
  by_cases h1 : fwd D c 0
  · have h2 : ¬ fwd D 0 c := fun h => hnb ⟨h1, h⟩
    simp [lam, h1, h2]
  · by_cases h2 : fwd D 0 c
    · simp only [lam, h1, h2, ↓reduceIte, zero_add, norm_star, one_mul]
      exact Finset.sum_comm
    · simp [lam, h1, h2]

/-- `‖ΛE_0‖²_HS = Σ_c χ_c ‖A‖²_HS`. -/
private lemma MS_S_lamE (D N : ℕ) [NeZero D] (A : Matrix (Fin N) (Fin N) ℂ) :
    MS_S (lam D N A * Ea D N 0) = (∑ c : Fin D, MS_chi D c) * MS_S A := by
  rw [Finset.sum_mul, ← Finset.sum_congr rfl fun c _ => MS_blk D N A c]
  unfold MS_S
  simp only [MS_mul_Ea_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (0 : Fin D)]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- `tr(S^* diag(d) S) = Σ_{q,p} d_p |S_{pq}|²`. -/
private lemma MS_tr_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℂ)
    (d : ι → ℂ) :
    (Sᴴ * diagonal d * S).trace = ∑ q, ∑ p, d p * (‖S p q‖ : ℂ) ^ 2 := by
  unfold Matrix.trace Matrix.diag
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, ← Complex.conj_mul', ← Complex.star_def]
  ring

/-- `tr(E_0 Λ E_c Λ E_0) = χ_c ‖A‖²_HS`. -/
private lemma MS_tr_blk (D N : ℕ) [NeZero D] (A : Matrix (Fin N) (Fin N) ℂ) (c : Fin D) :
    ((lam D N A * Ea D N 0)ᴴ * Ea D N c * (lam D N A * Ea D N 0)).trace =
      ((MS_chi D c * MS_S A : ℝ) : ℂ) := by
  rw [← MS_blk D N A c]
  conv_lhs => rw [show Ea D N c = diagonal fun p => if p.1 = c then 1 else 0 from rfl]
  rw [MS_tr_diag]
  simp only [MS_mul_Ea_apply, Fintype.sum_prod_type]
  push_cast
  rw [Fintype.sum_eq_single (M := ℂ) (0 : Fin D) (fun x hx => by simp [hx])]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_eq_single (M := ℂ) c (fun x hx => by simp [hx])]
  simp

end MS_Lam

/-! ### The resolvent `M` at `z` and `z̄` -/

section MS_Res

open scoped Matrix.Norms.L2Operator

private lemma MS_alg {ι : Type*} [Fintype ι] [DecidableEq ι] {Λ M : Matrix ι ι ℂ} {w : ℂ}
    (h : (Λ - w • (1 : Matrix ι ι ℂ)) * M = 1) :
    w • M = M * Λ - 1 ∧ w • M = Λ * M - 1 := by
  have h' := mul_eq_one_comm.mp h
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one] at h h'
  exact ⟨by rw [← h']; abel, by rw [← h]; abel⟩

private lemma MS_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) {z : ℂ}
    (hz : 0 < z.im) : mExt Λ z = mSol Λ z ∧ MExt Λ z = MSol Λ z := by
  have h : mExt Λ z = mSol Λ z := by simp only [mExt, hz, ↓reduceIte]
  exact ⟨h, by rw [MExt, MSol, h]⟩

/-- For `Im z > 0` and `z₁ ∈ {z, z̄}`, with `w₁ = z₁ + m(z₁)` and `M₁ = M(z₁)`:
`w₁ M₁ = M₁ Λ - 1 = Λ M₁ - 1`, `‖M₁‖ ≤ 5/4` and `9/10 < |w₁| ≤ |z| + 1`. -/
private lemma MS_res {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Λ : Matrix ι ι ℂ}
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ} (hz : 0 < z.im) {z₁ : ℂ}
    (h₁ : z₁ = z ∨ z₁ = star z) :
    (z₁ + mExt Λ z₁) • MExt Λ z₁ = MExt Λ z₁ * Λ - 1 ∧
      (z₁ + mExt Λ z₁) • MExt Λ z₁ = Λ * MExt Λ z₁ - 1 ∧
      opNorm (MExt Λ z₁) ≤ 5 / 4 ∧ 9 / 10 < ‖z₁ + mExt Λ z₁‖ ∧
      ‖z₁ + mExt Λ z₁‖ ≤ ‖z‖ + 1 := by
  obtain ⟨hm, hM⟩ := MS_pos Λ hz
  obtain ⟨a1, a2, a3⟩ := mSol_apriori Λ hΛ hℓ z hz
  obtain ⟨-, -, hinv⟩ := mSol_spec Λ hΛ z hz
  have hl0 : 0 ≤ opNorm Λ := MS_op_nonneg Λ
  have hM54 : opNorm (MSol Λ z) ≤ 5 / 4 := by
    refine a3.le.trans ?_
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hw1 : ‖z + mSol Λ z‖ ≤ ‖z‖ + 1 := (norm_add_le _ _).trans (by linarith)
  rcases h₁ with rfl | rfl
  · rw [hm, hM]
    obtain ⟨e1, e2⟩ := MS_alg hinv
    exact ⟨e1, e2, hM54, by linarith, hw1⟩
  · obtain ⟨c1, c2⟩ := mExt_conj Λ hΛ z hz.ne'
    rw [c1, c2, hm, hM]
    have hinv' : (Λ - (star z + star (mSol Λ z)) • (1 : Matrix ι ι ℂ)) * (MSol Λ z)ᴴ = 1 := by
      have h4 := congrArg Matrix.conjTranspose (mul_eq_one_comm.mp hinv)
      rwa [conjTranspose_mul, conjTranspose_one, conjTranspose_sub, conjTranspose_smul,
        conjTranspose_one, hΛ.eq, star_add] at h4
    obtain ⟨e1, e2⟩ := MS_alg hinv'
    have hn : ‖star z + star (mSol Λ z)‖ = ‖z + mSol Λ z‖ := by
      rw [← star_add, norm_star]
    refine ⟨e1, e2, by rw [MS_op_conj]; exact hM54, by rw [hn]; linarith, ?_⟩
    rw [hn]; exact hw1

/-- For `Λ = lam D N A`, `Im z > 0`, `M = M(z)` and `d₁ = Im m / (Im m + η)` ((A.3)
[equation_z_im_m]): `M^* M = M M^*`, `⟨M M^*⟩ = d₁`, `D ⟨M M^* E_a⟩ = d₁` and
`Re ⟨M²⟩ ≤ d₁`. -/
private lemma MS_dfacts (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im) :
    (MExt (lam D N A) z)ᴴ * MExt (lam D N A) z =
        MExt (lam D N A) z * (MExt (lam D N A) z)ᴴ ∧
      ntr (MExt (lam D N A) z * (MExt (lam D N A) z)ᴴ) =
        (((mSol (lam D N A) z).im / ((mSol (lam D N A) z).im + z.im) : ℝ) : ℂ) ∧
      (∀ a : Fin D, (D : ℂ) * ntr (MExt (lam D N A) z * (MExt (lam D N A) z)ᴴ * Ea D N a) =
        (((mSol (lam D N A) z).im / ((mSol (lam D N A) z).im + z.im) : ℝ) : ℂ)) ∧
      (ntr (MExt (lam D N A) z * MExt (lam D N A) z)).re ≤
        (mSol (lam D N A) z).im / ((mSol (lam D N A) z).im + z.im) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  obtain ⟨hm, hM⟩ := MS_pos (lam D N A) hz
  have hsc := (def_M_scalar D hD N hN A z hz.ne').1
  rw [hM] at hsc ⊢
  rw [hm] at hsc
  obtain ⟨hpos, -, hinv⟩ := mSol_spec (lam D N A) hΛ z hz
  obtain ⟨h1, h2⟩ := equation_z_im_m (lam D N A) hΛ z hz
  set Λ := lam D N A with hΛdef
  set M := MSol Λ z with hMdef
  set m := mSol Λ z with hmdef
  obtain ⟨e1, e2⟩ := MS_alg hinv
  have hcomm : Λ * M = M * Λ := by
    have := e1.symm.trans e2
    exact (sub_left_inj.mp this).symm
  have hcommH : Λ * Mᴴ = Mᴴ * Λ := by
    have := congrArg Matrix.conjTranspose hcomm
    rw [conjTranspose_mul, conjTranspose_mul, hΛ.eq] at this
    exact this.symm
  have hinv' := mul_eq_one_comm.mp hinv
  have hX : (Λ - (z + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * Mᴴ =
      Mᴴ * (Λ - (z + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hcommH, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hnorm : Mᴴ * M = M * Mᴴ := by
    calc Mᴴ * M = M * (Λ - (z + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * Mᴴ * M := by
          rw [hinv', Matrix.one_mul]
      _ = M * (Mᴴ * ((Λ - (z + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M)) := by
          rw [Matrix.mul_assoc M, hX]; simp only [Matrix.mul_assoc]
      _ = M * Mᴴ := by rw [hinv, Matrix.mul_one]
  set d : ℝ := m.im / (m.im + z.im) with hd
  set b : ℝ := z.im + m.im with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  set c : ℂ := 2 * Complex.I * (b : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) ?_
    exact_mod_cast hb0.ne'
  refine ⟨hnorm, h1, ?_, ?_⟩
  · intro a
    have hEa := MS_Ea_conj D N a
    have k1 : (D : ℂ) * ntr (Mᴴ * Ea D N a) = star m := by
      have : Mᴴ * Ea D N a = (Ea D N a * M)ᴴ := by
        rw [conjTranspose_mul, hEa]
      rw [this, MS_ntr_conj, MS_ntr_comm, ← hsc a, star_mul', Complex.star_def,
        Complex.conj_natCast]
    have k2 : c * ((D : ℂ) * ntr (M * Mᴴ * Ea D N a)) = m - star m := by
      calc c * ((D : ℂ) * ntr (M * Mᴴ * Ea D N a))
          = (D : ℂ) * ntr ((c • (M * Mᴴ)) * Ea D N a) := by
            rw [Matrix.smul_mul, MS_ntr_smul]; ring
        _ = (D : ℂ) * ntr ((M - Mᴴ) * Ea D N a) := by rw [h2]
        _ = (D : ℂ) * ntr (M * Ea D N a) - (D : ℂ) * ntr (Mᴴ * Ea D N a) := by
            rw [Matrix.sub_mul, MS_ntr_sub]; ring
        _ = m - star m := by rw [hsc a, k1]
    have k3 : m - star m = 2 * Complex.I * (m.im : ℂ) := by
      apply Complex.ext <;> simp; ring
    rw [k3] at k2
    have : (D : ℂ) * ntr (M * Mᴴ * Ea D N a) = (m.im : ℂ) / (b : ℂ) := by
      have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
      rw [eq_div_iff hb']
      have h2I : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
      apply mul_left_cancel₀ h2I
      rw [hc] at k2
      linear_combination k2
    rw [this, hd, hb]
    push_cast
    ring
  · have key : M * M + Mᴴ * Mᴴ = (M - Mᴴ) * (M - Mᴴ) + (2 : ℂ) • (M * Mᴴ) := by
      rw [two_smul]
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      rw [hnorm]
      abel
    rw [h2, smul_mul_smul_comm] at key
    have k := congrArg ntr key
    rw [MS_ntr_add, MS_ntr_add, MS_ntr_smul, MS_ntr_smul, h1] at k
    have hHH : Mᴴ * Mᴴ = (M * M)ᴴ := by rw [conjTranspose_mul]
    rw [hHH, MS_ntr_conj] at k
    have hP : (M * Mᴴ) * (M * Mᴴ) = (M * Mᴴ) * (M * Mᴴ)ᴴ := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [hP] at k
    have hPP : ntr ((M * Mᴴ) * (M * Mᴴ)ᴴ) =
        (((Fintype.card (Idx D N) : ℝ)⁻¹ * MS_S (M * Mᴴ) : ℝ) : ℂ) := by
      unfold ntr
      rw [MS_trace_mul_conj]
      push_cast
      ring
    rw [hPP] at k
    have hre := congrArg Complex.re k
    have hcc : (2 * Complex.I * (b : ℂ)) * (2 * Complex.I * (b : ℂ)) =
        ((-(4 * b ^ 2) : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hcc] at hre
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
    have hS := MS_S_nonneg (M * Mᴴ)
    have hcard : (0 : ℝ) ≤ (Fintype.card (Idx D N) : ℝ)⁻¹ := by positivity
    have : 0 ≤ 4 * b ^ 2 * ((Fintype.card (Idx D N) : ℝ)⁻¹ * MS_S (M * Mᴴ)) := by positivity
    simp only [Complex.re_ofNat] at hre
    nlinarith

/-- `M̂_{ab}` of (3.1) [def_ML] as `N⁻¹ Σ_{i,j} M(z₁)_{(b,j),(a,i)} M(z₂)_{(a,i),(b,j)}`. -/
private lemma MS_Mhat_apply (D N : ℕ) (hD : D ≠ 0) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z₁ z₂ : ℂ) (a b : Fin D) :
    Mhat Λ z₁ z₂ a b = (N : ℂ)⁻¹ *
      ∑ i : Fin N, ∑ j : Fin N, MExt Λ z₁ (b, j) (a, i) * MExt Λ z₂ (a, i) (b, j) := by
  have h1 : (D : ℂ) * ((Fintype.card (Idx D N) : ℂ))⁻¹ = (N : ℂ)⁻¹ := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    have : (D : ℂ) ≠ 0 := by exact_mod_cast hD
    field_simp
  have h2 : (MExt Λ z₁ * Ea D N a * MExt Λ z₂ * Ea D N b).trace =
      ∑ i : Fin N, ∑ j : Fin N, MExt Λ z₁ (b, j) (a, i) * MExt Λ z₂ (a, i) (b, j) := by
    simp only [Matrix.trace, Matrix.diag, Ea, Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.diagonal_apply]
    simp [ite_and]
    exact Finset.sum_comm
  unfold Mhat ntr
  rw [← mul_assoc, h1, h2]

/-- `D ⟨X⟩ = N⁻¹ tr X` on `Idx D N`. -/
private lemma MS_D_ntr (D N : ℕ) (hD : D ≠ 0) (X : Matrix (Idx D N) (Idx D N) ℂ) :
    (D : ℂ) * ntr X = (N : ℂ)⁻¹ * X.trace := by
  unfold ntr
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  by_cases hN : (N : ℂ) = 0
  · simp [hN]
  · field_simp

/-- The row sums of `M̂`: `Σ_b M̂_{ab} = D ⟨M(z₁) E_a M(z₂)⟩`. -/
private lemma MS_rowsum (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z₁ z₂ : ℂ) (a : Fin D) :
    ∑ b, Mhat Λ z₁ z₂ a b = (D : ℂ) * ntr (MExt Λ z₁ * Ea D N a * MExt Λ z₂) := by
  unfold Mhat
  rw [← Finset.mul_sum]
  congr 1
  conv_rhs => rw [← Matrix.mul_one (MExt Λ z₁ * Ea D N a * MExt Λ z₂), ← MS_sum_Ea D N]
  rw [Matrix.mul_sum]
  simp only [ntr, Matrix.trace_sum, Finset.mul_sum]

/-- `λ̂_0 = ⟨M(z₁) M(z₂)⟩`. -/
private lemma MS_circEig_zero_Mhat (D N : ℕ) [NeZero D] (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (z₁ z₂ : ℂ) : circEig (Mhat Λ z₁ z₂) 0 = ntr (MExt Λ z₁ * MExt Λ z₂) := by
  have hD : (D : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne D
  rw [MS_circEig_zero]
  simp only [MS_rowsum]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  conv_rhs => rw [← Matrix.mul_one (MExt Λ z₁), ← MS_sum_Ea D N]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp only [ntr, Matrix.trace_sum, Finset.mul_sum]

end MS_Res

/-! ### The spectrum of `M̂` -/

section MS_Spec

open scoped Matrix.Norms.L2Operator

/-- The weight `g_l = Σ_c χ_c (1 - ζ^{lc})` of the leading term of `λ̂_0 - λ̂_l`. -/
private def MS_g (D : ℕ) [NeZero D] (l : Fin D) : ℂ :=
  ∑ c : Fin D, (MS_chi D c : ℂ) * (1 - MS_zeta D ^ ((l : ℕ) * (c : ℕ)))

/-- `g_l` is real, `0 ≤ g_l ≤ 4D`, and `g_l ≥ g₀ > 0` for `l ≠ 0`. -/
private lemma MS_g_facts (D : ℕ) (hD : 2 ≤ D) [NeZero D] :
    ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ l : Fin D, (MS_g D l).im = 0 ∧ 0 ≤ (MS_g D l).re ∧
      ‖MS_g D l‖ ≤ 4 * D ∧ ((l : ℕ) ≠ 0 → g₀ ≤ (MS_g D l).re) := by
  have hD0 : D ≠ 0 := by omega
  have hζ := MS_zeta_prim D hD0
  -- the two neighbours of the block `0`
  have hval : ∀ l : Fin D, MS_g D l = (1 - MS_zeta D ^ (l : ℕ)) +
      (if 3 ≤ D then 1 - MS_zeta D ^ ((l : ℕ) * (D - 1)) else 0) := by
    intro l
    unfold MS_g MS_chi
    simp only [Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [Fintype.sum_eq_single (⟨1, by omega⟩ : Fin D)]
      · simp [fwd]
      · intro c hc
        have : ¬ fwd D 0 c := by
          unfold fwd
          intro h
          apply hc
          simp only [Fin.val_zero] at h
          exact Fin.ext (show (c : ℕ) = 1 by omega)
        simp [this]
    · by_cases h3 : 3 ≤ D
      · simp only [h3, ↓reduceIte]
        rw [Fintype.sum_eq_single (⟨D - 1, by omega⟩ : Fin D)]
        · have : fwd D (⟨D - 1, by omega⟩ : Fin D) 0 :=
            Or.inr ⟨h3, by simp only; omega, by simp⟩
          simp [this]
        · intro c hc
          have : ¬ fwd D c 0 := by
            unfold fwd
            intro h
            apply hc
            simp only [Fin.val_zero] at h
            exact Fin.ext (show (c : ℕ) = D - 1 by omega)
          simp [this]
      · simp only [h3, ↓reduceIte]
        refine Finset.sum_eq_zero fun c _ => ?_
        have : ¬ fwd D c 0 := by unfold fwd; simp only [Fin.val_zero]; omega
        simp [this]
  have hstar : ∀ l : ℕ, MS_zeta D ^ (l * (D - 1)) = star (MS_zeta D ^ l) := by
    intro l
    have h1 : MS_zeta D ^ (l * (D - 1)) * MS_zeta D ^ l = 1 := by
      rw [← pow_add, show l * (D - 1) + l = D * l by
        rw [mul_comm D]; cases D with
        | zero => omega
        | succ n => simp [Nat.mul_succ]]
      rw [pow_mul, hζ.pow_eq_one, one_pow]
    have h2 := MS_star_zeta_pow D hD0 l
    have hne : MS_zeta D ^ l ≠ 0 := by
      intro h; have := MS_norm_zeta_pow D hD0 l; rw [h, norm_zero] at this; norm_num at this
    exact mul_right_cancel₀ hne (h1.trans h2.symm)
  have hre1 : ∀ l : ℕ, (MS_zeta D ^ l).re ≤ 1 := by
    intro l
    have := Complex.re_le_norm (MS_zeta D ^ l)
    rwa [MS_norm_zeta_pow D hD0] at this
  -- positivity of `1 - Re ζ^l` for `l ≠ 0`
  have hpos : ∀ l : Fin D, (l : ℕ) ≠ 0 → 0 < 1 - (MS_zeta D ^ (l : ℕ)).re := by
    intro l hl
    have hne : MS_zeta D ^ (l : ℕ) ≠ 1 := by
      intro h
      have := (hζ.pow_eq_one_iff_dvd _).1 h
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hl) this
      omega
    by_contra hc
    have hre : (MS_zeta D ^ (l : ℕ)).re = 1 := le_antisymm (hre1 _) (by linarith)
    have hn := MS_norm_zeta_pow D hD0 (l : ℕ)
    have hsq : (MS_zeta D ^ (l : ℕ)).re ^ 2 + (MS_zeta D ^ (l : ℕ)).im ^ 2 = 1 := by
      have := Complex.sq_norm (MS_zeta D ^ (l : ℕ))
      rw [hn, Complex.normSq_apply] at this
      nlinarith
    have him : (MS_zeta D ^ (l : ℕ)).im = 0 := by rw [hre] at hsq; nlinarith
    exact hne (Complex.ext (by simp [hre]) (by simp [him]))
  obtain ⟨l₀, hl₀⟩ := Finite.exists_min
    (fun l : Fin D => if (l : ℕ) = 0 then (1 : ℝ) else 1 - (MS_zeta D ^ (l : ℕ)).re)
  have hg₀ : 0 < (if (l₀ : ℕ) = 0 then (1 : ℝ) else 1 - (MS_zeta D ^ (l₀ : ℕ)).re) := by
    split_ifs with h
    · norm_num
    · exact hpos l₀ h
  refine ⟨_, hg₀, fun l => ?_⟩
  have hmin := hl₀ l
  have ht1 := hre1 (l : ℕ)
  have htn := MS_norm_zeta_pow D hD0 (l : ℕ)
  have hpl := hpos l
  have hst := hstar (l : ℕ)
  have h4D : (4 : ℝ) ≤ 4 * D := by
    have : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    linarith
  rw [hval l]
  by_cases h3 : 3 ≤ D
  · simp only [h3, ↓reduceIte]
    rw [hst]
    generalize MS_zeta D ^ (l : ℕ) = t at *
    have hn1 : ‖1 - t‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, htn]; norm_num
    have hn2 : ‖1 - star t‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_star, htn]; norm_num
    have hre : (1 - t + (1 - star t)).re = 2 * (1 - t.re) := by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.star_def,
        Complex.conj_re]
      ring
    refine ⟨by simp, ?_, ?_, ?_⟩
    · rw [hre]; linarith
    · exact (norm_add_le _ _).trans (by linarith)
    · intro hl
      rw [hre]
      simp only [hl, ↓reduceIte] at hmin
      linarith [hpl hl]
  · simp only [h3, ↓reduceIte, add_zero]
    have hD1 : D - 1 = 1 := by omega
    rw [hD1, mul_one] at hst
    generalize MS_zeta D ^ (l : ℕ) = t at *
    have hreal : t.im = 0 := by
      have := congrArg Complex.im hst
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    refine ⟨by simp [hreal], ?_, ?_, ?_⟩
    · simp only [Complex.sub_re, Complex.one_re]; linarith
    · have hn1 : ‖1 - t‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, htn]; norm_num
      linarith
    · intro hl
      simp only [hl, ↓reduceIte] at hmin
      simp only [Complex.sub_re, Complex.one_re]
      linarith

/-- `|N⁻¹ Σ_{i,j} X_{(b,j),(0,i)} Y_{(0,i),(b,j)}| ≤ (U_b + V_b)/2` when every product is bounded
by the mean of `|M_{(b,j),(0,i)}|²` and `|M_{(0,i),(b,j)}|²`. -/
private lemma MS_amgm (D N : ℕ) [NeZero D] (X Y M : Matrix (Idx D N) (Idx D N) ℂ) (b : Fin D)
    (h : ∀ i j : Fin N, ‖X (b, j) (0, i) * Y (0, i) (b, j)‖ ≤
      (‖M (b, j) (0, i)‖ ^ 2 + ‖M (0, i) (b, j)‖ ^ 2) / 2) :
    ‖(N : ℂ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, X (b, j) (0, i) * Y (0, i) (b, j)‖ ≤
      ((N : ℝ)⁻¹ * (∑ i : Fin N, ∑ j : Fin N, ‖M (b, j) (0, i)‖ ^ 2) +
        (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, ‖M (0, i) (b, j)‖ ^ 2) / 2 := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ‖∑ i : Fin N, ∑ j : Fin N, X (b, j) (0, i) * Y (0, i) (b, j)‖ ≤
      ∑ i : Fin N, ∑ j : Fin N, (‖M (b, j) (0, i)‖ ^ 2 + ‖M (0, i) (b, j)‖ ^ 2) / 2 :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => h i j))
  have h2 : ∑ i : Fin N, ∑ j : Fin N, (‖M (b, j) (0, i)‖ ^ 2 + ‖M (0, i) (b, j)‖ ^ 2) / 2 =
      ((∑ i : Fin N, ∑ j : Fin N, ‖M (b, j) (0, i)‖ ^ 2) +
        ∑ i : Fin N, ∑ j : Fin N, ‖M (0, i) (b, j)‖ ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  rw [h2] at h1
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  calc (N : ℝ)⁻¹ * ‖∑ i : Fin N, ∑ j : Fin N, X (b, j) (0, i) * Y (0, i) (b, j)‖
      ≤ (N : ℝ)⁻¹ * (((∑ i : Fin N, ∑ j : Fin N, ‖M (b, j) (0, i)‖ ^ 2) +
        ∑ i : Fin N, ∑ j : Fin N, ‖M (0, i) (b, j)‖ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h1 hN
    _ = _ := by ring

/-- `Σ_b |M̂_{0b}(z₁, z₂)| ≤ d₁ = Im m / (Im m + η)` for `z₁, z₂ ∈ {z, z̄}`. -/
private lemma MS_rowabs (D : ℕ) (hD : 2 ≤ D) [NeZero D] (N : ℕ) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) :
    ∑ b : Fin D, ‖Mhat (lam D N A) z₁ z₂ 0 b‖ ≤
      (mSol (lam D N A) z).im / ((mSol (lam D N A) z).im + z.im) := by
  have : Nonempty (Idx D N) := ⟨(0, ⟨0, hN⟩)⟩
  have hD0 : D ≠ 0 := by omega
  have hΛ := lam_isHermitian D N A
  obtain ⟨hnorm, -, hE, -⟩ := MS_dfacts D hD N hN A z hz
  have hconj := (mExt_conj (lam D N A) hΛ z hz.ne').2
  set M := MExt (lam D N A) z with hMdef
  set d : ℝ := (mSol (lam D N A) z).im / ((mSol (lam D N A) z).im + z.im)
  set U : Fin D → ℝ := fun b => (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, ‖M (b, j) (0, i)‖ ^ 2
  set V : Fin D → ℝ := fun b => (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, ‖M (0, i) (b, j)‖ ^ 2
  have hU0 : ∀ b, 0 ≤ U b := fun b => by simp only [U]; positivity
  have hV0 : ∀ b, 0 ≤ V b := fun b => by simp only [V]; positivity
  have hU : ∀ b, Mhat (lam D N A) z (star z) 0 b = (U b : ℂ) := by
    intro b
    rw [MS_Mhat_apply D N hD0, hconj]
    simp only [U, ← hMdef, Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj',
      Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum,
      Complex.ofReal_pow]
  have hV : ∀ b, Mhat (lam D N A) (star z) z 0 b = (V b : ℂ) := by
    intro b
    rw [MS_Mhat_apply D N hD0, hconj]
    simp only [V, ← hMdef, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul',
      Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum,
      Complex.ofReal_pow]
  have hsU : ∑ b, U b = d := by
    have h := MS_rowsum D N (lam D N A) z (star z) 0
    rw [hconj, MS_ntr_comm, ← Matrix.mul_assoc, hnorm, hE 0] at h
    simp only [hU] at h
    exact_mod_cast h
  have hsV : ∑ b, V b = d := by
    have h := MS_rowsum D N (lam D N A) (star z) z 0
    rw [hconj, MS_ntr_comm, ← Matrix.mul_assoc, hE 0] at h
    simp only [hV] at h
    exact_mod_cast h
  have hamgm : ∀ x y : ℂ, ‖x * y‖ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
    intro x y
    rw [norm_mul]
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hmid : (∀ b, ‖Mhat (lam D N A) z₁ z₂ 0 b‖ ≤ U b) ∨
      (∀ b, ‖Mhat (lam D N A) z₁ z₂ 0 b‖ ≤ V b) ∨
      ∀ b, ‖Mhat (lam D N A) z₁ z₂ 0 b‖ ≤ (U b + V b) / 2 := by
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
    · right; right; intro b
      rw [MS_Mhat_apply D N hD0]
      exact MS_amgm D N M M M b fun i j => hamgm _ _
    · left; intro b
      rw [hU, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hU0 b)]
    · right; left; intro b
      rw [hV, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hV0 b)]
    · right; right; intro b
      rw [MS_Mhat_apply D N hD0, hconj]
      refine MS_amgm D N Mᴴ Mᴴ M b fun i j => ?_
      simp only [Matrix.conjTranspose_apply]
      rw [mul_comm]
      have := hamgm (M (b, j) (0, i)) (M (0, i) (b, j))
      simpa [norm_star] using this
  rcases hmid with h | h | h
  · exact (Finset.sum_le_sum fun b _ => h b).trans hsU.le
  · exact (Finset.sum_le_sum fun b _ => h b).trans hsV.le
  · refine (Finset.sum_le_sum fun b _ => h b).trans (le_of_eq ?_)
    rw [← Finset.sum_div, Finset.sum_add_distrib, hsU, hsV]
    ring

/-- The expansion of `M̂_{0c}`, `c ≠ 0`, behind (A.27) [wh_M_expansion]: with `P = E_0`, `Q = E_c`,
`(w₁ w₂)² tr(M₁ P M₂ Q) = tr(P Λ (Λ M₂ Q M₁ Λ - Λ M₂ Q - Q M₁ Λ + Q) Λ P)`. -/
private lemma MS_expand (D N : ℕ) [NeZero D] (Λ M₁ M₂ : Matrix (Idx D N) (Idx D N) ℂ)
    (w₁ w₂ : ℂ) (h₁ : w₁ • M₁ = M₁ * Λ - 1) (h₂ : w₂ • M₂ = Λ * M₂ - 1) (c : Fin D)
    (hc : c ≠ 0) :
    (w₁ * w₂) ^ 2 * (M₁ * Ea D N 0 * M₂ * Ea D N c).trace =
      (Ea D N 0 * Λ * (Λ * M₂ * Ea D N c * M₁ * Λ - Λ * M₂ * Ea D N c - Ea D N c * M₁ * Λ +
        Ea D N c) * (Λ * Ea D N 0)).trace := by
  set P := Ea D N 0
  set Q := Ea D N c
  have hPP : P * P = P := MS_Ea_sq D N 0
  have hQQ : Q * Q = Q := MS_Ea_sq D N c
  have hQP : Q * P = 0 := MS_Ea_mul_ne D N c 0 hc
  have hPQ : P * Q = 0 := MS_Ea_mul_ne D N 0 c (Ne.symm hc)
  have t1 : (M₁ * P * M₂ * Q).trace = ((Q * M₁ * P) * (P * M₂ * Q)).trace := by
    have e1 : (Q * M₁ * P) * (P * M₂ * Q) = Q * (M₁ * P * M₂ * Q) := by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc P P, hPP]
    rw [e1, Matrix.trace_mul_comm Q, Matrix.mul_assoc (M₁ * P * M₂) Q Q, hQQ]
  have t2 : w₁ • (Q * M₁ * P) = Q * M₁ * Λ * P := by
    rw [Matrix.mul_assoc Q M₁ P, ← Matrix.mul_smul, ← Matrix.smul_mul, h₁, Matrix.sub_mul,
      Matrix.one_mul, Matrix.mul_sub, hQP, sub_zero]
    simp only [Matrix.mul_assoc]
  have t3 : w₂ • (P * M₂ * Q) = P * Λ * M₂ * Q := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, h₂, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      hPQ, sub_zero]
    simp only [Matrix.mul_assoc]
  have t4 : (w₁ * w₂) • (M₂ * Q * M₁) = Λ * M₂ * Q * M₁ * Λ - Λ * M₂ * Q - Q * M₁ * Λ + Q := by
    have : (w₂ • M₂) * Q * (w₁ • M₁) = (w₁ * w₂) • (M₂ * Q * M₁) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← this, h₁, h₂]
    noncomm_ring
  calc (w₁ * w₂) ^ 2 * (M₁ * P * M₂ * Q).trace
      = (w₁ * w₂) * ((w₁ • (Q * M₁ * P)) * (w₂ • (P * M₂ * Q))).trace := by
        rw [t1, smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul]; ring
    _ = (w₁ * w₂) * ((Q * M₁ * Λ * P) * (P * Λ * M₂ * Q)).trace := by rw [t2, t3]
    _ = (w₁ * w₂) * (P * Λ * (M₂ * Q * M₁) * (Λ * P)).trace := by
        have e : (P * Λ * M₂ * Q) * (Q * M₁ * Λ * P) = P * Λ * (M₂ * Q * M₁) * (Λ * P) := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Q Q, hQQ]
        rw [Matrix.trace_mul_comm, e]
    _ = (P * Λ * ((w₁ * w₂) • (M₂ * Q * M₁)) * (Λ * P)).trace := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    _ = _ := by rw [t4]

/-- The error of the expansion: `|(w₁w₂)² tr(M₁ E_0 M₂ E_c) - tr(E_0 Λ E_c Λ E_0)| ≤
3 ‖Λ‖ ‖Λ E_0‖²_HS` for `c ≠ 0`, `‖Λ‖ ≤ 1/10` and `‖M_i‖ ≤ 5/4`. -/
private lemma MS_expand_bd (D N : ℕ) [NeZero D] (Λ M₁ M₂ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (w₁ w₂ : ℂ) (h₁ : w₁ • M₁ = M₁ * Λ - 1)
    (h₂ : w₂ • M₂ = Λ * M₂ - 1) (hM₁ : opNorm M₁ ≤ 5 / 4) (hM₂ : opNorm M₂ ≤ 5 / 4)
    (c : Fin D) (hc : c ≠ 0) :
    ‖(w₁ * w₂) ^ 2 * (M₁ * Ea D N 0 * M₂ * Ea D N c).trace -
        ((Λ * Ea D N 0)ᴴ * Ea D N c * (Λ * Ea D N 0)).trace‖ ≤
      3 * opNorm Λ * MS_S (Λ * Ea D N 0) := by
  rw [MS_expand D N Λ M₁ M₂ w₁ w₂ h₁ h₂ c hc]
  have hS : (Λ * Ea D N 0)ᴴ = Ea D N 0 * Λ := by
    rw [conjTranspose_mul, MS_Ea_conj, hΛ.eq]
  set S := Λ * Ea D N 0
  set Q := Ea D N c
  set Y := Λ * M₂ * Q * M₁ * Λ - Λ * M₂ * Q - Q * M₁ * Λ
  have e : (Ea D N 0 * Λ * (Λ * M₂ * Q * M₁ * Λ - Λ * M₂ * Q - Q * M₁ * Λ + Q) * S).trace -
      (Sᴴ * Q * S).trace = (Sᴴ * Y * S).trace := by
    have e2 : Ea D N 0 * Λ * (Λ * M₂ * Q * M₁ * Λ - Λ * M₂ * Q - Q * M₁ * Λ + Q) * S -
        Ea D N 0 * Λ * Q * S = Ea D N 0 * Λ * Y * S := by
      simp only [Y]
      noncomm_ring
    rw [hS, ← Matrix.trace_sub, e2]
  rw [e]
  refine (MS_tr_sandwich S Y).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (MS_S_nonneg S)
  have hl0 := MS_op_nonneg Λ
  have hQ := MS_Ea_norm D N c
  have hQ0 := MS_op_nonneg Q
  have hM₁0 := MS_op_nonneg M₁
  have hM₂0 := MS_op_nonneg M₂
  have b1 : opNorm (Λ * M₂ * Q * M₁ * Λ) ≤ opNorm Λ * (5 / 4) * 1 * (5 / 4) * opNorm Λ := by
    refine (MS_op_mul _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hl0
    refine (MS_op_mul _ _).trans ?_
    refine mul_le_mul (?_) hM₁ hM₁0 (by positivity)
    refine (MS_op_mul _ _).trans ?_
    refine mul_le_mul (?_) hQ hQ0 (by positivity)
    refine (MS_op_mul _ _).trans ?_
    exact mul_le_mul_of_nonneg_left hM₂ hl0
  have b2 : opNorm (Λ * M₂ * Q) ≤ opNorm Λ * (5 / 4) * 1 := by
    refine (MS_op_mul _ _).trans ?_
    refine mul_le_mul (?_) hQ hQ0 (by positivity)
    refine (MS_op_mul _ _).trans ?_
    exact mul_le_mul_of_nonneg_left hM₂ hl0
  have b3 : opNorm (Q * M₁ * Λ) ≤ 1 * (5 / 4) * opNorm Λ := by
    refine (MS_op_mul _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hl0
    refine (MS_op_mul _ _).trans ?_
    exact mul_le_mul hQ hM₁ hM₁0 zero_le_one
  have hsub : ∀ X Z : Matrix (Idx D N) (Idx D N) ℂ, opNorm (X - Z) ≤ opNorm X + opNorm Z :=
    fun X Z => by simpa only [MS_op_eq] using norm_sub_le X Z
  calc opNorm Y ≤ opNorm (Λ * M₂ * Q * M₁ * Λ) + opNorm (Λ * M₂ * Q) + opNorm (Q * M₁ * Λ) := by
        refine (hsub _ _).trans ?_
        linarith [hsub (Λ * M₂ * Q * M₁ * Λ) (Λ * M₂ * Q)]
    _ ≤ 3 * opNorm Λ := by nlinarith

/-- The spectrum of `M̂(z₁, z₂)`, `z₁, z₂ ∈ {z, z̄}`, `Im z > 0`, `‖Λ‖ ≤ 1/10`: `|λ̂_l| ≤ d₁`,
`λ̂_0 = ⟨M(z₁) M(z₂)⟩`, and `λ̂_0 - λ̂_l = X (w₁w₂)⁻² g_l + O(D² ‖Λ‖ X)`,
`X = ‖A‖²_HS / N`. -/
private lemma MS_spec (D : ℕ) (hD : 2 ≤ D) [NeZero D] (N : ℕ) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im)
    (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) :
    (∀ l, Mhat (lam D N A) z₁ z₂ *ᵥ fourierVec D l =
      circEig (Mhat (lam D N A) z₁ z₂) l • fourierVec D l) ∧
    (∀ l, ‖circEig (Mhat (lam D N A) z₁ z₂) l‖ ≤
      (mSol (lam D N A) z).im / ((mSol (lam D N A) z).im + z.im)) ∧
    circEig (Mhat (lam D N A) z₁ z₂) 0 = ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₂) ∧
    ∀ l, ‖circEig (Mhat (lam D N A) z₁ z₂) 0 - circEig (Mhat (lam D N A) z₁ z₂) l -
        ((MS_S A / N : ℝ) : ℂ) *
          (((z₁ + mExt (lam D N A) z₁) * (z₂ + mExt (lam D N A) z₂)) ^ 2)⁻¹ * MS_g D l‖ ≤
      24 * D ^ 2 * opNorm (lam D N A) * (MS_S A / N) := by
  have : Nonempty (Idx D N) := ⟨(0, ⟨0, hN⟩)⟩
  have hD0 : D ≠ 0 := by omega
  have hΛ := lam_isHermitian D N A
  have him : ∀ z' : ℂ, (z' = z ∨ z' = star z) → z'.im ≠ 0 := by
    rintro z' (rfl | rfl)
    · exact hz.ne'
    · simp only [Complex.star_def, Complex.conj_im]; linarith
  have hev := Mhat_eigvec D hD N A z₁ z₂ (him z₁ h₁) (him z₂ h₂)
  have hrow : ∀ l, circEig (Mhat (lam D N A) z₁ z₂) l =
      ∑ b : Fin D, Mhat (lam D N A) z₁ z₂ 0 b * MS_zeta D ^ ((l : ℕ) * (b : ℕ)) :=
    fun l => MS_circEig_row D _ l (hev l)
  refine ⟨hev, ?_, MS_circEig_zero_Mhat D N _ z₁ z₂, ?_⟩
  · intro l
    rw [hrow l]
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (le_of_eq ?_) (MS_rowabs D hD N hN A z hz z₁ z₂ h₁ h₂)
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [norm_mul, MS_norm_zeta_pow D hD0, mul_one]
  · intro l
    obtain ⟨r1, -, n1, w1, -⟩ := MS_res hΛ hℓ hz h₁
    obtain ⟨-, r2, n2, w2, -⟩ := MS_res hΛ hℓ hz h₂
    set M₁ := MExt (lam D N A) z₁
    set M₂ := MExt (lam D N A) z₂
    set w₁ := z₁ + mExt (lam D N A) z₁
    set w₂ := z₂ + mExt (lam D N A) z₂
    set ℓ := opNorm (lam D N A)
    set X : ℝ := MS_S A / N
    set R : ℂ := ((w₁ * w₂) ^ 2)⁻¹
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hSA := MS_S_nonneg A
    have hX0 : 0 ≤ X := by positivity
    have hl0 : 0 ≤ ℓ := MS_op_nonneg _
    have hW : (0.9 : ℝ) ^ 2 ≤ ‖w₁ * w₂‖ := by
      rw [norm_mul]; nlinarith
    have hR : ‖R‖ ≤ 2 := by
      simp only [R, norm_inv, norm_pow]
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith
    have hchi : ∀ c : Fin D, 0 ≤ MS_chi D c ∧ MS_chi D c ≤ 2 := by
      intro c; unfold MS_chi; split_ifs <;> norm_num
    have hSS : MS_S (lam D N A * Ea D N 0) ≤ 2 * D * MS_S A := by
      rw [MS_S_lamE]
      refine mul_le_mul_of_nonneg_right ?_ hSA
      calc ∑ c : Fin D, MS_chi D c ≤ ∑ _c : Fin D, (2 : ℝ) :=
            Finset.sum_le_sum fun c _ => (hchi c).2
        _ = 2 * D := by simp [mul_comm]
    -- each off-diagonal entry
    have hent : ∀ c : Fin D, c ≠ 0 →
        ‖Mhat (lam D N A) z₁ z₂ 0 c - (X : ℂ) * R * (MS_chi D c : ℂ)‖ ≤ 12 * D * ℓ * X := by
      intro c hc
      have hb := MS_expand_bd D N (lam D N A) M₁ M₂ hΛ hℓ w₁ w₂ r1 r2 n1 n2 c hc
      rw [MS_tr_blk] at hb
      have hM : Mhat (lam D N A) z₁ z₂ 0 c = (N : ℂ)⁻¹ * (M₁ * Ea D N 0 * M₂ * Ea D N c).trace := by
        unfold Mhat; rw [MS_D_ntr D N hD0]
      have hw0 : (w₁ * w₂) ^ 2 ≠ 0 := by
        refine pow_ne_zero 2 fun h => ?_
        rw [h, norm_zero] at hW; norm_num at hW
      have hw₁ : w₁ ≠ 0 := fun h => by rw [h, norm_zero] at w1; norm_num at w1
      have hw₂ : w₂ ≠ 0 := fun h => by rw [h, norm_zero] at w2; norm_num at w2
      have e : Mhat (lam D N A) z₁ z₂ 0 c - (X : ℂ) * R * (MS_chi D c : ℂ) =
          (N : ℂ)⁻¹ * R * ((w₁ * w₂) ^ 2 * (M₁ * Ea D N 0 * M₂ * Ea D N c).trace -
            ((MS_chi D c * MS_S A : ℝ) : ℂ)) := by
        rw [hM]
        simp only [X, R]
        push_cast
        field_simp
      rw [e, norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
      calc (N : ℝ)⁻¹ * ‖R‖ * ‖(w₁ * w₂) ^ 2 * (M₁ * Ea D N 0 * M₂ * Ea D N c).trace -
            ((MS_chi D c * MS_S A : ℝ) : ℂ)‖
          ≤ (N : ℝ)⁻¹ * 2 * (3 * ℓ * (2 * D * MS_S A)) := by
            gcongr
            exact hb.trans (mul_le_mul_of_nonneg_left hSS (by positivity))
        _ = 12 * D * ℓ * X := by simp only [X]; field_simp; ring
    -- the sum over `c`
    have hdiff : circEig (Mhat (lam D N A) z₁ z₂) 0 - circEig (Mhat (lam D N A) z₁ z₂) l -
        (X : ℂ) * R * MS_g D l = ∑ c : Fin D, (Mhat (lam D N A) z₁ z₂ 0 c -
          (X : ℂ) * R * (MS_chi D c : ℂ)) * (1 - MS_zeta D ^ ((l : ℕ) * (c : ℕ))) := by
      rw [hrow 0, hrow l]
      simp only [MS_g, Fin.val_zero, zero_mul, pow_zero, mul_one, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hdiff]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c : Fin D, ‖(Mhat (lam D N A) z₁ z₂ 0 c - (X : ℂ) * R * (MS_chi D c : ℂ)) *
          (1 - MS_zeta D ^ ((l : ℕ) * (c : ℕ)))‖ ≤ ∑ _c : Fin D, 24 * D * ℓ * X := by
          refine Finset.sum_le_sum fun c _ => ?_
          by_cases hc : c = 0
          · subst hc
            rw [Fin.val_zero, mul_zero, pow_zero, sub_self, mul_zero, norm_zero]
            positivity
          · rw [norm_mul]
            have h2 : ‖1 - MS_zeta D ^ ((l : ℕ) * (c : ℕ))‖ ≤ 2 := by
              refine (norm_sub_le _ _).trans ?_
              rw [norm_one, MS_norm_zeta_pow D hD0]; norm_num
            calc _ ≤ (12 * D * ℓ * X) * 2 :=
                  mul_le_mul (hent c hc) h2 (norm_nonneg _) (by positivity)
              _ = 24 * D * ℓ * X := by ring
      _ = 24 * D ^ 2 * ℓ * X := by simp; ring

end MS_Spec

/-! ### Scalar bounds from (A.1), (A.2), (A.3) and (A.12) -/

section MS_Scalar

set_option maxHeartbeats 1000000 in
/-- For `Λ = lam D N A`, `‖Λ‖ ≤ 1/10`, `|z| ≤ τ⁻¹`, `η > 0`, and `s = κ + η`: `η ≲ Im m`,
`√s ≲ |1 - ⟨M²⟩| ≲ √s`, `η / Im m ≲ √s`, `Im m ≲ √s` and `√s ≲ 1`, by (A.1)
[square_root_density], (A.2) [edge_close_to_edge_sc], (A.3) [equation_z_im_m] and (A.12)
[de_ir_0]. -/
private lemma MS_scalar (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : ℕ), 2 ≤ D → ∀ (N : ℕ), 1 ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ,
      opNorm (lam D N A) ≤ 1 / 10 → ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
      z.im ≤ C * (mSol (lam D N A) z).im ∧
      C⁻¹ * Real.sqrt (kappa (lam D N A) z.re + z.im) ≤
        ‖1 - ntr (MExt (lam D N A) z * MExt (lam D N A) z)‖ ∧
      ‖1 - ntr (MExt (lam D N A) z * MExt (lam D N A) z)‖ ≤
        C * Real.sqrt (kappa (lam D N A) z.re + z.im) ∧
      z.im / (mSol (lam D N A) z).im ≤ C * Real.sqrt (kappa (lam D N A) z.re + z.im) ∧
      (mSol (lam D N A) z).im ≤ C * Real.sqrt (kappa (lam D N A) z.re + z.im) ∧
      Real.sqrt (kappa (lam D N A) z.re + z.im) ≤ C := by
  obtain ⟨C₁, hC₁, hsrd⟩ := square_root_density τ hτ
  obtain ⟨C₂, hC₂, hde⟩ := de_ir_0 τ hτ
  obtain ⟨C₃, hC₃, hedge⟩ := edge_close_to_edge_sc
  have hτ' : 0 < τ⁻¹ := inv_pos.2 hτ
  set Q : ℝ := Real.sqrt (2 + C₃ / 10 + 2 * τ⁻¹) with hQ
  set r : ℝ := Real.sqrt τ⁻¹ with hr
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hC1' : 1 ≤ 1 + C₁ * Q + C₂ * C₁ + Q + 5 * C₁ + 4 * r := by
    nlinarith [mul_nonneg hC₁.le hQ0, mul_pos hC₂ hC₁]
  refine ⟨1 + C₁ * Q + C₂ * C₁ + Q + 5 * C₁ + 4 * r, hC1', ?_⟩
  intro D hD N hN A hℓ z hzn hz
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  have htr := MS_ntr_lam D N A
  set C := 1 + C₁ * Q + C₂ * C₁ + Q + 5 * C₁ + 4 * r with hC
  have hC1Q := mul_nonneg hC₁.le hQ0
  have hC21 := mul_pos hC₂ hC₁
  have hCpos : 0 < C := by linarith
  have hCa : C₂ * C₁ ≤ C := by rw [hC]; linarith
  have hCb : C₁ + Q ≤ C := by rw [hC]; linarith
  have hCc : C₁ * Q ≤ C := by rw [hC]; linarith
  have hCd : 5 * C₁ + 4 * r ≤ C := by rw [hC]; linarith
  have hCe : C₁ ≤ C := by rw [hC]; linarith
  have hCf : Q ≤ C := by rw [hC]; linarith
  obtain ⟨hm, hM⟩ := MS_pos (lam D N A) hz
  rw [hM]
  obtain ⟨-, hS⟩ := hsrd (Idx D N) (lam D N A) hΛ hℓ
  have hS' := hS z hzn hz
  obtain ⟨hy, -, -⟩ := mSol_spec (lam D N A) hΛ z hz
  obtain ⟨-, -, hMn⟩ := mSol_apriori (lam D N A) hΛ hℓ z hz
  obtain ⟨h1, h2⟩ := equation_z_im_m (lam D N A) hΛ z hz
  have hdf := MS_dfacts D hD N hN A z hz
  rw [hM] at hdf
  obtain ⟨-, -, -, hRe⟩ := hdf
  set Λ := lam D N A
  set M := MSol Λ z
  set y := (mSol Λ z).im
  set η := z.im
  set κ := kappa Λ z.re
  have hκ : 0 ≤ κ := le_min (abs_nonneg _) (abs_nonneg _)
  set s := κ + η
  set q := Real.sqrt s
  have hs : 0 < s := by positivity
  have hq : 0 < q := Real.sqrt_pos.2 hs
  have hqq : q * q = s := Real.mul_self_sqrt hs.le
  have hηs : η ≤ q * q := by rw [hqq]; linarith
  -- `s ≤ Q²`
  have hηn : η ≤ τ⁻¹ := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hzn)
  have hEn : |z.re| ≤ τ⁻¹ := (Complex.abs_re_le_norm z).trans hzn
  have hE := hedge (Idx D N) Λ hΛ hℓ
  have hκb : κ ≤ 2 + C₃ / 10 + τ⁻¹ := by
    have h1 : κ ≤ |Eplus Λ - z.re| := min_le_left _ _
    have h2 : |Eplus Λ - z.re| ≤ |Eplus Λ| + |z.re| := by
      have := abs_sub (Eplus Λ) z.re; linarith
    have h3 : |Eplus Λ| ≤ 2 + |2 - Eplus Λ| := by
      have := abs_sub_abs_le_abs_sub (Eplus Λ) 2
      rw [abs_two, abs_sub_comm] at this
      linarith
    have h4 : |2 - Eplus Λ| ≤ C₃ / 10 := by
      have := abs_nonneg (2 + Eminus Λ)
      nlinarith [MS_op_nonneg Λ]
    linarith
  have hqQ : q ≤ Q := Real.sqrt_le_sqrt (by linarith)
  have hηr : η ≤ r * q := by
    have h1 : η = Real.sqrt η * Real.sqrt η := (Real.mul_self_sqrt hz.le).symm
    have h2 : Real.sqrt η ≤ r := Real.sqrt_le_sqrt hηn
    have h3 : Real.sqrt η ≤ q := Real.sqrt_le_sqrt (by linarith)
    rw [h1]
    exact mul_le_mul h2 h3 (Real.sqrt_nonneg _) hr0
  -- the two regimes of (A.1)
  have hηy : η / y ≤ C₁ * q ∧ y ≤ C₁ * q := by
    by_cases hin : z.re ∈ Set.Icc (Eminus Λ) (Eplus Λ)
    · obtain ⟨a1, a2⟩ := hS'.1 hin
      refine ⟨?_, a2⟩
      rw [div_le_iff₀ hy]
      have : q * q ≤ C₁ * q * y := by
        have := mul_le_mul_of_nonneg_left a1 (mul_nonneg hC₁.le hq.le)
        calc q * q = C₁ * q * (C₁⁻¹ * q) := by field_simp
          _ ≤ C₁ * q * y := this
      linarith
    · obtain ⟨a1, a2⟩ := hS'.2 hin
      have hηq : η / q ≤ q := by rw [div_le_iff₀ hq]; linarith
      refine ⟨?_, a2.trans (mul_le_mul_of_nonneg_left hηq hC₁.le)⟩
      rw [div_le_iff₀ hy]
      have := mul_le_mul_of_nonneg_left a1 (mul_nonneg hC₁.le hq.le)
      calc η = C₁ * q * (C₁⁻¹ * (η / q)) := by field_simp
        _ ≤ C₁ * q * y := this
  obtain ⟨hηy1, hy1⟩ := hηy
  have hd1 : 1 - y / (y + η) = η / (y + η) := by field_simp; ring
  have hd2 : η / (y + η) ≤ η / y := div_le_div_of_nonneg_left hz.le hy (by linarith)
  -- `|⟨M M^*⟩ - ⟨M²⟩| ≤ 4 (η + Im m)`
  have hdiff : ‖ntr (M * Mᴴ) - ntr (M * M)‖ ≤ 4 * (η + y) := by
    have e : M * Mᴴ - M * M = -((2 * Complex.I * ((η + y : ℝ) : ℂ)) • (M * (M * Mᴴ))) := by
      rw [← Matrix.mul_smul, ← h2]; noncomm_ring
    rw [← MS_ntr_sub, e]
    have hneg : ∀ X : Matrix (Idx D N) (Idx D N) ℂ, ntr (-X) = -ntr X := fun X => by
      simp [ntr, Matrix.trace_neg]
    rw [hneg, norm_neg, MS_ntr_smul, norm_mul]
    have hc : ‖2 * Complex.I * ((η + y : ℝ) : ℂ)‖ = 2 * (η + y) := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      norm_num
    rw [hc]
    have hM54 : opNorm M ≤ 5 / 4 := by
      refine hMn.le.trans ?_
      rw [inv_le_comm₀ (by linarith [MS_op_nonneg Λ]) (by norm_num)]
      linarith [MS_op_nonneg Λ]
    have hn : ‖ntr (M * (M * Mᴴ))‖ ≤ 2 := by
      refine (MS_ntr_le _).trans ?_
      refine (MS_op_mul _ _).trans ?_
      have := MS_op_mul M Mᴴ
      rw [MS_op_conj] at this
      have h0 := MS_op_nonneg M
      nlinarith
    nlinarith
  have hup : ‖1 - ntr (M * M)‖ ≤ η / y + 4 * (η + y) := by
    have : 1 - ntr (M * M) = ((1 - y / (y + η) : ℝ) : ℂ) + (ntr (M * Mᴴ) - ntr (M * M)) := by
      rw [h1]; push_cast; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, hd1, abs_of_nonneg (by positivity)]
    linarith
  have hlow_re : η / (y + η) ≤ ‖1 - ntr (M * M)‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have h0 := norm_nonneg (1 - ntr (M * M))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (div_le_iff₀ hy).1 (hηy1.trans (mul_le_mul_of_nonneg_left hqQ hC₁.le))
    calc η ≤ C₁ * Q * y := this
      _ ≤ C * y := mul_le_mul_of_nonneg_right hCc hy.le
  · rw [inv_mul_le_iff₀ hCpos]
    by_cases hin : z.re ∈ Set.Icc (Eminus Λ) (Eplus Λ)
    · obtain ⟨a1, -⟩ := hS'.1 hin
      obtain ⟨b1, -⟩ := hde (Idx D N) Λ hΛ hℓ htr z hzn hz hin
      rw [sq] at b1
      have e1 : q ≤ C₁ * y := by
        have := mul_le_mul_of_nonneg_left a1 hC₁.le
        rwa [← mul_assoc, mul_inv_cancel₀ hC₁.ne', one_mul] at this
      have e2 : y ≤ C₂ * ‖1 - ntr (M * M)‖ := by
        have := mul_le_mul_of_nonneg_left b1 hC₂.le
        rwa [← mul_assoc, mul_inv_cancel₀ hC₂.ne', one_mul] at this
      calc q ≤ C₁ * y := e1
        _ ≤ C₁ * (C₂ * ‖1 - ntr (M * M)‖) := mul_le_mul_of_nonneg_left e2 hC₁.le
        _ = C₂ * C₁ * ‖1 - ntr (M * M)‖ := by ring
        _ ≤ C * ‖1 - ntr (M * M)‖ := mul_le_mul_of_nonneg_right hCa h0
    · obtain ⟨-, a2⟩ := hS'.2 hin
      have hyq : y * q ≤ C₁ * η := by
        have := mul_le_mul_of_nonneg_right a2 hq.le
        calc y * q ≤ C₁ * (η / q) * q := this
          _ = C₁ * η := by field_simp
      have : q / (C₁ + q) ≤ η / (y + η) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc q * (y + η) = y * q + q * η := by ring
          _ ≤ C₁ * η + q * η := by linarith
          _ = η * (C₁ + q) := by ring
      have h3 : q ≤ (C₁ + q) * ‖1 - ntr (M * M)‖ := by
        have h4 := this.trans hlow_re
        rw [div_le_iff₀ (by positivity)] at h4
        linarith
      calc q ≤ (C₁ + q) * ‖1 - ntr (M * M)‖ := h3
        _ ≤ (C₁ + Q) * ‖1 - ntr (M * M)‖ := by gcongr
        _ ≤ C * ‖1 - ntr (M * M)‖ := mul_le_mul_of_nonneg_right hCb h0
  · calc ‖1 - ntr (M * M)‖ ≤ η / y + 4 * (η + y) := hup
      _ ≤ C₁ * q + 4 * (r * q + C₁ * q) := by linarith
      _ = (5 * C₁ + 4 * r) * q := by ring
      _ ≤ C * q := mul_le_mul_of_nonneg_right hCd hq.le
  · exact hηy1.trans (mul_le_mul_of_nonneg_right hCe hq.le)
  · exact hy1.trans (mul_le_mul_of_nonneg_right hCe hq.le)
  · exact hqQ.trans hCf

end MS_Scalar

/-! ### Auxiliary estimates -/

section MS_Aux

open scoped Matrix.Norms.L2Operator

/-- `N^{-δ} ≤ θ` for all large `N`. -/
private lemma MS_N0 (δ θ : ℝ) (hδ : 0 < δ) (hθ : 0 < θ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → (N : ℝ) ^ (-δ) ≤ θ := by
  have h := (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (h.eventually (Iio_mem_nhds hθ))
  exact ⟨max N₁ 1, le_max_right _ _, fun N hN => (hN₁ N (le_of_max_le_left hN)).le⟩

/-- `‖Λ‖ ≤ 2D²θ`, `0 ≤ X ≤ θ²` for `X = ‖A‖²_HS / N` when `‖A‖ ≤ θ`. -/
private lemma MS_small (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) (θ : ℝ)
    (hA : opNorm A ≤ θ) :
    opNorm (lam D N A) ≤ 2 * D ^ 2 * θ ∧ 0 ≤ MS_S A / N ∧ MS_S A / N ≤ θ ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hA0 := MS_op_nonneg A
  refine ⟨(MS_opNorm_lam D N hN A).trans (by gcongr), by have := MS_S_nonneg A; positivity, ?_⟩
  rw [div_le_iff₀ hN0]
  have := MS_S_le_card A
  rw [Fintype.card_fin] at this
  have h2 := pow_le_pow_left₀ hA0 hA 2
  nlinarith

/-- `|⟨M₁²⟩ - w₁⁻²| ≤ 4‖Λ‖` from `w₁ M₁ = M₁ Λ - 1`, `‖M₁‖ ≤ 5/4`, `|w₁| > 9/10`. -/
private lemma MS_w2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ M : Matrix ι ι ℂ)
    (w : ℂ) (hℓ : opNorm Λ ≤ 1 / 10) (h : w • M = M * Λ - 1) (hM : opNorm M ≤ 5 / 4)
    (hw : 9 / 10 < ‖w‖) : ‖ntr (M * M) - (w ^ 2)⁻¹‖ ≤ 4 * opNorm Λ := by
  have hw0 : w ≠ 0 := fun e => by rw [e, norm_zero] at hw; norm_num at hw
  have hl0 := MS_op_nonneg Λ
  have hM0 := MS_op_nonneg M
  have e : (w • M) * (w • M) = M * Λ * (M * Λ) - (2 : ℂ) • (M * Λ) + 1 := by
    rw [h, two_smul]; noncomm_ring
  rw [smul_mul_smul_comm] at e
  have e2 := congrArg ntr e
  rw [MS_ntr_smul, MS_ntr_add, MS_ntr_sub, MS_ntr_smul, MS_ntr_one] at e2
  have e3 : ntr (M * M) - (w ^ 2)⁻¹ =
      (w ^ 2)⁻¹ * (ntr (M * Λ * (M * Λ)) - 2 * ntr (M * Λ)) := by
    field_simp
    linear_combination e2
  rw [e3, norm_mul, norm_inv, norm_pow]
  have b1 : ‖ntr (M * Λ * (M * Λ))‖ ≤ (5 / 4 * opNorm Λ) * (5 / 4 * opNorm Λ) := by
    refine (MS_ntr_le _).trans ((MS_op_mul _ _).trans ?_)
    have := MS_op_mul M Λ
    have h1 : opNorm (M * Λ) ≤ 5 / 4 * opNorm Λ := this.trans (by nlinarith)
    exact mul_le_mul h1 h1 (MS_op_nonneg _) (by positivity)
  have b2 : ‖ntr (M * Λ)‖ ≤ 5 / 4 * opNorm Λ :=
    (MS_ntr_le _).trans ((MS_op_mul _ _).trans (by nlinarith))
  have b3 : ‖ntr (M * Λ * (M * Λ)) - 2 * ntr (M * Λ)‖ ≤ 3 * opNorm Λ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    norm_num
    nlinarith
  have hw2 : (81 / 100 : ℝ) ≤ ‖w‖ ^ 2 := by nlinarith
  calc (‖w‖ ^ 2)⁻¹ * ‖ntr (M * Λ * (M * Λ)) - 2 * ntr (M * Λ)‖
      ≤ (81 / 100 : ℝ)⁻¹ * (3 * opNorm Λ) := by
        gcongr
    _ ≤ 4 * opNorm Λ := by nlinarith

/-- `|α + β| ≥ |α|/2` when `Re α ≥ 0` and `|Im β| ≤ Re β`. -/
private lemma MS_sector (α β : ℂ) (hα : 0 ≤ α.re) (hβ : |β.im| ≤ β.re) :
    ‖α‖ / 2 ≤ ‖α + β‖ := by
  have h1 : ‖α‖ ^ 2 / 2 ≤ ‖α + β‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im]
    have hb : β.im ^ 2 ≤ β.re ^ 2 := by
      have := abs_nonneg β.im
      nlinarith [sq_abs β.im]
    nlinarith [mul_nonneg hα (le_trans (abs_nonneg _) hβ), sq_nonneg (α.im + 2 * β.im)]
  have h2 : (‖α‖ / 2) ^ 2 ≤ ‖α + β‖ ^ 2 := by nlinarith [sq_nonneg ‖α‖]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 h2

/-- The entries of `F diag(κ) F^*` differ by at most `2 max_{l ≠ 0} |κ_l|`. -/
private lemma MS_entry_diff (D : ℕ) [NeZero D] (κ : Fin D → ℂ) (Kb : ℝ) (hKb : 0 ≤ Kb)
    (hκ : ∀ l : Fin D, (l : ℕ) ≠ 0 → ‖κ l‖ ≤ Kb) (a b a' b' : Fin D) :
    ‖(MS_F D * diagonal κ * (MS_F D)ᴴ) a b - (MS_F D * diagonal κ * (MS_F D)ᴴ) a' b'‖ ≤
      2 * Kb := by
  have hD : D ≠ 0 := NeZero.ne D
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD
  have happ : ∀ x y : Fin D, (MS_F D * diagonal κ * (MS_F D)ᴴ) x y =
      ∑ l : Fin D, κ l * (MS_F D x l * star (MS_F D y l)) := by
    intro x y
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    ring
  have hF : ∀ x y l : Fin D, MS_F D x l * star (MS_F D y l) =
      (D : ℂ)⁻¹ * (MS_zeta D ^ ((l : ℕ) * (x : ℕ)) * star (MS_zeta D ^ ((l : ℕ) * (y : ℕ)))) := by
    intro x y l
    simp only [MS_F, Matrix.of_apply, MS_fourierVec_eq, star_mul']
    rw [← MS_sqrt_inv_sq D]
    ring
  have hFn : ∀ x y l : Fin D, ‖MS_F D x l * star (MS_F D y l)‖ = (D : ℝ)⁻¹ := by
    intro x y l
    rw [hF, norm_mul, norm_mul, norm_star, MS_norm_zeta_pow D hD, MS_norm_zeta_pow D hD, norm_inv,
      Complex.norm_natCast]
    ring
  rw [happ, happ, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ l : Fin D, ‖κ l * (MS_F D a l * star (MS_F D b l)) -
        κ l * (MS_F D a' l * star (MS_F D b' l))‖ ≤ ∑ _l : Fin D, 2 * Kb / D := by
        refine Finset.sum_le_sum fun l _ => ?_
        by_cases hl : (l : ℕ) = 0
        · rw [hF, hF, hl]
          simp only [zero_mul, pow_zero, star_one, mul_one, sub_self, norm_zero]
          positivity
        · rw [← mul_sub, norm_mul]
          have h2 : ‖MS_F D a l * star (MS_F D b l) - MS_F D a' l * star (MS_F D b' l)‖ ≤
              2 / D := by
            refine (norm_sub_le _ _).trans ?_
            rw [hFn, hFn]; ring_nf; rfl
          calc ‖κ l‖ * ‖MS_F D a l * star (MS_F D b l) - MS_F D a' l * star (MS_F D b' l)‖
              ≤ Kb * (2 / D) := mul_le_mul (hκ l hl) h2 (norm_nonneg _) hKb
            _ = 2 * Kb / D := by ring
    _ = 2 * Kb := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- The large-`N` regime: `N ≥ 1`, `‖Λ‖ ≤ 1/10`, `‖Λ‖ ≤ θ`, `0 ≤ X ≤ θ`, `X ≤ (N^{-δ_A})²` and
`‖A‖²_HS = N X`. -/
private lemma MS_setup (D : ℕ) (δA θ : ℝ) (hδA : 0 < δA) (hθ : 0 < θ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ,
      opNorm A ≤ (N : ℝ) ^ (-δA) →
      1 ≤ N ∧ opNorm (lam D N A) ≤ 1 / 10 ∧ opNorm (lam D N A) ≤ θ ∧ 0 ≤ MS_S A / N ∧
        MS_S A / N ≤ θ ∧ MS_S A / N ≤ ((N : ℝ) ^ (-δA)) ^ 2 ∧ hsNorm A ^ 2 = MS_S A := by
  set θ' : ℝ := min (θ / (2 * (D + 1) ^ 2)) (min (1 / (20 * (D + 1) ^ 2)) 1) with hθ'
  have hθ'0 : 0 < θ' := by
    simp only [hθ', lt_min_iff]; refine ⟨by positivity, by positivity, one_pos⟩
  have h1 : θ' ≤ θ / (2 * (D + 1) ^ 2) := min_le_left _ _
  have h2 : θ' ≤ 1 / (20 * (D + 1) ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : θ' ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N₀, hN₀1, hN₀⟩ := MS_N0 δA θ' hδA hθ'0
  refine ⟨N₀, fun N hN A hA => ?_⟩
  have hN1 : 1 ≤ N := hN₀1.trans hN
  have hAθ := hA.trans (hN₀ N hN)
  obtain ⟨hℓ, hX0, hX⟩ := MS_small D N hN1 A θ' hAθ
  obtain ⟨-, -, hX'⟩ := MS_small D N hN1 A _ hA
  have hD2 : (D : ℝ) ^ 2 ≤ (D + 1) ^ 2 := by gcongr; linarith
  have hDp : (0 : ℝ) < (D + 1) ^ 2 := by positivity
  refine ⟨hN1, ?_, ?_, hX0, ?_, hX', ?_⟩
  · calc opNorm (lam D N A) ≤ 2 * D ^ 2 * θ' := hℓ
      _ ≤ 2 * (D + 1) ^ 2 * (1 / (20 * (D + 1) ^ 2)) := by gcongr
      _ = 1 / 10 := by field_simp; ring
  · calc opNorm (lam D N A) ≤ 2 * D ^ 2 * θ' := hℓ
      _ ≤ 2 * (D + 1) ^ 2 * (θ / (2 * (D + 1) ^ 2)) := by gcongr
      _ = θ := by field_simp
  · calc MS_S A / N ≤ θ' ^ 2 := hX
      _ ≤ θ' := by nlinarith
      _ ≤ θ / (2 * (D + 1) ^ 2) := h1
      _ ≤ θ := div_le_self hθ.le (by
          have : (0 : ℝ) ≤ D := Nat.cast_nonneg D
          nlinarith)
  · unfold hsNorm MS_S; exact Real.sq_sqrt (by positivity)

/-- `Re β ≥ X g Re R - E` and `|Im β| ≤ X g |Im R| + E` when `|β - X R g| ≤ E`, `g` real. -/
private lemma MS_beta (β R g : ℂ) (X E : ℝ) (hX : 0 ≤ X) (hg : g.im = 0) (hg0 : 0 ≤ g.re)
    (h : ‖β - (X : ℂ) * R * g‖ ≤ E) :
    X * g.re * R.re - E ≤ β.re ∧ |β.im| ≤ X * g.re * |R.im| + E := by
  have hre : ((X : ℂ) * R * g).re = X * g.re * R.re := by
    simp [Complex.mul_re, hg]; ring
  have him : ((X : ℂ) * R * g).im = X * g.re * R.im := by
    simp [Complex.mul_im, hg]; ring
  have a1 := (Complex.abs_re_le_norm (β - (X : ℂ) * R * g)).trans h
  have a2 := (Complex.abs_im_le_norm (β - (X : ℂ) * R * g)).trans h
  rw [Complex.sub_re, hre] at a1
  rw [Complex.sub_im, him] at a2
  have hXg : 0 ≤ X * g.re := mul_nonneg hX hg0
  constructor
  · linarith [neg_abs_le (β.re - X * g.re * R.re)]
  · have : |X * g.re * R.im| = X * g.re * |R.im| := by
      rw [abs_mul, abs_of_nonneg hXg]
    have := abs_sub_abs_le_abs_sub β.im (X * g.re * R.im)
    linarith

/-- `1 - B` is invertible and `‖(1 - B)⁻¹‖ ≤ c⁻¹` when every `|1 - λ̂_l| ≥ c > 0`. -/
private lemma MS_inv_le (D : ℕ) (hD : D ≠ 0) (B : Matrix (Fin D) (Fin D) ℂ)
    (hB : ∀ l, B *ᵥ fourierVec D l = circEig B l • fourierVec D l) (c : ℝ) (hc : 0 < c)
    (h : ∀ l, c ≤ ‖1 - circEig B l‖) :
    (1 - B).det ≠ 0 ∧ opNorm ((1 - B)⁻¹) ≤ c⁻¹ := by
  have hμ : ∀ l, 1 - circEig B l ≠ 0 := fun l e => by
    have := h l; rw [e, norm_zero] at this; linarith
  obtain ⟨hdet, -, hn⟩ := MS_circ_inv D hD B _ hB hμ
  refine ⟨hdet, ?_⟩
  rw [hn]
  refine (pi_norm_le_iff_of_nonneg (inv_nonneg.2 hc.le)).2 fun l => ?_
  rw [norm_inv]
  exact inv_anti₀ hc (h l)

/-- The crude bound `|λ̂_0 - λ̂_l| ≤ (8D + 3D²) X`. -/
private lemma MS_crude (D : ℕ) (hD : 2 ≤ D) [NeZero D] (N : ℕ) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im)
    (z₁ z₂ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) (l : Fin D) :
    ‖circEig (Mhat (lam D N A) z₁ z₂) 0 - circEig (Mhat (lam D N A) z₁ z₂) l‖ ≤
      (8 * D + 3 * D ^ 2) * (MS_S A / N) := by
  have : Nonempty (Idx D N) := ⟨(0, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  obtain ⟨-, -, -, hexp⟩ := MS_spec D hD N hN A hℓ z hz z₁ z₂ h₁ h₂
  obtain ⟨g₀, -, hg⟩ := MS_g_facts D hD
  obtain ⟨-, -, -, w1, -⟩ := MS_res hΛ hℓ hz h₁
  obtain ⟨-, -, -, w2, -⟩ := MS_res hΛ hℓ hz h₂
  have hX0 : 0 ≤ MS_S A / N := by have := MS_S_nonneg A; positivity
  have hl0 := MS_op_nonneg (lam D N A)
  have hR : ‖(((z₁ + mExt (lam D N A) z₁) * (z₂ + mExt (lam D N A) z₂)) ^ 2)⁻¹‖ ≤ 2 := by
    rw [norm_inv, norm_pow, norm_mul]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    have := mul_le_mul w1.le w2.le (by norm_num) (norm_nonneg _)
    nlinarith
  have hgn := (hg l).2.2.1
  have e := hexp l
  set X := MS_S A / N
  set R := (((z₁ + mExt (lam D N A) z₁) * (z₂ + mExt (lam D N A) z₂)) ^ 2)⁻¹
  have hXRg : ‖(X : ℂ) * R * MS_g D l‖ ≤ X * 2 * (4 * D) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
    gcongr
  calc ‖circEig (Mhat (lam D N A) z₁ z₂) 0 - circEig (Mhat (lam D N A) z₁ z₂) l‖
      ≤ ‖(X : ℂ) * R * MS_g D l‖ + ‖circEig (Mhat (lam D N A) z₁ z₂) 0 -
          circEig (Mhat (lam D N A) z₁ z₂) l - (X : ℂ) * R * MS_g D l‖ := by
        have := norm_add_le ((X : ℂ) * R * MS_g D l) (circEig (Mhat (lam D N A) z₁ z₂) 0 -
          circEig (Mhat (lam D N A) z₁ z₂) l - (X : ℂ) * R * MS_g D l)
        rwa [add_sub_cancel] at this
    _ ≤ X * 2 * (4 * D) + 24 * D ^ 2 * (1 / 10) * X := by
        gcongr
        exact e.trans (by gcongr)
    _ ≤ (8 * D + 3 * D ^ 2) * X := by nlinarith

/-- `d₁ = Im m / (Im m + η) ∈ (0, 1)`. -/
private lemma MS_d_bounds (y η : ℝ) (hy : 0 < y) (hη : 0 < η) :
    0 < y / (y + η) ∧ y / (y + η) < 1 ∧ 1 - y / (y + η) = η / (y + η) := by
  refine ⟨by positivity, (div_lt_one (by linarith)).2 (by linarith), ?_⟩
  field_simp; ring

/-- `‖1 - ⟨M(z₁)²⟩‖ = ‖1 - ⟨M(z)²⟩‖` for `z₁ ∈ {z, z̄}`. -/
private lemma MS_conj_scalar {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) {z : ℂ} (hz : 0 < z.im) {z₁ : ℂ}
    (h₁ : z₁ = z ∨ z₁ = star z) :
    ‖1 - ntr (MExt Λ z₁ * MExt Λ z₁)‖ = ‖1 - ntr (MExt Λ z * MExt Λ z)‖ := by
  rcases h₁ with rfl | rfl
  · rfl
  · rw [(mExt_conj Λ hΛ z hz.ne').2, ← conjTranspose_mul, MS_ntr_conj, ← star_one ℂ,
      ← star_sub, norm_star, star_one]

end MS_Aux

/-- For `z₁ = z̄₂ ∈ {z, z̄}`: the row sums of `M̂` are `d₁`, `λ̂_0 = d₁`, and `|λ̂_l| ≤ d₁`. -/
private lemma MS_conj_pair (D : ℕ) (hD : 2 ≤ D) [NeZero D] (N : ℕ) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im)
    (z₁ z₂ : ℂ) (hzz : z₁ = z ∧ z₂ = star z ∨ z₁ = star z ∧ z₂ = z) :
    (z₁ = z ∨ z₁ = star z) ∧ (z₂ = z ∨ z₂ = star z) ∧
    (∀ a : Fin D, ∑ b : Fin D, Mhat (lam D N A) z₁ z₂ a b =
      (((mSol (lam D N A) z).im / ((mSol (lam D N A) z).im + z.im) : ℝ) : ℂ)) ∧
    circEig (Mhat (lam D N A) z₁ z₂) 0 =
      (((mSol (lam D N A) z).im / ((mSol (lam D N A) z).im + z.im) : ℝ) : ℂ) := by
  have : Nonempty (Idx D N) := ⟨(0, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  obtain ⟨hnorm, hntr, hE, -⟩ := MS_dfacts D hD N hN A z hz
  have hconj := (mExt_conj (lam D N A) hΛ z hz.ne').2
  have h12 : (z₁ = z ∨ z₁ = star z) ∧ (z₂ = z ∨ z₂ = star z) := by
    rcases hzz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inl h1, Or.inr h2⟩
    · exact ⟨Or.inr h1, Or.inl h2⟩
  refine ⟨h12.1, h12.2, fun a => ?_, ?_⟩
  · rw [MS_rowsum, MS_ntr_comm, ← Matrix.mul_assoc]
    rcases hzz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hconj, hnorm, hE a]
    · rw [hconj, hE a]
  · rw [MS_circEig_zero_Mhat]
    rcases hzz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hconj, hntr]
    · rw [hconj, MS_ntr_comm, hntr]

/-- For `z₁ = z₂ ∈ {z, z̄}`, `l ≠ 0` and `|1 - λ̂_0| < 1/10`: `|1 - λ̂_l| ≥ |1 - λ̂_0| / 2` and
`|1 - λ̂_l| ≥ g₀ X / 2`, since `Re(1 - λ̂_0) ≥ 0` and `λ̂_0 - λ̂_l` lies in the sector
`|Im| ≤ Re` (the near-edge case of (A.29) [eq:whlambdal]). -/
private lemma MS_same_small (D : ℕ) (hD : 2 ≤ D) [NeZero D] (N : ℕ) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 40) (z : ℂ) (hz : 0 < z.im)
    (z₁ : ℂ) (h₁ : z₁ = z ∨ z₁ = star z) (g₀ : ℝ)
    (hg : ∀ l : Fin D, (MS_g D l).im = 0 ∧ 0 ≤ (MS_g D l).re ∧ ‖MS_g D l‖ ≤ 4 * D ∧
      ((l : ℕ) ≠ 0 → g₀ ≤ (MS_g D l).re))
    (hℓ2 : opNorm (lam D N A) ≤ g₀ / (400 * D ^ 2)) (l : Fin D) (hl : (l : ℕ) ≠ 0)
    (hα : ‖1 - circEig (Mhat (lam D N A) z₁ z₁) 0‖ < 1 / 10) :
    ‖1 - circEig (Mhat (lam D N A) z₁ z₁) 0‖ / 2 ≤ ‖1 - circEig (Mhat (lam D N A) z₁ z₁) l‖ ∧
      g₀ * (MS_S A / N) / 2 ≤ ‖1 - circEig (Mhat (lam D N A) z₁ z₁) l‖ := by
  have : Nonempty (Idx D N) := ⟨(0, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hℓ' : opNorm (lam D N A) ≤ 1 / 10 := hℓ.trans (by norm_num)
  obtain ⟨-, hbd, h0, hexp⟩ := MS_spec D hD N hN A hℓ' z hz z₁ z₁ h₁ h₁
  obtain ⟨r1, -, n1, w1, -⟩ := MS_res hΛ hℓ' hz h₁
  have hw2 := MS_w2 _ _ _ hℓ' r1 n1 w1
  have hy := (mSol_spec (lam D N A) hΛ z hz).1
  obtain ⟨hd0, hd1, -⟩ := MS_d_bounds _ _ hy hz
  obtain ⟨hgi, hgr, -, hgl⟩ := hg l
  have hg0 := hgl hl
  have hD2 : (0 : ℝ) < D ^ 2 := by positivity
  have hX0 : 0 ≤ MS_S A / N := by have := MS_S_nonneg A; positivity
  have hl0 := MS_op_nonneg (lam D N A)
  set X := MS_S A / N
  set ℓ := opNorm (lam D N A)
  set w₁ := z₁ + mExt (lam D N A) z₁
  set lz := circEig (Mhat (lam D N A) z₁ z₁) 0
  set lk := circEig (Mhat (lam D N A) z₁ z₁) l
  set v := (w₁ ^ 2)⁻¹
  have hv : ‖v - 1‖ ≤ 1 / 5 := by
    have e : v - 1 = -(ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₁) - v) - (1 - lz) := by
      rw [h0]; ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg]
    linarith
  set R := ((w₁ * w₁) ^ 2)⁻¹
  have hRv : R = v ^ 2 := by simp only [R, v]; rw [inv_pow]; ring
  have hR : ‖R - 1‖ ≤ 11 / 25 := by
    rw [hRv, show v ^ 2 - 1 = (v - 1) * ((v - 1) + 2) by ring, norm_mul]
    have : ‖(v - 1) + 2‖ ≤ 1 / 5 + 2 := (norm_add_le _ _).trans (by norm_num; linarith)
    calc ‖v - 1‖ * ‖(v - 1) + 2‖ ≤ (1 / 5) * (1 / 5 + 2) :=
          mul_le_mul hv this (norm_nonneg _) (by norm_num)
      _ = 11 / 25 := by norm_num
  have hRre : 14 / 25 ≤ R.re := by
    have := Complex.abs_re_le_norm (R - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    linarith [neg_abs_le (R.re - 1)]
  have hRim : |R.im| ≤ 11 / 25 := by
    have := Complex.abs_im_le_norm (R - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hE : 24 * D ^ 2 * ℓ * X ≤ 3 / 50 * g₀ * X := by
    have : 24 * D ^ 2 * ℓ ≤ 3 / 50 * g₀ := by
      calc 24 * D ^ 2 * ℓ ≤ 24 * D ^ 2 * (g₀ / (400 * D ^ 2)) := by gcongr
        _ = 3 / 50 * g₀ := by field_simp; ring
    exact mul_le_mul_of_nonneg_right this hX0
  obtain ⟨b1, b2⟩ := MS_beta (lz - lk) R (MS_g D l) X _ hX0 hgi hgr (hexp l)
  have hXg : g₀ * X ≤ (MS_g D l).re * X := mul_le_mul_of_nonneg_right hg0 hX0
  have hRe_beta : (MS_g D l).re * X / 2 ≤ (lz - lk).re := by
    have : X * (MS_g D l).re * (14 / 25) ≤ X * (MS_g D l).re * R.re :=
      mul_le_mul_of_nonneg_left hRre (mul_nonneg hX0 hgr)
    nlinarith
  have hIm_beta : |(lz - lk).im| ≤ (lz - lk).re := by
    have : X * (MS_g D l).re * |R.im| ≤ X * (MS_g D l).re * (11 / 25) :=
      mul_le_mul_of_nonneg_left hRim (mul_nonneg hX0 hgr)
    nlinarith
  have hRe_alpha : 0 ≤ (1 - lz).re := by
    have := Complex.re_le_norm lz
    simp only [Complex.sub_re, Complex.one_re]
    linarith [hbd 0]
  have e1 : 1 - lk = (1 - lz) + (lz - lk) := by ring
  refine ⟨?_, ?_⟩
  · rw [e1]; exact MS_sector _ _ hRe_alpha hIm_beta
  · rw [e1]
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.add_re]
    nlinarith

/-- For `z₁ = z̄₂ ∈ {z, z̄}`, `|z| ≤ τ⁻¹` and `l ≠ 0`: `|1 - λ̂_l| ≥ g₀ ρ X / 2` with
`ρ = (τ⁻¹ + 1)⁻⁴` (the case `z₁ = z̄₂` of (A.29) [eq:whlambdal]). -/
private lemma MS_conj_lower (D : ℕ) (hD : 2 ≤ D) [NeZero D] (N : ℕ) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10) (τ : ℝ) (hτ : 0 < τ)
    (z : ℂ) (hzn : ‖z‖ ≤ τ⁻¹) (hz : 0 < z.im) (z₁ z₂ : ℂ)
    (hzz : z₁ = z ∧ z₂ = star z ∨ z₁ = star z ∧ z₂ = z) (g₀ : ℝ)
    (hg : ∀ l : Fin D, (MS_g D l).im = 0 ∧ 0 ≤ (MS_g D l).re ∧ ‖MS_g D l‖ ≤ 4 * D ∧
      ((l : ℕ) ≠ 0 → g₀ ≤ (MS_g D l).re))
    (hℓ2 : opNorm (lam D N A) ≤ g₀ * ((τ⁻¹ + 1) ^ 4)⁻¹ / (48 * D ^ 2)) (l : Fin D)
    (hl : (l : ℕ) ≠ 0) :
    g₀ * ((τ⁻¹ + 1) ^ 4)⁻¹ * (MS_S A / N) / 2 ≤ ‖1 - circEig (Mhat (lam D N A) z₁ z₂) l‖ := by
  have : Nonempty (Idx D N) := ⟨(0, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  obtain ⟨h₁, h₂, -, h0⟩ := MS_conj_pair D hD N hN A z hz z₁ z₂ hzz
  obtain ⟨-, hbd, -, hexp⟩ := MS_spec D hD N hN A hℓ z hz z₁ z₂ h₁ h₂
  obtain ⟨-, -, -, w0, wτ⟩ := MS_res hΛ hℓ hz (Or.inl rfl : z = z ∨ z = star z)
  have hy := (mSol_spec (lam D N A) hΛ z hz).1
  obtain ⟨hd0, hd1, -⟩ := MS_d_bounds _ _ hy hz
  obtain ⟨hgi, hgr, -, hgl⟩ := hg l
  have hg0 := hgl hl
  have hD2 : (0 : ℝ) < D ^ 2 := by positivity
  have hX0 : 0 ≤ MS_S A / N := by have := MS_S_nonneg A; positivity
  set X := MS_S A / N
  set w := z + mExt (lam D N A) z
  have hconj : mExt (lam D N A) (star z) = star (mExt (lam D N A) z) :=
    (mExt_conj (lam D N A) hΛ z hz.ne').1
  have hww : (z₁ + mExt (lam D N A) z₁) * (z₂ + mExt (lam D N A) z₂) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rcases hzz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hconj, ← star_add, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · rw [hconj, ← star_add, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow]
  set ρ : ℝ := ((τ⁻¹ + 1) ^ 4)⁻¹
  have hw0 : 0 < ‖w‖ := by linarith
  have hwτ : ‖w‖ ≤ τ⁻¹ + 1 := wτ.trans (by linarith)
  set R := (((z₁ + mExt (lam D N A) z₁) * (z₂ + mExt (lam D N A) z₂)) ^ 2)⁻¹
  have hR : R = (((‖w‖ ^ 4)⁻¹ : ℝ) : ℂ) := by
    simp only [R, hww]; push_cast; ring
  have hRre : ρ ≤ R.re := by
    rw [hR, Complex.ofReal_re]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hw0.le hwτ 4)
  have hρ : 0 < ρ := by positivity
  have hE : 24 * D ^ 2 * opNorm (lam D N A) * X ≤ g₀ * ρ / 2 * X := by
    have : 24 * D ^ 2 * opNorm (lam D N A) ≤ g₀ * ρ / 2 := by
      calc 24 * D ^ 2 * opNorm (lam D N A) ≤ 24 * D ^ 2 * (g₀ * ρ / (48 * D ^ 2)) := by gcongr
        _ = g₀ * ρ / 2 := by field_simp; ring
    exact mul_le_mul_of_nonneg_right this hX0
  obtain ⟨b1, -⟩ := MS_beta _ R (MS_g D l) X _ hX0 hgi hgr (hexp l)
  set lz := circEig (Mhat (lam D N A) z₁ z₂) 0
  set lk := circEig (Mhat (lam D N A) z₁ z₂) l
  have hRe_alpha : 0 ≤ (1 - lz).re := by
    have := Complex.re_le_norm lz
    simp only [Complex.sub_re, Complex.one_re]
    linarith [hbd 0]
  have e1 : 1 - lk = (1 - lz) + (lz - lk) := by ring
  rw [e1]
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [Complex.add_re]
  have h1 : X * g₀ * ρ ≤ X * (MS_g D l).re * R.re :=
    mul_le_mul (mul_le_mul_of_nonneg_left hg0 hX0) hRre hρ.le (mul_nonneg hX0 hgr)
  nlinarith

/-! ### Lemma A.1 (vii)–(xii) and the stability of `1 - M̂` -/

/-- (A.8) [1-M]: for `z₁ = z̄₂ ∈ {z, z̄}`, `‖[1 - M̂(z₁, z₂)]⁻¹‖ = (Im m + η)/η ≤ C Im m / η`,
`|z| ≤ τ⁻¹`, `η > 0`, `Λ = lam D N A`, `‖A‖ ≤ N^{-δ_A}`. -/
theorem one_minus_Mhat_conj (D : ℕ) (hD : 2 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
        opNorm ((1 - Mhat (lam D N A) z (star z))⁻¹) =
            ((mSol (lam D N A) z).im + z.im) / z.im ∧
          opNorm ((1 - Mhat (lam D N A) (star z) z)⁻¹) =
            ((mSol (lam D N A) z).im + z.im) / z.im ∧
          ((mSol (lam D N A) z).im + z.im) / z.im ≤ C * ((mSol (lam D N A) z).im / z.im) := by
  have : NeZero D := ⟨by omega⟩
  have hD0 : D ≠ 0 := by omega
  obtain ⟨CS, hCS, hS⟩ := MS_scalar τ hτ
  obtain ⟨N₀, hN₀⟩ := MS_setup D δA 1 hδA one_pos
  refine ⟨1 + CS, by linarith, N₀, fun N hN A hA z hzn hz => ?_⟩
  obtain ⟨hN1, hℓ, -⟩ := hN₀ N hN A hA
  have : Nonempty (Idx D N) := ⟨(0, ⟨0, hN1⟩)⟩
  have hy := (mSol_spec (lam D N A) (lam_isHermitian D N A) z hz).1
  obtain ⟨hd0, hd1, hd⟩ := MS_d_bounds _ _ hy hz
  set y := (mSol (lam D N A) z).im
  set d : ℝ := y / (y + z.im)
  have key : ∀ z₁ z₂ : ℂ, (z₁ = z ∧ z₂ = star z ∨ z₁ = star z ∧ z₂ = z) →
      opNorm ((1 - Mhat (lam D N A) z₁ z₂)⁻¹) = (y + z.im) / z.im := by
    intro z₁ z₂ hzz
    obtain ⟨h₁, h₂, -, h0⟩ := MS_conj_pair D hD N hN1 A z hz z₁ z₂ hzz
    obtain ⟨hev, hbd, -, -⟩ := MS_spec D hD N hN1 A hℓ z hz z₁ z₂ h₁ h₂
    have hlow : ∀ l, 1 - d ≤ ‖1 - circEig (Mhat (lam D N A) z₁ z₂) l‖ := by
      intro l
      have := norm_sub_norm_le (1 : ℂ) (circEig (Mhat (lam D N A) z₁ z₂) l)
      rw [norm_one] at this
      linarith [hbd l]
    have hμ : ∀ l, 1 - circEig (Mhat (lam D N A) z₁ z₂) l ≠ 0 := fun l e => by
      have := hlow l; rw [e, norm_zero] at this; linarith
    obtain ⟨-, -, hn⟩ := MS_circ_inv D hD0 _ _ hev hμ
    rw [hn]
    have hval : (1 - d)⁻¹ = (y + z.im) / z.im := by rw [hd, inv_div]
    rw [← hval]
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg (inv_nonneg.2 (by linarith))).2 fun l => ?_
      rw [norm_inv]
      exact inv_anti₀ (by linarith) (hlow l)
    · have := norm_le_pi_norm (fun l => (1 - circEig (Mhat (lam D N A) z₁ z₂) l)⁻¹) 0
      refine le_trans (le_of_eq ?_) this
      simp only [h0, norm_inv]
      rw [show (1 : ℂ) - (d : ℂ) = ((1 - d : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
  refine ⟨key z (star z) (Or.inl ⟨rfl, rfl⟩), key (star z) z (Or.inr ⟨rfl, rfl⟩), ?_⟩
  obtain ⟨hηy, -⟩ := hS D hD N hN1 A hℓ z hzn hz
  rw [div_le_iff₀ hz, mul_assoc, div_mul_cancel₀ _ hz.ne']
  linarith

set_option maxHeartbeats 1000000 in
/-- (A.9) [1-M-2] and (A.10) [1-M-3]: for `z₁ = z₂ ∈ {z, z̄}` with
`c₀ N^{-ε_g} ≤ η / Im m ≤ c₀⁻¹ N^{-ε_g}`, `ε_g ∈ (0, δ_A/4)`:
`1 - M̂(z₁, z₂)` and `1 - ⟨M(z₁) M(z₂)⟩` are invertible,
`‖[1 - M̂(z₁, z₂)]⁻¹‖ ≤ C ((Im m)⁻¹ ∧ N^{ε_g})` and `|1 - ⟨M(z₁) M(z₂)⟩|⁻¹ ≤ C ((Im m)⁻¹ ∧ N^{ε_g})`. -/
theorem one_minus_Mhat_same (D : ℕ) (hD : 2 ≤ D) (δA εg c₀ τ : ℝ) (hδA : 0 < δA)
    (hεg : 0 < εg) (hεg' : εg < δA / 4) (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
        c₀ * (N : ℝ) ^ (-εg) ≤ z.im / (mSol (lam D N A) z).im →
        z.im / (mSol (lam D N A) z).im ≤ c₀⁻¹ * (N : ℝ) ^ (-εg) →
        ∀ z₁ : ℂ, z₁ = z ∨ z₁ = star z →
          (1 - Mhat (lam D N A) z₁ z₁).det ≠ 0 ∧
            1 - ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₁) ≠ 0 ∧
            opNorm ((1 - Mhat (lam D N A) z₁ z₁)⁻¹) ≤
              C * min ((mSol (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) ∧
            ‖1 - ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₁)‖⁻¹ ≤
              C * min ((mSol (lam D N A) z).im)⁻¹ ((N : ℝ) ^ εg) := by
  have : NeZero D := ⟨by omega⟩
  have hD0 : D ≠ 0 := by omega
  obtain ⟨CS, hCS, hS⟩ := MS_scalar τ hτ
  set K : ℝ := 8 * D + 3 * D ^ 2
  have hK : 0 < K := by positivity
  set θ : ℝ := (CS ^ 2)⁻¹ / (2 * K)
  have hθ : 0 < θ := by positivity
  obtain ⟨N₁, -, hN₁⟩ := MS_N0 δA θ hδA hθ
  obtain ⟨N₂, hN₂⟩ := MS_setup D δA 1 hδA one_pos
  set C : ℝ := 1 + c₀⁻¹ + 2 * CS ^ 2
  refine ⟨C, by positivity, max N₁ N₂, fun N hN A hA z hzn hz hw1 _ z₁ h₁ => ?_⟩
  obtain ⟨hN1, hℓ, -, hX0, -, hXA, -⟩ := hN₂ N (le_of_max_le_right hN) A hA
  have hNθ := hN₁ N (le_of_max_le_left hN)
  have : Nonempty (Idx D N) := ⟨(0, ⟨0, hN1⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hy := (mSol_spec (lam D N A) hΛ z hz).1
  obtain ⟨hd0, hd1, hd⟩ := MS_d_bounds _ _ hy hz
  obtain ⟨-, hlow, -, -, hyq, -⟩ := hS D hD N hN1 A hℓ z hzn hz
  obtain ⟨hev, hbd, h0, -⟩ := MS_spec D hD N hN1 A hℓ z hz z₁ z₁ h₁ h₁
  have hsc := MS_conj_scalar hΛ hz h₁
  set y := (mSol (lam D N A) z).im
  set η := z.im
  set d : ℝ := y / (y + η)
  set X := MS_S A / N
  set q := Real.sqrt (kappa (lam D N A) z.re + η)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set P : ℝ := (N : ℝ) ^ εg
  have hP1 : 1 ≤ P := Real.one_le_rpow hNr hεg.le
  have hP0 : 0 < P := by linarith
  have hPn : (N : ℝ) ^ (-εg) = P⁻¹ := Real.rpow_neg (by linarith) εg
  rw [hPn] at hw1
  -- `|1 - λ̂_l| ≥ 1 - d₁` and `(1 - d₁)⁻¹ ≤ (1 + c₀⁻¹) N^{ε_g}`
  have hlow1 : ∀ l, 1 - d ≤ ‖1 - circEig (Mhat (lam D N A) z₁ z₁) l‖ := by
    intro l
    have := norm_sub_norm_le (1 : ℂ) (circEig (Mhat (lam D N A) z₁ z₁) l)
    rw [norm_one] at this
    linarith [hbd l]
  have hb1 : (1 - d)⁻¹ ≤ (1 + c₀⁻¹) * P := by
    rw [hd, inv_div]
    have e : (y + η) / η = 1 + (η / y)⁻¹ := by field_simp; ring
    rw [e]
    have : (η / y)⁻¹ ≤ c₀⁻¹ * P := by
      have h2 : (c₀ * P⁻¹)⁻¹ = c₀⁻¹ * P := by rw [mul_inv, inv_inv]
      rw [← h2]
      exact inv_anti₀ (by positivity) hw1
    nlinarith
  -- `|1 - λ̂_0| ≥ y / CS²`
  have hα : (CS ^ 2)⁻¹ * y ≤ ‖1 - circEig (Mhat (lam D N A) z₁ z₁) 0‖ := by
    rw [h0, hsc]
    refine le_trans ?_ hlow
    have : y ≤ CS * q := hyq
    rw [sq, mul_inv]
    calc CS⁻¹ * CS⁻¹ * y ≤ CS⁻¹ * CS⁻¹ * (CS * q) := by gcongr
      _ = CS⁻¹ * q := by field_simp
  -- `K X ≤ y / (2 CS²)` when `y ≥ N^{-ε_g}`
  have hKX : K * X ≤ (CS ^ 2)⁻¹ / 2 * P⁻¹ := by
    have h1 : (N : ℝ) ^ (-δA) ≤ P⁻¹ := by
      rw [← hPn]
      exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    have h2 : X ≤ θ * P⁻¹ := by
      calc X ≤ ((N : ℝ) ^ (-δA)) ^ 2 := hXA
        _ = (N : ℝ) ^ (-δA) * (N : ℝ) ^ (-δA) := sq _
        _ ≤ θ * P⁻¹ := mul_le_mul hNθ h1 (by positivity) hθ.le
    calc K * X ≤ K * (θ * P⁻¹) := mul_le_mul_of_nonneg_left h2 hK.le
      _ = (CS ^ 2)⁻¹ / 2 * P⁻¹ := by simp only [θ]; field_simp
  set m : ℝ := min y⁻¹ P
  have hm : 0 < m := lt_min (inv_pos.2 hy) hP0
  have hall : ∀ l, (C * m)⁻¹ ≤ ‖1 - circEig (Mhat (lam D N A) z₁ z₁) l‖ := by
    intro l
    by_cases hcase : y⁻¹ ≤ P
    · have hmy : m = y⁻¹ := min_eq_left hcase
      have hyP : P⁻¹ ≤ y := by
        rw [inv_le_comm₀ hP0 hy]; exact hcase
      have hcr := MS_crude D hD N hN1 A hℓ z hz z₁ z₁ h₁ h₁ l
      have h3 := norm_sub_norm_le (1 - circEig (Mhat (lam D N A) z₁ z₁) 0)
        (-(circEig (Mhat (lam D N A) z₁ z₁) 0 - circEig (Mhat (lam D N A) z₁ z₁) l))
      rw [sub_neg_eq_add, norm_neg,
        show 1 - circEig (Mhat (lam D N A) z₁ z₁) 0 +
          (circEig (Mhat (lam D N A) z₁ z₁) 0 - circEig (Mhat (lam D N A) z₁ z₁) l) =
          1 - circEig (Mhat (lam D N A) z₁ z₁) l by ring] at h3
      have h4 : (CS ^ 2)⁻¹ / 2 * P⁻¹ ≤ (CS ^ 2)⁻¹ / 2 * y :=
        mul_le_mul_of_nonneg_left hyP (by positivity)
      have h5 : (C * m)⁻¹ ≤ (CS ^ 2)⁻¹ / 2 * y := by
        rw [hmy, mul_inv, inv_inv]
        have : C⁻¹ ≤ (CS ^ 2)⁻¹ / 2 := by
          rw [div_eq_mul_inv, ← mul_inv]
          exact inv_anti₀ (by positivity) (by simp only [C]; nlinarith [inv_pos.2 hc₀])
        nlinarith
      nlinarith
    · push Not at hcase
      have hmP : m = P := min_eq_right hcase.le
      rw [hmP]
      refine le_trans ?_ (hlow1 l)
      have : ((1 + c₀⁻¹) * P)⁻¹ ≤ 1 - d := by
        rw [inv_le_comm₀ (by positivity) (by linarith)]; exact hb1
      refine le_trans (inv_anti₀ (by positivity) ?_) this
      exact mul_le_mul_of_nonneg_right (by simp only [C]; nlinarith) hP0.le
  obtain ⟨hdet, hn⟩ := MS_inv_le D hD0 _ hev _ (by positivity) hall
  have h00 := hall 0
  rw [h0] at h00
  refine ⟨hdet, fun e => ?_, by rwa [inv_inv] at hn, ?_⟩
  · rw [e, norm_zero] at h00
    have : 0 < (C * m)⁻¹ := by positivity
    linarith
  · rw [← inv_inv (C * m)]
    exact inv_anti₀ (by positivity) h00

/-- (A.11) [flat_M] in multiplicative form: for `z₁, z₂ ∈ {z, z̄}`, `|z| ≤ τ⁻¹`, `η > 0`,
`1 - M̂(z₁, z₂)` is invertible and `‖A‖²_HS · |K_{ab} - K_{a'b'}| ≤ C N`. -/
theorem flat_M (D : ℕ) (hD : 2 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
      ∀ z₁ z₂ : ℂ, (z₁ = z ∨ z₁ = star z) → (z₂ = z ∨ z₂ = star z) →
        (1 - Mhat (lam D N A) z₁ z₂).det ≠ 0 ∧
        ∀ a b a' b' : Fin D,
          hsNorm A ^ 2 * ‖Kmat (lam D N A) z₁ z₂ a b - Kmat (lam D N A) z₁ z₂ a' b'‖ ≤
            C * N := by
  have : NeZero D := ⟨by omega⟩
  have hD0 : D ≠ 0 := by omega
  obtain ⟨g₀, hg₀, hg⟩ := MS_g_facts D hD
  set K : ℝ := 8 * D + 3 * D ^ 2
  have hK : 0 < K := by positivity
  set ρ : ℝ := ((τ⁻¹ + 1) ^ 4)⁻¹
  have hρ : 0 < ρ := by positivity
  set θ : ℝ := min (min (1 / (20 * K)) (g₀ / (400 * D ^ 2)))
    (min (g₀ * ρ / (48 * D ^ 2)) (1 / 40))
  have hθ : 0 < θ := by
    simp only [θ, lt_min_iff]
    exact ⟨⟨by positivity, by positivity⟩, by positivity, by norm_num⟩
  have hθ1 : θ ≤ 1 / (20 * K) := (min_le_left _ _).trans (min_le_left _ _)
  have hθ2 : θ ≤ g₀ / (400 * D ^ 2) := (min_le_left _ _).trans (min_le_right _ _)
  have hθ3 : θ ≤ g₀ * ρ / (48 * D ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hθ4 : θ ≤ 1 / 40 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N₀, hN₀⟩ := MS_setup D δA θ hδA hθ
  set cf : ℝ := min (1 / 20) (min (g₀ * ρ / 2) (g₀ / 2))
  have hcf : 0 < cf := by
    simp only [cf, lt_min_iff]; exact ⟨by norm_num, by positivity, by positivity⟩
  refine ⟨2 / cf, by positivity, N₀, fun N hN A hA z hzn hz z₁ z₂ h₁ h₂ => ?_⟩
  obtain ⟨hN1, hℓ, hℓθ, hX0, hXθ, -, hhs⟩ := hN₀ N hN A hA
  have : Nonempty (Idx D N) := ⟨(0, ⟨0, hN1⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hy := (mSol_spec (lam D N A) hΛ z hz).1
  obtain ⟨hd0, hd1, hd⟩ := MS_d_bounds _ _ hy hz
  obtain ⟨hev, hbd, -, -⟩ := MS_spec D hD N hN1 A hℓ z hz z₁ z₂ h₁ h₂
  set B := Mhat (lam D N A) z₁ z₂
  set X := MS_S A / N
  set d : ℝ := (mSol (lam D N A) z).im / ((mSol (lam D N A) z).im + z.im)
  have hlow1 : ∀ l, 1 - d ≤ ‖1 - circEig B l‖ := by
    intro l
    have := norm_sub_norm_le (1 : ℂ) (circEig B l)
    rw [norm_one] at this
    linarith [hbd l]
  have hμ : ∀ l, 1 - circEig B l ≠ 0 := fun l e => by
    have := hlow1 l; rw [e, norm_zero] at this; linarith
  obtain ⟨hdet, hinv, -⟩ := MS_circ_inv D hD0 B _ hev hμ
  refine ⟨hdet, fun a b a' b' => ?_⟩
  -- `|1 - λ̂_l| ≥ c X` for `l ≠ 0`
  have hlow : ∀ l : Fin D, (l : ℕ) ≠ 0 → cf * X ≤ ‖1 - circEig B l‖ := by
    intro l hl
    have hcase : (z₁ = z ∧ z₂ = star z ∨ z₁ = star z ∧ z₂ = z) ∨ z₁ = z₂ := by
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr rfl
    rcases hcase with hzz | rfl
    · have := MS_conj_lower D hD N hN1 A hℓ τ hτ z hzn hz z₁ z₂ hzz g₀ hg (hℓθ.trans hθ3) l hl
      refine le_trans ?_ this
      have : cf ≤ g₀ * ρ / 2 := (min_le_right _ _).trans (min_le_left _ _)
      calc cf * X ≤ g₀ * ρ / 2 * X := mul_le_mul_of_nonneg_right this hX0
        _ = g₀ * ρ * X / 2 := by ring
    · by_cases hbig : 1 / 10 ≤ ‖1 - circEig B 0‖
      · have hcr := MS_crude D hD N hN1 A hℓ z hz z₁ z₁ h₁ h₁ l
        have hKX : K * X ≤ 1 / 20 := by
          calc K * X ≤ K * (1 / (20 * K)) := mul_le_mul_of_nonneg_left (hXθ.trans hθ1) hK.le
            _ = 1 / 20 := by field_simp
        have h3 := norm_sub_norm_le (1 - circEig B 0) (-(circEig B 0 - circEig B l))
        rw [sub_neg_eq_add, norm_neg,
          show 1 - circEig B 0 + (circEig B 0 - circEig B l) = 1 - circEig B l by ring] at h3
        have : cf * X ≤ 1 / 20 * 1 :=
          mul_le_mul (min_le_left _ _) (hXθ.trans (hθ4.trans (by norm_num))) hX0 (by norm_num)
        linarith
      · push Not at hbig
        have := (MS_same_small D hD N hN1 A (hℓθ.trans hθ4) z hz z₁ h₁ g₀ hg (hℓθ.trans hθ2) l
          hl hbig).2
        refine le_trans ?_ this
        have : cf ≤ g₀ / 2 := (min_le_right _ _).trans (min_le_right _ _)
        calc cf * X ≤ g₀ / 2 * X := mul_le_mul_of_nonneg_right this hX0
          _ = g₀ * X / 2 := by ring
  -- `K = F diag(λ̂ / (1 - λ̂)) F^*`
  have hKm : Kmat (lam D N A) z₁ z₂ =
      MS_F D * diagonal (fun l => (1 - circEig B l)⁻¹ * circEig B l) * (MS_F D)ᴴ := by
    have hKB : Kmat (lam D N A) z₁ z₂ = (1 - B)⁻¹ * B := rfl
    rw [hKB, hinv]
    conv_lhs => arg 2; rw [MS_circ D hD0 B _ hev]
    have e : MS_F D * diagonal (fun l => (1 - circEig B l)⁻¹) * (MS_F D)ᴴ *
        (MS_F D * diagonal (circEig B) * (MS_F D)ᴴ) =
        MS_F D * (diagonal (fun l => (1 - circEig B l)⁻¹) * ((MS_F D)ᴴ * MS_F D) *
          diagonal (circEig B)) * (MS_F D)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, MS_F_unitary D hD0, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  have hhsX : hsNorm A ^ 2 = N * X := by
    rw [hhs]; simp only [X]; field_simp
  rcases hX0.eq_or_lt with hX | hX
  · rw [hhsX, ← hX, mul_zero, zero_mul]; positivity
  · have hκ : ∀ l : Fin D, (l : ℕ) ≠ 0 → ‖(1 - circEig B l)⁻¹ * circEig B l‖ ≤ (cf * X)⁻¹ := by
      intro l hl
      rw [norm_mul, norm_inv]
      have h1 : ‖circEig B l‖ ≤ 1 := (hbd l).trans hd1.le
      have h2 : ‖1 - circEig B l‖⁻¹ ≤ (cf * X)⁻¹ := inv_anti₀ (by positivity) (hlow l hl)
      calc ‖1 - circEig B l‖⁻¹ * ‖circEig B l‖ ≤ (cf * X)⁻¹ * 1 :=
            mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
        _ = (cf * X)⁻¹ := mul_one _
    have hdiff := MS_entry_diff D _ _ (by positivity) hκ a b a' b'
    rw [hKm, hhsX]
    calc (N : ℝ) * X * ‖_‖ ≤ N * X * (2 * (cf * X)⁻¹) := by gcongr
      _ = 2 / cf * N := by field_simp

/-- (A.17) [eq:otherM2], (A.18) [eq:akbk2]: for `z₁ = z₂ ∈ {z, z̄}`, `λ̂_0 = ⟨M(z₁)²⟩`, and every
eigenvalue `λ̂_l = d₁ - â_l - i b̂_l` has `â_l ≥ 0` and
`|â_l + i b̂_l| ≤ C (√(κ+η) + ‖A‖²_HS / N)`, `|z| ≤ τ⁻¹`, `η > 0`. -/
theorem otherM2 (D : ℕ) (hD : 2 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im → ∀ z₁ : ℂ, z₁ = z ∨ z₁ = star z →
        (∀ l : Fin D, (l : ℕ) = 0 →
          circEig (Mhat (lam D N A) z₁ z₁) l = ntr (MExt (lam D N A) z₁ ^ 2)) ∧
        ∀ l : Fin D,
          0 ≤ ((((mSol (lam D N A) z).im / ((mSol (lam D N A) z).im + z.im) : ℝ) : ℂ) -
            circEig (Mhat (lam D N A) z₁ z₁) l).re ∧
          ‖(((mSol (lam D N A) z).im / ((mSol (lam D N A) z).im + z.im) : ℝ) : ℂ) -
            circEig (Mhat (lam D N A) z₁ z₁) l‖ ≤
            C * (Real.sqrt (kappa (lam D N A) z.re + z.im) + hsNorm A ^ 2 / N) := by
  have : NeZero D := ⟨by omega⟩
  obtain ⟨CS, hCS, hS⟩ := MS_scalar τ hτ
  obtain ⟨N₀, hN₀⟩ := MS_setup D δA 1 hδA one_pos
  refine ⟨2 * CS + (8 * D + 3 * D ^ 2), by positivity, N₀, fun N hN A hA z hzn hz z₁ h₁ => ?_⟩
  obtain ⟨hN1, hℓ, -, hX0, -, -, hhs⟩ := hN₀ N hN A hA
  have : Nonempty (Idx D N) := ⟨(0, ⟨0, hN1⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hy := (mSol_spec (lam D N A) hΛ z hz).1
  obtain ⟨hd0, hd1, hd⟩ := MS_d_bounds _ _ hy hz
  obtain ⟨-, -, hup, hηy, -, -⟩ := hS D hD N hN1 A hℓ z hzn hz
  obtain ⟨-, hbd, h0, -⟩ := MS_spec D hD N hN1 A hℓ z hz z₁ z₁ h₁ h₁
  have hsc := MS_conj_scalar hΛ hz h₁
  refine ⟨fun l hl => ?_, fun l => ⟨?_, ?_⟩⟩
  · have : l = 0 := Fin.ext hl
    rw [this, h0, sq]
  · simp only [Complex.sub_re, Complex.ofReal_re]
    linarith [Complex.re_le_norm (circEig (Mhat (lam D N A) z₁ z₁) l), hbd l]
  · set y := (mSol (lam D N A) z).im
    set q := Real.sqrt (kappa (lam D N A) z.re + z.im)
    set X := MS_S A / N
    have e : ((y / (y + z.im) : ℝ) : ℂ) - circEig (Mhat (lam D N A) z₁ z₁) l =
        -(((1 - y / (y + z.im) : ℝ) : ℂ)) + (1 - circEig (Mhat (lam D N A) z₁ z₁) 0) +
          (circEig (Mhat (lam D N A) z₁ z₁) 0 - circEig (Mhat (lam D N A) z₁ z₁) l) := by
      push_cast; ring
    rw [e, hhs]
    have t1 : ‖(((1 - y / (y + z.im) : ℝ) : ℂ))‖ ≤ CS * q := by
      rw [Complex.norm_real, Real.norm_eq_abs, hd, abs_of_nonneg (by positivity)]
      exact (div_le_div_of_nonneg_left hz.le hy (by linarith)).trans hηy
    have t2 : ‖1 - circEig (Mhat (lam D N A) z₁ z₁) 0‖ ≤ CS * q := by
      rw [h0, hsc]; exact hup
    have t3 := MS_crude D hD N hN1 A hℓ z hz z₁ z₁ h₁ h₁ l
    have hq : 0 ≤ q := Real.sqrt_nonneg _
    have p1 : 0 ≤ 2 * CS * X := by positivity
    have p2 : 0 ≤ (8 * D + 3 * D ^ 2) * q := by positivity
    calc _ ≤ ‖-(((1 - y / (y + z.im) : ℝ) : ℂ))‖ + ‖1 - circEig (Mhat (lam D N A) z₁ z₁) 0‖ +
          ‖circEig (Mhat (lam D N A) z₁ z₁) 0 - circEig (Mhat (lam D N A) z₁ z₁) l‖ :=
          norm_add₃_le
      _ ≤ CS * q + CS * q + (8 * D + 3 * D ^ 2) * X := by rw [norm_neg]; linarith
      _ ≤ (2 * CS + (8 * D + 3 * D ^ 2)) * (q + X) := by nlinarith

/-- Stability of the block form of (2.13) [def_M]: for `z₁ = z₂ ∈ {z, z̄}`, `|z| ≤ τ⁻¹`, `η > 0`,
`1 - M̂(z₁, z₂)` is invertible and `‖[1 - M̂(z₁, z₂)]⁻¹‖ ≤ C (κ + η)^{-1/2}`. -/
theorem one_minus_Mhat_stability (D : ℕ) (hD : 2 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im → ∀ z₁ : ℂ, z₁ = z ∨ z₁ = star z →
        (1 - Mhat (lam D N A) z₁ z₁).det ≠ 0 ∧
          opNorm ((1 - Mhat (lam D N A) z₁ z₁)⁻¹) ≤
            C / Real.sqrt (kappa (lam D N A) z.re + z.im) := by
  have : NeZero D := ⟨by omega⟩
  have hD0 : D ≠ 0 := by omega
  obtain ⟨CS, hCS, hS⟩ := MS_scalar τ hτ
  obtain ⟨g₀, hg₀, hg⟩ := MS_g_facts D hD
  set K : ℝ := 8 * D + 3 * D ^ 2
  have hK : 0 < K := by positivity
  set θ : ℝ := min (min (1 / (20 * K)) (g₀ / (400 * D ^ 2))) (1 / 40)
  have hθ : 0 < θ := by
    simp only [θ, lt_min_iff]; refine ⟨⟨by positivity, by positivity⟩, by norm_num⟩
  obtain ⟨N₀, hN₀⟩ := MS_setup D δA θ hδA hθ
  refine ⟨20 * CS ^ 2, by positivity, N₀, fun N hN A hA z hzn hz z₁ h₁ => ?_⟩
  obtain ⟨hN1, hℓ, hℓθ, hX0, hXθ, -, -⟩ := hN₀ N hN A hA
  have : Nonempty (Idx D N) := ⟨(0, ⟨0, hN1⟩)⟩
  have hΛ := lam_isHermitian D N A
  obtain ⟨-, hlow, -, -, -, hqC⟩ := hS D hD N hN1 A hℓ z hzn hz
  obtain ⟨hev, -, h0, -⟩ := MS_spec D hD N hN1 A hℓ z hz z₁ z₁ h₁ h₁
  have hsc := MS_conj_scalar hΛ hz h₁
  set q := Real.sqrt (kappa (lam D N A) z.re + z.im)
  have hκ : 0 ≤ kappa (lam D N A) z.re := le_min (abs_nonneg _) (abs_nonneg _)
  have hq : 0 < q := Real.sqrt_pos.2 (by linarith)
  have hθ1 : θ ≤ 1 / (20 * K) := (min_le_left _ _).trans (min_le_left _ _)
  have hθ2 : θ ≤ g₀ / (400 * D ^ 2) := (min_le_left _ _).trans (min_le_right _ _)
  have hθ3 : θ ≤ 1 / 40 := min_le_right _ _
  have hα : CS⁻¹ * q ≤ ‖1 - circEig (Mhat (lam D N A) z₁ z₁) 0‖ := by rw [h0, hsc]; exact hlow
  have hc1 : q / (20 * CS ^ 2) ≤ CS⁻¹ * q / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : CS⁻¹ * q * (20 * CS ^ 2) = 20 * CS * q := by field_simp
    rw [this]; nlinarith
  have hall : ∀ l, q / (20 * CS ^ 2) ≤ ‖1 - circEig (Mhat (lam D N A) z₁ z₁) l‖ := by
    intro l
    by_cases hl : (l : ℕ) = 0
    · have : l = 0 := Fin.ext hl
      rw [this]; linarith [hc1, (by positivity : 0 ≤ CS⁻¹ * q)]
    · by_cases hbig : 1 / 10 ≤ ‖1 - circEig (Mhat (lam D N A) z₁ z₁) 0‖
      · have hcr := MS_crude D hD N hN1 A hℓ z hz z₁ z₁ h₁ h₁ l
        have hKX : K * (MS_S A / N) ≤ 1 / 20 := by
          calc K * (MS_S A / N) ≤ K * (1 / (20 * K)) :=
                mul_le_mul_of_nonneg_left (hXθ.trans hθ1) hK.le
            _ = 1 / 20 := by field_simp
        have e1 : 1 - circEig (Mhat (lam D N A) z₁ z₁) l =
            (1 - circEig (Mhat (lam D N A) z₁ z₁) 0) +
              (circEig (Mhat (lam D N A) z₁ z₁) 0 - circEig (Mhat (lam D N A) z₁ z₁) l) := by
          ring
        have h3 := norm_sub_norm_le (1 - circEig (Mhat (lam D N A) z₁ z₁) 0)
          (-(circEig (Mhat (lam D N A) z₁ z₁) 0 - circEig (Mhat (lam D N A) z₁ z₁) l))
        rw [sub_neg_eq_add, ← e1, norm_neg] at h3
        have hq20 : q / (20 * CS ^ 2) ≤ 1 / 20 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith
      · push Not at hbig
        have := (MS_same_small D hD N hN1 A (hℓθ.trans hθ3) z hz z₁ h₁ g₀ hg (hℓθ.trans hθ2) l hl
          hbig).1
        linarith
  obtain ⟨hdet, hn⟩ := MS_inv_le D hD0 _ hev _ (by positivity) hall
  refine ⟨hdet, hn.trans (le_of_eq ?_)⟩
  field_simp

end RBMTransitionEdge

end
