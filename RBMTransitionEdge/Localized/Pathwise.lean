module

public import RBMTransitionEdge.Main.Statements
public import RBMTransitionEdge.LocalLaw.Class
public import RBMTransitionEdge.Tools.MinMax

@[expose] public section

/-!
# Pathwise inequalities of the localized phase

`Im G`, the linearity of `Λ` in the coupling, the first inequality of (5.26) [bdwgy] for every unit
eigenvector, and the pathwise form of (5.16) [eq:boundE1] and (5.18)
[localized_bound_eigenvector_general_D].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `Im G(z) = (G(z) - G(z)^*)/(2i)` for the resolvent `G(z) = (X - z)⁻¹` of (2.12)
[def_resolv]. -/
def imRes {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  (2 * Complex.I)⁻¹ • (res X z - (res X z)ᴴ)

/-- The coupling `A` enters linearly: `t Λ(A) = Λ(t A)` for the interaction `Λ` of (1.3)
[matrix_H] and real `t`, so `H + tΛ` of Theorem 2.5 [theorem_localized_eigenvalue] is the model
with coupling `tA`. -/
theorem lam_smul (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    (t : ℂ) • lam D N A = lam D N ((t : ℂ) • A) := by
  ext p q
  simp only [lam, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [mul_add, Complex.conj_ofReal]

section Aux

variable {ι : Type*} [Fintype ι]

/-- `v^* v = Σ |v_i|²` for a vector `v`. -/
private lemma Pathwise_dot_self (v : ι → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul']
  push_cast
  rfl

/-- `‖M v‖² = v^* M^* M v`, as complex numbers. -/
private lemma Pathwise_nsq_mulVec (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    ((∑ i, ‖(M *ᵥ v) i‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ ((Mᴴ * M) *ᵥ v) := by
  rw [← Pathwise_dot_self, star_mulVec, ← mulVec_mulVec, ← dotProduct_mulVec]

/-- Cauchy–Schwarz for the bilinear sum: `|a · b|² ≤ (Σ |a_i|²)(Σ |b_i|²)`. -/
private lemma Pathwise_dot_sq_le (a b : ι → ℂ) :
    ‖a ⬝ᵥ b‖ ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖b i‖ ^ 2 := by
  have h1 : ‖a ⬝ᵥ b‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
    refine (norm_sum_le _ _).trans ?_
    simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖a i‖) (fun i => ‖b i‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- For a unit vector `u`, `‖C u‖² ≤ Σ_{i,k} |C_{ik}|²` (the squared Hilbert–Schmidt norm). -/
private lemma Pathwise_mulVec_sq_le (C : Matrix ι ι ℂ) (u : ι → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) :
    ∑ i, ‖(C *ᵥ u) i‖ ^ 2 ≤ ∑ i, ∑ k, ‖C i k‖ ^ 2 := by
  refine Finset.sum_le_sum fun i _ => ?_
  have := Pathwise_dot_sq_le (fun k => C i k) u
  rwa [hu, mul_one] at this

/-- `tr(M M^*) = Σ_{i,k} |M_{ik}|²`. -/
private lemma Pathwise_trace_mul_conjTranspose (M : Matrix ι ι ℂ) :
    Matrix.trace (M * Mᴴ) = ((∑ i, ∑ k, ‖M i k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, Complex.mul_conj']
  push_cast
  rfl

end Aux

section Res
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For Hermitian `X` and `Im z ≠ 0`, `(res X z)^*` is the two-sided inverse of `X - z̄`. -/
private lemma Pathwise_res_conj (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    (X - (star z) • (1 : Matrix ι ι ℂ)) * (res X z)ᴴ = 1 ∧
      (res X z)ᴴ * (X - (star z) • (1 : Matrix ι ι ℂ)) = 1 := by
  obtain ⟨h1, h2⟩ := res_mul_sub_of_im_ne X hX z hz
  have e : (X - z • (1 : Matrix ι ι ℂ))ᴴ = X - (star z) • (1 : Matrix ι ι ℂ) := by
    rw [conjTranspose_sub, hX.eq, conjTranspose_smul, conjTranspose_one]
  refine ⟨?_, ?_⟩
  · have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, e, conjTranspose_one] at this
  · have := congrArg conjTranspose h1
    rwa [conjTranspose_mul, e, conjTranspose_one] at this

/-- For Hermitian `X` and `Im z ≠ 0`, `Im G(z) = (Im z) G(z) G(z)^*`, where `G = (X - z)⁻¹`
of (2.12) [def_resolv]. -/
private lemma Pathwise_imRes_eq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    imRes X z = (z.im : ℂ) • (res X z * (res X z)ᴴ) := by
  obtain ⟨h1, h2⟩ := res_mul_sub_of_im_ne X hX z hz
  obtain ⟨h3, h4⟩ := Pathwise_res_conj X hX z hz
  have e : res X z - (res X z)ᴴ = (z - star z) • (res X z * (res X z)ᴴ) := by
    calc res X z - (res X z)ᴴ
        = res X z * ((X - (star z) • (1 : Matrix ι ι ℂ)) * (res X z)ᴴ) -
          (res X z * (X - z • (1 : Matrix ι ι ℂ))) * (res X z)ᴴ := by
          rw [h3, h2]; simp
      _ = (z - star z) • (res X z * (res X z)ᴴ) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, Matrix.mul_smul,
            Matrix.smul_mul, Matrix.mul_one, sub_smul]
          abel
  unfold imRes
  rw [e, smul_smul]
  have hz2 : z - star z = (2 * Complex.I) * (z.im : ℂ) := by
    apply Complex.ext
    · simp
    · simp; ring
  rw [hz2, ← mul_assoc, inv_mul_cancel₀ (by simp), one_mul]

/-- If `X u = μ u` for real `μ` and `Im z ≠ 0`, then `(X - z)⁻¹ u = (μ - z)⁻¹ u`. -/
private lemma Pathwise_res_mulVec_eigvec (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ)
    (hz : z.im ≠ 0) (μ : ℝ) (u : ι → ℂ) (hu : X *ᵥ u = (μ : ℂ) • u) :
    res X z *ᵥ u = ((μ : ℂ) - z)⁻¹ • u := by
  obtain ⟨h1, h2⟩ := res_mul_sub_of_im_ne X hX z hz
  have hne : (μ : ℂ) - z ≠ 0 := by
    intro h
    apply hz
    have := congrArg Complex.im h
    simpa using this.symm
  have h3 : (X - z • (1 : Matrix ι ι ℂ)) *ᵥ u = ((μ : ℂ) - z) • u := by
    rw [Matrix.sub_mulVec, hu, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
  have h4 : u = ((μ : ℂ) - z) • (res X z *ᵥ u) := by
    calc u = (res X z * (X - z • (1 : Matrix ι ι ℂ))) *ᵥ u := by rw [h2, Matrix.one_mulVec]
      _ = res X z *ᵥ ((X - z • (1 : Matrix ι ι ℂ)) *ᵥ u) := by rw [Matrix.mulVec_mulVec]
      _ = ((μ : ℂ) - z) • (res X z *ᵥ u) := by rw [h3, Matrix.mulVec_smul]
  have h5 : ((μ : ℂ) - z)⁻¹ • u = res X z *ᵥ u := by
    conv_lhs => rw [h4]
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  exact h5.symm



omit [DecidableEq ι] in
/-- For a Hermitian `B` and real `η`,
`tr(η G₀G₀^* B η G₁G₁^* B) = η² ‖G₀^* B G₁‖²_HS` (real part). -/
private lemma Pathwise_trace_form (G₀ G₁ B : Matrix ι ι ℂ) (hB : B.IsHermitian) (η : ℝ) :
    (Matrix.trace (((η : ℂ) • (G₀ * G₀ᴴ)) * B * ((η : ℂ) • (G₁ * G₁ᴴ)) * B)).re =
      η ^ 2 * ∑ i, ∑ k, ‖(G₀ᴴ * B * G₁) i k‖ ^ 2 := by
  have hMh : (G₀ᴴ * B * G₁)ᴴ = G₁ᴴ * B * G₀ := by
    rw [conjTranspose_mul, conjTranspose_mul, hB.eq, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have h1 : ((η : ℂ) • (G₀ * G₀ᴴ)) * B * ((η : ℂ) • (G₁ * G₁ᴴ)) * B =
      ((η : ℂ) ^ 2) • (G₀ * (G₀ᴴ * B * G₁ * (G₁ᴴ * B))) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, sq]
  have h2 : Matrix.trace (G₀ * (G₀ᴴ * B * G₁ * (G₁ᴴ * B))) =
      Matrix.trace ((G₀ᴴ * B * G₁) * (G₀ᴴ * B * G₁)ᴴ) := by
    rw [Matrix.trace_mul_comm, hMh]
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_smul, h2, Pathwise_trace_mul_conjTranspose]
  simp [smul_eq_mul, ← Complex.ofReal_pow]

end Res


section Block
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For Hermitian `S` and real `ρ`, `‖(S + iρ) s‖² = ‖S s‖² + ρ² ‖s‖²`. -/
private lemma Pathwise_nsq_shift (S : Matrix ι ι ℂ) (hS : S.IsHermitian) (ρ : ℝ) (s : ι → ℂ) :
    ∑ i, ‖((S + ((ρ : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)) *ᵥ s) i‖ ^ 2 =
      (∑ i, ‖(S *ᵥ s) i‖ ^ 2) + ρ ^ 2 * ∑ i, ‖s i‖ ^ 2 := by
  apply Complex.ofReal_injective
  have e1 := Pathwise_nsq_mulVec (S + ((ρ : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)) s
  have e2 := Pathwise_nsq_mulVec S s
  have e3 := Pathwise_dot_self s
  have hm : (S + ((ρ : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ))ᴴ *
      (S + ((ρ : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)) = Sᴴ * S + ((ρ : ℂ) ^ 2) • 1 := by
    have h1 : star ((ρ : ℂ) * Complex.I) = -((ρ : ℂ) * Complex.I) := by
      simp
    have h2 : ((ρ : ℂ) * Complex.I) * -((ρ : ℂ) * Complex.I) = (ρ : ℂ) ^ 2 := by
      have := Complex.I_mul_I
      linear_combination (-(ρ : ℂ) ^ 2) * this
    have key : ∀ a b : ℂ, (S + b • (1 : Matrix ι ι ℂ)) * (S + a • (1 : Matrix ι ι ℂ)) =
        S * S + (a + b) • S + (a * b) • (1 : Matrix ι ι ℂ) := by
      intro a b
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, smul_add, smul_smul, add_smul]
      abel
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_one, hS.eq, h1, key, h2]
    simp
  rw [Complex.ofReal_add, Complex.ofReal_mul, e1, e2, ← e3, hm, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul]
  simp [smul_eq_mul]

omit [Fintype ι] in
/-- `W - x` is Hermitian for Hermitian `W` and real `x`. -/
private lemma Pathwise_hermitian_sub_smul_one (W : Matrix ι ι ℂ) (hW : W.IsHermitian) (x : ℝ) :
    (W - (x : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_sub, hW.eq, conjTranspose_smul, conjTranspose_one]
  simp

/-- `|a + b|² ≤ 2|a|² + 2|b|²`. -/
private lemma Pathwise_norm_add_sq_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b, norm_nonneg (a + b)]

/-- Core inequality of one block: if `T p = -(T + d + iη) q` for the Hermitian `T = W - x` and
`‖T s‖ ≥ w₀ ‖s‖`, then `‖p‖² ≤ (2 + 3η²/w₀²) ‖q‖²`. -/
private lemma Pathwise_block_ineq (W : Matrix ι ι ℂ) (hW : W.IsHermitian) (x d η w₀ : ℝ)
    (hd : d ^ 2 ≤ η ^ 2) (hw₀ : 0 < w₀)
    (hsep : ∀ s : ι → ℂ, w₀ ^ 2 * ∑ i, ‖s i‖ ^ 2 ≤
      ∑ i, ‖((W - (x : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ s) i‖ ^ 2)
    (p q : ι → ℂ)
    (hpq : (W - (x : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ p =
      -((W - (x : ℂ) • (1 : Matrix ι ι ℂ) + ((d : ℂ) + (η : ℂ) * Complex.I) • 1) *ᵥ q)) :
    ∑ i, ‖p i‖ ^ 2 ≤ (2 + 3 * η ^ 2 / w₀ ^ 2) * ∑ i, ‖q i‖ ^ 2 := by
  set T : Matrix ι ι ℂ := W - (x : ℂ) • (1 : Matrix ι ι ℂ) with hT
  have hTh : T.IsHermitian := Pathwise_hermitian_sub_smul_one W hW x
  have hinj : Function.Injective T.mulVec := by
    intro s s' h
    have h0 : T *ᵥ (s - s') = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
    have h1 := hsep (s - s')
    rw [h0] at h1
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero] at h1
    have h2 : ∑ i, ‖(s - s') i‖ ^ 2 = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg fun i _ => by positivity)
      by_contra hcon
      have := mul_pos (pow_pos hw₀ 2) (not_le.mp hcon)
      linarith
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp h2
    funext i
    have := h3 i (Finset.mem_univ i)
    have h4 : ‖(s - s') i‖ = 0 := by simpa using this
    have h5 : (s - s') i = 0 := norm_eq_zero.mp h4
    simpa [sub_eq_zero] using h5
  obtain ⟨s, hs⟩ : ∃ s, T *ᵥ s = q :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj) q
  set P : Matrix ι ι ℂ := T + ((d : ℂ) + (η : ℂ) * Complex.I) • 1 with hP
  have hcomm : T * P = P * T := by
    simp only [hP, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  have e1 : T *ᵥ (P *ᵥ s) = P *ᵥ q := by
    rw [← hs, mulVec_mulVec, mulVec_mulVec, hcomm]
  have hp : p = -(P *ᵥ s) := by
    have h1 : T *ᵥ (p + P *ᵥ s) = T *ᵥ 0 := by
      rw [Matrix.mulVec_add, Matrix.mulVec_zero, hpq, e1, neg_add_cancel]
    exact eq_neg_of_add_eq_zero_left (hinj h1)
  have hS : (T + (d : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_add, hTh.eq, conjTranspose_smul, conjTranspose_one]
    simp
  have hPs : ∑ i, ‖(P *ᵥ s) i‖ ^ 2 =
      (∑ i, ‖((T + (d : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ s) i‖ ^ 2) + η ^ 2 * ∑ i, ‖s i‖ ^ 2 := by
    have : P = (T + (d : ℂ) • (1 : Matrix ι ι ℂ)) +
        ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) := by
      rw [hP, add_assoc, ← add_smul]
    rw [this]
    exact Pathwise_nsq_shift _ hS η s
  have hSs : ∀ i, ‖((T + (d : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ s) i‖ ^ 2 ≤
      2 * ‖(T *ᵥ s) i‖ ^ 2 + 2 * (d ^ 2 * ‖s i‖ ^ 2) := by
    intro i
    have h1 : ((T + (d : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ s) i = (T *ᵥ s) i + (d : ℂ) * s i := by
      simp [Matrix.add_mulVec, Matrix.smul_mulVec]
    rw [h1]
    have h := Pathwise_norm_add_sq_le ((T *ᵥ s) i) ((d : ℂ) * s i)
    have h2 : ‖(d : ℂ) * s i‖ ^ 2 = d ^ 2 * ‖s i‖ ^ 2 := by
      rw [norm_mul]; simp [mul_pow]
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hSs i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hsep' := hsep s
  set a : ℝ := ∑ i, ‖s i‖ ^ 2 with ha
  set b : ℝ := ∑ i, ‖(T *ᵥ s) i‖ ^ 2 with hb
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun i _ => by positivity
  have hab : a ≤ b / w₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hA : η ^ 2 * a ≤ η ^ 2 * (b / w₀ ^ 2) := mul_le_mul_of_nonneg_left hab (sq_nonneg η)
  have hB : d ^ 2 * a ≤ η ^ 2 * a := mul_le_mul_of_nonneg_right hd ha0
  have hq : ∑ i, ‖q i‖ ^ 2 = b := by rw [hb, hs]
  have hpn : ∑ i, ‖p i‖ ^ 2 = ∑ i, ‖(P *ᵥ s) i‖ ^ 2 := by
    rw [hp]
    simp only [Pi.neg_apply, norm_neg]
  rw [hpn, hq, hPs]
  have hc : (2 + 3 * η ^ 2 / w₀ ^ 2) * b = 2 * b + 3 * (η ^ 2 * (b / w₀ ^ 2)) := by ring
  rw [hc]
  linarith

end Block

section Model

/-- The Wigner matrix `wig n w` is Hermitian. -/
private lemma Pathwise_wig_isHermitian (n : ℕ) (w : Coords n) : (wig n w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [wig, star_mul', Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.not_gt, h.ne']
  · subst h
    simp
  · simp [h, h.ne, h.not_gt, h.ne']

/-- The block-diagonal matrix `blockH D N w` is Hermitian. -/
private lemma Pathwise_blockH_isHermitian (D N : ℕ) (w : Fin D → Coords N) :
    (blockH D N w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  by_cases h : p.1 = q.1
  · simp only [blockH, h, ↓reduceIte]
    exact (Pathwise_wig_isHermitian N (w q.1)).apply p.2 q.2
  · have h' : ¬ q.1 = p.1 := fun e => h e.symm
    simp [blockH, h, h']

/-- The interaction `lam D N A` is Hermitian, for every `A`. -/
private lemma Pathwise_lam_isHermitian (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (lam D N A).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  simp only [lam, star_add]
  split_ifs <;> simp [add_comm]

/-- The product of `blockH` with a vector acts blockwise. -/
private lemma Pathwise_blockH_mulVec (D N : ℕ) (w : Fin D → Coords N) (v : Idx D N → ℂ)
    (b : Fin D) (j : Fin N) :
    (blockH D N w *ᵥ v) (b, j) = (wig N (w b) *ᵥ fun k => v (b, k)) j := by
  simp only [Matrix.mulVec, dotProduct, blockH, ite_mul, zero_mul, Fintype.sum_prod_type]
  simp

end Model

/-- The first inequality of (5.26) [bdwgy], for every unit eigenvector: for a Hermitian `X`, a
unit eigenvector `u` of the eigenvalue `μ`, a Hermitian `B`, `γ ∈ ℝ` and `η > 0`, with
`G = (X - γ - iη)⁻¹`, `|u^* B u|² ≤ ((μ - γ)² + η²)² η^{-2} tr(Im G B Im G B)`. -/
theorem eig_form_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X B : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hB : B.IsHermitian) (μ : ℝ) (u : ι → ℂ) (hu : IsUnitEigvec X μ u)
    (γ η : ℝ) (hη : 0 < η) :
    ‖star u ⬝ᵥ (B *ᵥ u)‖ ^ 2 ≤
      ((μ - γ) ^ 2 + η ^ 2) ^ 2 / η ^ 2 *
        (Matrix.trace (imRes X ((γ : ℂ) + (η : ℂ) * Complex.I) * B *
          imRes X ((γ : ℂ) + (η : ℂ) * Complex.I) * B)).re := by
  obtain ⟨hu1, hu2⟩ := hu
  set z : ℂ := (γ : ℂ) + (η : ℂ) * Complex.I with hzdef
  have him : z.im = η := by simp [hzdef]
  have hz : z.im ≠ 0 := by rw [him]; exact hη.ne'
  have hG : res X z *ᵥ u = ((μ : ℂ) - z)⁻¹ • u := Pathwise_res_mulVec_eigvec X hX z hz μ u hu1
  set G := res X z with hGdef
  set c : ℂ := ((μ : ℂ) - z)⁻¹ with hc
  have hQ : imRes X z = (η : ℂ) • (G * Gᴴ) := by rw [Pathwise_imRes_eq X hX z hz, him]
  rw [hQ, Pathwise_trace_form G G B hB η]
  set C := Gᴴ * B * G with hCdef
  have hR : ‖(μ : ℂ) - z‖ ^ 2 = (μ - γ) ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hzdef]
    ring
  have hRpos : 0 < (μ - γ) ^ 2 + η ^ 2 := by positivity
  have hCu : star u ⬝ᵥ (C *ᵥ u) = star c * (c * (star u ⬝ᵥ (B *ᵥ u))) := by
    have e1 : C *ᵥ u = Gᴴ *ᵥ (B *ᵥ (G *ᵥ u)) := by
      rw [hCdef, ← mulVec_mulVec, ← mulVec_mulVec]
    rw [e1, dotProduct_mulVec, ← star_mulVec, hG, star_smul, Matrix.mulVec_smul,
      smul_dotProduct, dotProduct_smul]
    simp [smul_eq_mul]
  have hnc : ‖star c * (c * (star u ⬝ᵥ (B *ᵥ u)))‖ =
      ‖star u ⬝ᵥ (B *ᵥ u)‖ / ((μ - γ) ^ 2 + η ^ 2) := by
    have hcn : ‖c‖ * ‖c‖ = ((μ - γ) ^ 2 + η ^ 2)⁻¹ := by
      rw [← sq, hc, norm_inv, inv_pow, hR]
    rw [norm_mul, norm_mul, norm_star, ← mul_assoc, hcn]
    field_simp
  have h1 := Pathwise_dot_sq_le (star u) (C *ᵥ u)
  have h2 := Pathwise_mulVec_sq_le C u hu2
  have h3 : ∑ i, ‖(star u) i‖ ^ 2 = 1 := by simpa using hu2
  rw [h3, one_mul, hCu, hnc] at h1
  have h4 := h1.trans h2
  rw [div_pow, div_le_iff₀ (by positivity)] at h4
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [h4]

/-- The pathwise form of (5.16) [eq:boundE1] and (5.18) [localized_bound_eigenvector_general_D]
for every `D ≥ 2` and every unit eigenvector: let `u` be a unit eigenvector of `H_Λ` for the
eigenvalue `μ`, `Δ, γ ∈ ℝ`, `η > 0` with `|μ - γ| ≤ η`, and `w₀ > 0` with
`‖(H_b - (μ - Δ)) v‖ ≥ w₀ ‖v‖` for every block `b ≠ a` (that is,
`dist(μ - Δ, spec H_b) ≥ w₀`). With `G₀ = (H - (γ - Δ + iη))⁻¹`, `G₁ = (H_Λ - (γ + iη))⁻¹` and
`Λ̃ = Λ - Δ`, `Σ_{b ≠ a} ‖E_b u‖² ≤ 2 (2 + 3η²/w₀²) tr(Im G₀ Λ̃ Im G₁ Λ̃)`. -/
theorem offblock_mass_le (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin D → Coords N)
    (μ : ℝ) (u : Idx D N → ℂ) (hu : IsUnitEigvec (HLam D N A w) μ u) (Δ γ η w₀ : ℝ)
    (hη : 0 < η) (hw₀ : 0 < w₀) (hμ : |μ - γ| ≤ η) (a : Fin D)
    (hsep : ∀ b : Fin D, b ≠ a → ∀ v : Fin N → ℂ,
      w₀ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤
        ∑ i, ‖((wig N (w b) - ((μ - Δ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ v) i‖ ^ 2) :
    ∑ b ∈ Finset.univ.erase a, blockMass u b ≤
      2 * (2 + 3 * η ^ 2 / w₀ ^ 2) *
        (Matrix.trace (imRes (blockH D N w) (((γ - Δ : ℝ) : ℂ) + (η : ℂ) * Complex.I) *
          (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
          imRes (HLam D N A w) ((γ : ℂ) + (η : ℂ) * Complex.I) *
          (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))).re := by
  obtain ⟨hu1, hu2⟩ := hu
  set H := blockH D N w with hH
  set L := HLam D N A w with hL
  set Lt : Matrix (Idx D N) (Idx D N) ℂ :=
    lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ) with hLt
  set z₀ : ℂ := ((γ - Δ : ℝ) : ℂ) + (η : ℂ) * Complex.I with hz₀def
  set z₁ : ℂ := (γ : ℂ) + (η : ℂ) * Complex.I with hz₁def
  have him₀ : z₀.im = η := by simp [hz₀def]
  have him₁ : z₁.im = η := by simp [hz₁def]
  have hz₀ : z₀.im ≠ 0 := by rw [him₀]; exact hη.ne'
  have hz₁ : z₁.im ≠ 0 := by rw [him₁]; exact hη.ne'
  have hHh : H.IsHermitian := Pathwise_blockH_isHermitian D N w
  have hLh : L.IsHermitian := HLam_isHermitian D N A w
  have hLth : Lt.IsHermitian := by
    have h1 : ((Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [conjTranspose_smul, conjTranspose_one]
      simp
    exact (Pathwise_lam_isHermitian D N A).sub h1
  set G₀ := res H z₀ with hG₀
  set G₁ := res L z₁ with hG₁
  have htr : (Matrix.trace (imRes H z₀ * Lt * imRes L z₁ * Lt)).re =
      η ^ 2 * ∑ i, ∑ k, ‖(G₀ᴴ * Lt * G₁) i k‖ ^ 2 := by
    rw [Pathwise_imRes_eq H hHh z₀ hz₀, Pathwise_imRes_eq L hLh z₁ hz₁, him₀, him₁]
    exact Pathwise_trace_form G₀ G₁ Lt hLth η
  rw [htr]
  have hG₁u : G₁ *ᵥ u = ((μ : ℂ) - z₁)⁻¹ • u := Pathwise_res_mulVec_eigvec L hLh z₁ hz₁ μ u hu1
  set c : ℂ := ((μ : ℂ) - z₁)⁻¹ with hc
  set y : Idx D N → ℂ := Lt *ᵥ u with hy
  set v : Idx D N → ℂ := G₀ᴴ *ᵥ y with hv
  have hMu : (G₀ᴴ * Lt * G₁) *ᵥ u = c • v := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hG₁u, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hR : ‖(μ : ℂ) - z₁‖ ^ 2 = (μ - γ) ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hz₁def]
    ring
  have hRpos : 0 < (μ - γ) ^ 2 + η ^ 2 := by positivity
  have hcR : ‖c‖ ^ 2 * ((μ - γ) ^ 2 + η ^ 2) = 1 := by
    rw [hc, norm_inv, inv_pow, hR]
    exact inv_mul_cancel₀ hRpos.ne'
  have hd : (μ - γ) ^ 2 ≤ η ^ 2 := sq_le_sq' (abs_le.mp hμ).1 (abs_le.mp hμ).2
  -- the mass of `v`
  set HS : ℝ := ∑ i, ∑ k, ‖(G₀ᴴ * Lt * G₁) i k‖ ^ 2 with hHS
  have hvle : ∑ i, ‖v i‖ ^ 2 ≤ 2 * (η ^ 2 * HS) := by
    have h1 := Pathwise_mulVec_sq_le (G₀ᴴ * Lt * G₁) u hu2
    rw [hMu] at h1
    have h2 : ∑ i, ‖(c • v) i‖ ^ 2 = ‖c‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    rw [h2] at h1
    have hHS0 : 0 ≤ HS := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity
    have h3 : ∑ i, ‖v i‖ ^ 2 = ((μ - γ) ^ 2 + η ^ 2) * (‖c‖ ^ 2 * ∑ i, ‖v i‖ ^ 2) := by
      rw [← mul_assoc, mul_comm _ (‖c‖ ^ 2), hcR, one_mul]
    rw [h3]
    calc ((μ - γ) ^ 2 + η ^ 2) * (‖c‖ ^ 2 * ∑ i, ‖v i‖ ^ 2) ≤ ((μ - γ) ^ 2 + η ^ 2) * HS :=
          mul_le_mul_of_nonneg_left h1 hRpos.le
      _ ≤ (2 * η ^ 2) * HS := mul_le_mul_of_nonneg_right (by linarith) hHS0
      _ = 2 * (η ^ 2 * HS) := by ring
  -- the block equations
  have hv_eq : (H - (star z₀) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *ᵥ v = y := by
    rw [hv, mulVec_mulVec, (Pathwise_res_conj H hHh z₀ hz₀).1, Matrix.one_mulVec]
  have hu_eq : (H - (((μ - Δ : ℝ) : ℂ)) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *ᵥ u = -y := by
    have h1 : H *ᵥ u + lam D N A *ᵥ u = (μ : ℂ) • u := by
      rw [← Matrix.add_mulVec]; exact hu1
    rw [hy, hLt, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    have h2 : H *ᵥ u = (μ : ℂ) • u - lam D N A *ᵥ u := eq_sub_of_add_eq h1
    rw [h2]
    push_cast
    module
  have hblock : ∀ b : Fin D, b ≠ a →
      ∑ j, ‖u (b, j)‖ ^ 2 ≤ (2 + 3 * η ^ 2 / w₀ ^ 2) * ∑ j, ‖v (b, j)‖ ^ 2 := by
    intro b hb
    refine Pathwise_block_ineq (wig N (w b)) (Pathwise_wig_isHermitian N (w b)) (μ - Δ) (μ - γ)
      η w₀ hd hw₀ (hsep b hb) (fun j => u (b, j)) (fun j => v (b, j)) ?_
    funext j
    have e1 := congrFun hu_eq (b, j)
    have e2 := congrFun hv_eq (b, j)
    rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
      hH, Pathwise_blockH_mulVec] at e1 e2
    have hz : star z₀ = ((μ - Δ : ℝ) : ℂ) - (((μ - γ : ℝ) : ℂ) + (η : ℂ) * Complex.I) := by
      simp only [hz₀def, Complex.star_def, map_add, map_mul, Complex.conj_ofReal,
        Complex.conj_I]
      push_cast
      ring
    rw [hz] at e2
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at e1 e2 ⊢
    linear_combination e1 + e2
  have hsumv : ∑ i, ‖v i‖ ^ 2 = ∑ b, ∑ j, ‖v (b, j)‖ ^ 2 := by rw [Fintype.sum_prod_type]
  have hK : 0 ≤ 2 + 3 * η ^ 2 / w₀ ^ 2 := by positivity
  calc ∑ b ∈ Finset.univ.erase a, blockMass u b
      ≤ ∑ b ∈ Finset.univ.erase a, (2 + 3 * η ^ 2 / w₀ ^ 2) * ∑ j, ‖v (b, j)‖ ^ 2 :=
        Finset.sum_le_sum fun b hb => hblock b (Finset.ne_of_mem_erase hb)
    _ = (2 + 3 * η ^ 2 / w₀ ^ 2) * ∑ b ∈ Finset.univ.erase a, ∑ j, ‖v (b, j)‖ ^ 2 := by
        rw [← Finset.mul_sum]
    _ ≤ (2 + 3 * η ^ 2 / w₀ ^ 2) * ∑ b, ∑ j, ‖v (b, j)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => Finset.sum_nonneg fun _ _ => by positivity)) hK
    _ ≤ (2 + 3 * η ^ 2 / w₀ ^ 2) * (2 * (η ^ 2 * HS)) := by
        rw [← hsumv]
        exact mul_le_mul_of_nonneg_left hvle hK
    _ = 2 * (2 + 3 * η ^ 2 / w₀ ^ 2) * (η ^ 2 * HS) := by ring

end RBMTransitionEdge

end
