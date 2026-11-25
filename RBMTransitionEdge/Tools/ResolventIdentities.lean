module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Tools.Resolvent

@[expose] public section

/-!
# Resolvent identities: (2.25), Ward, spectral form

The identity (2.25) [eq:G-M] `G − M = −G(H + m)M`, the Ward identities (2.31) [eq_Ward0] and
(2.32) [eq_Ward], the spectral form of `G` and `Im G`, and the elementary bounds for the operator
norm.
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped NNReal ENNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal-form helper behind the spectral forms: for Hermitian `X` with `Im z > 0`,
`G(z) = U diag((λ_k - z)⁻¹) U*` with `U` the eigenvector unitary. -/
private lemma ResolventIdentities_res_eq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) :
    res X z = (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun k => ((hX.eigenvalues k : ℂ) - z)⁻¹) *
      star (hX.eigenvectorUnitary : Matrix ι ι ℂ) := by
  set U : Matrix ι ι ℂ := (hX.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self hX.eigenvectorUnitary
  have hUU' : star U * U = 1 := Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have hspec : X = U * Matrix.diagonal (fun k => (hX.eigenvalues k : ℂ)) * star U := by
    have h := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hne : ∀ k, ((hX.eigenvalues k : ℂ) - z) ≠ 0 := by
    intro k h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h1 : X - z • (1 : Matrix ι ι ℂ) =
      U * Matrix.diagonal (fun k => (hX.eigenvalues k : ℂ) - z) * star U := by
    have : Matrix.diagonal (fun k => (hX.eigenvalues k : ℂ) - z) =
        Matrix.diagonal (fun k => (hX.eigenvalues k : ℂ)) - z • (1 : Matrix ι ι ℂ) := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab]
    rw [this, mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, hUU, ← hspec]
  have h2 : (X - z • (1 : Matrix ι ι ℂ)) * (U * Matrix.diagonal (fun k => ((hX.eigenvalues k : ℂ) - z)⁻¹) * star U) = 1 := by
    rw [h1]
    calc U * Matrix.diagonal (fun k => (hX.eigenvalues k : ℂ) - z) * star U *
          (U * Matrix.diagonal (fun k => ((hX.eigenvalues k : ℂ) - z)⁻¹) * star U)
        = U * (Matrix.diagonal (fun k => (hX.eigenvalues k : ℂ) - z) * (star U * U) *
            Matrix.diagonal (fun k => ((hX.eigenvalues k : ℂ) - z)⁻¹)) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hUU', Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          have : (fun k => ((hX.eigenvalues k : ℂ) - z) * ((hX.eigenvalues k : ℂ) - z)⁻¹) =
              fun _ => (1 : ℂ) := by
            funext k; exact mul_inv_cancel₀ (hne k)
          rw [this, Matrix.diagonal_one, Matrix.mul_one, hUU]
  unfold res
  exact Matrix.inv_eq_right_inv h2

/-- The Hermitian conjugate form: `G - G* = 2iη G*G = 2iη GG*` for Hermitian `X`, `Im z > 0`. -/
private lemma ResolventIdentities_ward_key (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) :
    res X z - (res X z)ᴴ = (2 * Complex.I * z.im) • ((res X z)ᴴ * res X z) ∧
      res X z - (res X z)ᴴ = (2 * Complex.I * z.im) • (res X z * (res X z)ᴴ) := by
  obtain ⟨h1, h2⟩ := res_mul_sub X hX z hz
  have h1' := congrArg Matrix.conjTranspose h1
  have h2' := congrArg Matrix.conjTranspose h2
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hX.eq,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one] at h1' h2'
  have hc : z - starRingEnd ℂ z = 2 * Complex.I * z.im := by
    rw [Complex.sub_conj]; push_cast; ring
  have hsm : (X - star z • (1 : Matrix ι ι ℂ)) - (X - z • (1 : Matrix ι ι ℂ)) =
      (2 * Complex.I * z.im) • (1 : Matrix ι ι ℂ) := by
    rw [← hc, sub_sub_sub_cancel_left, ← sub_smul]
    rfl
  set R := res X z with hR
  set P := X - star z • (1 : Matrix ι ι ℂ) with hP
  set Q := X - z • (1 : Matrix ι ι ℂ) with hQ
  have e1 : R - Rᴴ = Rᴴ * (P - Q) * R := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc Rᴴ Q R, h1, Matrix.mul_one, h1',
      Matrix.one_mul]
  have e2 : R - Rᴴ = R * (P - Q) * Rᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc R P Rᴴ, h2', Matrix.mul_one,
      h2, Matrix.one_mul]
  rw [hsm] at e1 e2
  refine ⟨?_, ?_⟩
  · rw [e1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  · rw [e2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- (2.25) [eq:G-M]: with `M = (Λ - z - m)⁻¹` (the solution of (2.13) [def_M] when
`𝒮(M) = m`), `G - M = -G(H + m)M = -M(H + m)G`, for Hermitian `H`, `Λ`, `Im z > 0`, `Im m ≥ 0`. -/
theorem res_sub_dyson (H Λ : Matrix ι ι ℂ) (hH : H.IsHermitian) (hΛ : Λ.IsHermitian) (z m : ℂ)
    (hz : 0 < z.im) (hm : 0 ≤ m.im) :
    res (H + Λ) z - (Λ - (z + m) • (1 : Matrix ι ι ℂ))⁻¹ =
        -(res (H + Λ) z * (H + m • (1 : Matrix ι ι ℂ)) * (Λ - (z + m) • (1 : Matrix ι ι ℂ))⁻¹) ∧
      res (H + Λ) z - (Λ - (z + m) • (1 : Matrix ι ι ℂ))⁻¹ =
        -((Λ - (z + m) • (1 : Matrix ι ι ℂ))⁻¹ * (H + m • (1 : Matrix ι ι ℂ)) * res (H + Λ) z) := by
  have hHΛ : (H + Λ).IsHermitian := hH.add hΛ
  have hzm : 0 < (z + m).im := by rw [Complex.add_im]; linarith
  obtain ⟨hA1, hA2⟩ := res_mul_sub (H + Λ) hHΛ z hz
  obtain ⟨hB1, hB2⟩ := res_mul_sub Λ hΛ (z + m) hzm
  have hM : res Λ (z + m) = (Λ - (z + m) • (1 : Matrix ι ι ℂ))⁻¹ := rfl
  rw [← hM]
  have hd : (Λ - (z + m) • (1 : Matrix ι ι ℂ)) - ((H + Λ) - z • (1 : Matrix ι ι ℂ)) =
      -(H + m • (1 : Matrix ι ι ℂ)) := by
    rw [add_smul]; abel
  set G := res (H + Λ) z with hG
  set M := res Λ (z + m) with hMdef
  set A := (H + Λ) - z • (1 : Matrix ι ι ℂ) with hAdef
  set B := Λ - (z + m) • (1 : Matrix ι ι ℂ) with hBdef
  have e1 : G - M = G * (B - A) * M := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc G B M, hB1, Matrix.mul_one,
      Matrix.mul_assoc G A M, ← Matrix.mul_assoc G A M, hA2, Matrix.one_mul]
  have e2 : G - M = M * (B - A) * G := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hB2, Matrix.one_mul,
      Matrix.mul_assoc M A G, hA1, Matrix.mul_one]
  rw [hd] at e1 e2
  refine ⟨?_, ?_⟩
  · rw [e1, Matrix.mul_neg, Matrix.neg_mul]
  · rw [e2, Matrix.mul_neg, Matrix.neg_mul]

/-- (2.31) [eq_Ward0]: `Σ_x conj(R_{xy'}) R_{xy} = (R_{y'y} - conj R_{yy'}) / (2iη)` and
`Σ_x conj(R_{y'x}) R_{yx} = (R_{yy'} - conj R_{y'y}) / (2iη)`. -/
theorem ward_sum (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (y y' : ι) :
    ∑ x, starRingEnd ℂ (res X z x y') * res X z x y =
        (res X z y' y - starRingEnd ℂ (res X z y y')) / (2 * Complex.I * z.im) ∧
      ∑ x, starRingEnd ℂ (res X z y' x) * res X z y x =
        (res X z y y' - starRingEnd ℂ (res X z y' y)) / (2 * Complex.I * z.im) := by
  obtain ⟨k1, k2⟩ := ResolventIdentities_ward_key X hX z hz
  have hne : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by
    have : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
    simp [this]
  refine ⟨?_, ?_⟩
  · have h := congrFun (congrFun k1 y') y
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.star_def] at h
    rw [eq_div_iff hne, mul_comm]
    exact h.symm
  · have h := congrFun (congrFun k2 y) y'
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.star_def] at h
    rw [eq_div_iff hne, mul_comm]
    simp only [mul_comm (starRingEnd ℂ _) (res X z y _)]
    exact h.symm

/-- (2.32) [eq_Ward]: `Σ_x |R_{xy}|² = Σ_x |R_{yx}|² = Im R_{yy} / η`. -/
theorem ward_diag (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (y : ι) :
    ∑ x, ‖res X z x y‖ ^ 2 = (res X z y y).im / z.im ∧
      ∑ x, ‖res X z y x‖ ^ 2 = (res X z y y).im / z.im := by
  obtain ⟨w1, w2⟩ := ward_sum X hX z hz y y
  have hη : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hrhs : (res X z y y - starRingEnd ℂ (res X z y y)) / (2 * Complex.I * z.im) =
      (((res X z y y).im / z.im : ℝ) : ℂ) := by
    rw [Complex.sub_conj]
    push_cast
    field_simp
  rw [hrhs] at w1 w2
  refine ⟨?_, ?_⟩
  · apply Complex.ofReal_injective
    rw [← w1]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.conj_mul']
  · apply Complex.ofReal_injective
    rw [← w2]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.conj_mul']

/-- `G_{ij} = Σ_k v_k(i) conj(v_k(j)) / (λ_k - z)`, with `v_k` the columns of the eigenvector
unitary. -/
theorem res_eq_sum_eig (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (i j : ι) :
    res X z i j = ∑ k, (hX.eigenvectorUnitary : Matrix ι ι ℂ) i k *
      starRingEnd ℂ ((hX.eigenvectorUnitary : Matrix ι ι ℂ) j k) / ((hX.eigenvalues k : ℂ) - z) := by
  rw [ResolventIdentities_res_eq X hX z hz]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [div_eq_mul_inv, mul_assoc]
  left
  ring

/-- `(Im G)_{ij} = Σ_k v_k(i) conj(v_k(j)) η / |λ_k - z|²`, where `Im G = (G - G*) / (2i)`. -/
theorem imRes_eq_sum_eig (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (i j : ι) :
    ((2 * Complex.I)⁻¹ • (res X z - (res X z)ᴴ)) i j = ∑ k, (hX.eigenvectorUnitary : Matrix ι ι ℂ) i k *
      starRingEnd ℂ ((hX.eigenvectorUnitary : Matrix ι ι ℂ) j k) *
        ((z.im / ‖(hX.eigenvalues k : ℂ) - z‖ ^ 2 : ℝ) : ℂ) := by
  have hji := res_eq_sum_eig X hX z hz j i
  have hij := res_eq_sum_eig X hX z hz i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Complex.star_def,
    smul_eq_mul]
  rw [hij, hji, map_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set a := (hX.eigenvectorUnitary : Matrix ι ι ℂ) i k with ha
  set b := (hX.eigenvectorUnitary : Matrix ι ι ℂ) j k with hb
  set w : ℂ := (hX.eigenvalues k : ℂ) - z with hw
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hw] at this
    linarith
  have hcw : starRingEnd ℂ w = (hX.eigenvalues k : ℂ) - starRingEnd ℂ z := by
    rw [hw, map_sub, Complex.conj_ofReal]
  have hcw0 : starRingEnd ℂ w ≠ 0 := by simpa using hw0
  have hnorm : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * starRingEnd ℂ w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hη : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hnz : ((‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [hnorm]; exact mul_ne_zero hw0 hcw0
  have hdiff : starRingEnd ℂ w - w = 2 * Complex.I * z.im := by
    have h := Complex.sub_conj z
    rw [hcw, hw]
    have : (hX.eigenvalues k : ℂ) - starRingEnd ℂ z - ((hX.eigenvalues k : ℂ) - z) =
        z - starRingEnd ℂ z := by ring
    rw [this, h]
    push_cast
    ring
  rw [map_div₀, map_mul, Complex.conj_conj, Complex.ofReal_div, hnorm]
  have e : a * starRingEnd ℂ b / w - starRingEnd ℂ b * a / starRingEnd ℂ w =
      a * starRingEnd ℂ b * (starRingEnd ℂ w - w) / (w * starRingEnd ℂ w) := by
    field_simp
  rw [e, hdiff]
  field_simp

/-- The operator norm `‖·‖` is submultiplicative (used throughout §2.3 with (2.25) [eq:G-M]). -/
theorem opNorm_mul_le (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  unfold opNorm
  rw [map_mul]
  exact norm_mul_le _ _

/-- The triangle inequality for the operator norm `‖·‖`. -/
theorem opNorm_add_le (A B : Matrix ι ι ℂ) : opNorm (A + B) ≤ opNorm A + opNorm B := by
  unfold opNorm
  rw [map_add]
  exact norm_add_le _ _

/-- `‖c A‖ = |c| ‖A‖` for the operator norm. -/
theorem opNorm_smul (c : ℂ) (A : Matrix ι ι ℂ) : opNorm (c • A) = ‖c‖ * opNorm A := by
  unfold opNorm
  rw [map_smul, norm_smul]

/-- An entry is bounded by the operator norm: `|A_{ij}| ≤ ‖A‖`. -/
theorem norm_apply_le_opNorm (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
  unfold opNorm
  have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  have h2 : ‖(EuclideanSpace.single j (1 : ℂ))‖ = 1 := by simp
  rw [h2, mul_one] at h1
  have h3 : A i j = ((Matrix.toEuclideanCLM (𝕜 := ℂ) A) (EuclideanSpace.single j (1 : ℂ))) i := by
    simp [Matrix.mulVec_single]
  rw [h3]
  exact (PiLp.norm_apply_le _ i).trans h1

end RBMTransitionEdge

end
