module

public import RBMTransitionEdge.Model.Basic

@[expose] public section

/-!
# The resolvent (2.12)

The resolvent `G(z) = (X - z)⁻¹` of (2.12) [def_resolv] for a Hermitian matrix `X` and `Im z > 0`: a true inverse, the bound
`‖G‖ ≤ η⁻¹`, `G(z̄) = G(z)^*`, the resolvent identity, the Lipschitz bound in `z` and `∂_z G = G²`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped NNReal ENNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The resolvent `G(z) = (X - z)⁻¹` of (2.12) [def_resolv] (the matrix inverse; for Hermitian
`X` and `Im z > 0` it is a true inverse). -/
def res (X : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ := (X - z • (1 : Matrix ι ι ℂ))⁻¹

/-- The operator norm is submultiplicative. -/
private lemma Resolvent_opNorm_mul_le (A B : Matrix ι ι ℂ) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  unfold opNorm
  rw [map_mul]
  exact norm_mul_le _ _

/-- The operator norm of a scalar multiple. -/
private lemma Resolvent_opNorm_smul (c : ℂ) (A : Matrix ι ι ℂ) :
    opNorm (c • A) = ‖c‖ * opNorm A := by
  unfold opNorm
  rw [map_smul, norm_smul]

/-- An entry is bounded by the operator norm. -/
private lemma Resolvent_norm_apply_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
  unfold opNorm
  have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  have h2 : ‖(EuclideanSpace.single j (1 : ℂ))‖ = 1 := by simp
  rw [h2, mul_one] at h1
  have h3 : A i j = ((Matrix.toEuclideanCLM (𝕜 := ℂ) A) (EuclideanSpace.single j (1 : ℂ))) i := by
    simp [Matrix.mulVec_single]
  rw [h3]
  exact (PiLp.norm_apply_le _ i).trans h1

/-- Key estimate (L): `η ‖v‖ ≤ ‖(X - z) v‖` for Hermitian `X`, `z = E + iη`. -/
private lemma Resolvent_key (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ)
    (v : EuclideanSpace ℂ ι) :
    z.im * ‖v‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X - z • (1 : Matrix ι ι ℂ)) v‖ := by
  have hsym : (inner ℂ v (Matrix.toEuclideanLin X v)).im = 0 := by
    simpa using (Matrix.isSymmetric_toEuclideanLin_iff.mpr hX).im_inner_self_apply v
  have hu : Matrix.toEuclideanCLM (𝕜 := ℂ) (X - z • (1 : Matrix ι ι ℂ)) v
      = Matrix.toEuclideanLin X v - z • v := by
    rw [map_sub, map_smul, map_one]
    rfl
  rw [hu]
  have him : (inner ℂ v (Matrix.toEuclideanLin X v - z • v)).im = - (z.im * ‖v‖ ^ 2) := by
    rw [inner_sub_right, inner_smul_right, Complex.sub_im, hsym, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_im]
    norm_cast
    simp
  have h1 : |(inner ℂ v (Matrix.toEuclideanLin X v - z • v)).im| ≤
      ‖v‖ * ‖Matrix.toEuclideanLin X v - z • v‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  rw [him, abs_neg] at h1
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · have h2 : z.im * ‖v‖ ^ 2 ≤ |z.im * ‖v‖ ^ 2| := le_abs_self _
    refine le_of_mul_le_mul_left ?_ hpos
    nlinarith [h1, h2]

/-- `X - z` is invertible for Hermitian `X` and `Im z > 0`. -/
private lemma Resolvent_isUnit (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    IsUnit (X - z • (1 : Matrix ι ι ℂ)) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have h : (X - z • (1 : Matrix ι ι ℂ)) *ᵥ (a - b) = 0 := by
    rw [Matrix.mulVec_sub, hab, sub_self]
  have key := Resolvent_key X hX z (WithLp.toLp 2 (a - b))
  have h0 : Matrix.toEuclideanCLM (𝕜 := ℂ) (X - z • (1 : Matrix ι ι ℂ))
      (WithLp.toLp 2 (a - b)) = 0 := by
    rw [Matrix.toEuclideanCLM_toLp, h]
    rfl
  rw [h0, norm_zero] at key
  have hn : ‖(WithLp.toLp 2 (a - b) : EuclideanSpace ℂ ι)‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    by_contra hc
    rw [not_le] at hc
    nlinarith [mul_pos hz hc]
  rw [norm_eq_zero] at hn
  exact sub_eq_zero.mp (by simpa using congrArg WithLp.ofLp hn)

/-- `(X - z) G(z) = G(z) (X - z) = 1` for Hermitian `X` and `Im z > 0`. -/
theorem res_mul_sub (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    (X - z • (1 : Matrix ι ι ℂ)) * res X z = 1 ∧ res X z * (X - z • (1 : Matrix ι ι ℂ)) = 1 := by
  have h := (Matrix.isUnit_iff_isUnit_det _).mp (Resolvent_isUnit X hX z hz)
  exact ⟨Matrix.mul_nonsing_inv _ h, Matrix.nonsing_inv_mul _ h⟩

/-- `‖G(z)‖ ≤ (Im z)⁻¹`. -/
theorem opNorm_res_le (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    opNorm (res X z) ≤ z.im⁻¹ := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hz.le) fun u => ?_
  have h1 := (res_mul_sub X hX z hz).1
  have h2 : Matrix.toEuclideanCLM (𝕜 := ℂ) (X - z • (1 : Matrix ι ι ℂ))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (res X z) u) = u := by
    rw [← mul_apply_eq_comp, ← map_mul, h1, map_one]
    rfl
  have key := Resolvent_key X hX z (Matrix.toEuclideanCLM (𝕜 := ℂ) (res X z) u)
  rw [h2] at key
  rw [inv_mul_eq_div, le_div_iff₀ hz]
  linarith

/-- `G(z̄) = G(z)*`. -/
theorem res_conj (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    res X (starRingEnd ℂ z) = (res X z)ᴴ := by
  unfold res
  rw [Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, hX.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  rfl

/-- The resolvent identity `G(z) - G(w) = (z - w) G(z) G(w)`. -/
theorem res_sub_res (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z w : ℂ) (hz : 0 < z.im)
    (hw : 0 < w.im) : res X z - res X w = (z - w) • (res X z * res X w) := by
  obtain ⟨hz1, hz2⟩ := res_mul_sub X hX z hz
  obtain ⟨hw1, hw2⟩ := res_mul_sub X hX w hw
  have e : res X z - res X w
      = res X z * ((X - w • (1 : Matrix ι ι ℂ)) - (X - z • (1 : Matrix ι ι ℂ))) * res X w := by
    rw [mul_sub, sub_mul, hz2, one_mul, mul_assoc, hw1, mul_one]
  rw [e]
  have : (X - w • (1 : Matrix ι ι ℂ)) - (X - z • (1 : Matrix ι ι ℂ)) =
      (z - w) • (1 : Matrix ι ι ℂ) := by
    rw [sub_smul]
    abel
  rw [this, mul_smul_comm, smul_mul_assoc, mul_one]

/-- `‖G(z) - G(w)‖ ≤ |z - w| / (Im z Im w)`. -/
theorem opNorm_res_sub_le (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z w : ℂ) (hz : 0 < z.im)
    (hw : 0 < w.im) : opNorm (res X z - res X w) ≤ ‖z - w‖ / (z.im * w.im) := by
  rw [res_sub_res X hX z w hz hw, Resolvent_opNorm_smul]
  have h1 := opNorm_res_le X hX z hz
  have h2 := opNorm_res_le X hX w hw
  have h3 := Resolvent_opNorm_mul_le (res X z) (res X w)
  have h4 : opNorm (res X z) * opNorm (res X w) ≤ z.im⁻¹ * w.im⁻¹ :=
    mul_le_mul h1 h2 (by unfold opNorm; exact norm_nonneg _) (inv_nonneg.mpr hz.le)
  calc ‖z - w‖ * opNorm (res X z * res X w) ≤ ‖z - w‖ * (z.im⁻¹ * w.im⁻¹) :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (norm_nonneg _)
    _ = ‖z - w‖ / (z.im * w.im) := by
        field_simp

/-- Analyticity: every entry of `G` has complex derivative `(G²)_{ij}`, so `‖∂_z G‖ ≤ η⁻²`. -/
theorem hasDerivAt_res (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (i j : ι) : HasDerivAt (fun w => res X w i j) ((res X z * res X z) i j) z := by
  have hev : ∀ᶠ w in nhds z, 0 < w.im :=
    Complex.continuous_im.continuousAt.eventually (lt_mem_nhds hz)
  have hcont : ∀ k l : ι, ContinuousAt (fun w => res X w k l) z := by
    intro k l
    have hg : Tendsto (fun w : ℂ => ‖z - w‖ / (z.im * w.im)) (nhds z) (nhds 0) := by
      have hc : ContinuousAt (fun w : ℂ => ‖z - w‖ / (z.im * w.im)) z := by
        refine ContinuousAt.div (continuous_const.sub continuous_id).norm.continuousAt
          (continuousAt_const.mul Complex.continuous_im.continuousAt) ?_
        exact (mul_pos hz hz).ne'
      simpa using hc.tendsto
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
    filter_upwards [hev] with w hw
    calc ‖res X w k l - res X z k l‖ = ‖(res X z - res X w) k l‖ := by
          rw [Matrix.sub_apply, norm_sub_rev]
      _ ≤ opNorm (res X z - res X w) := Resolvent_norm_apply_le _ k l
      _ ≤ ‖z - w‖ / (z.im * w.im) := opNorm_res_sub_le X hX z w hz hw
  have hprod : Tendsto (fun w => (res X z * res X w) i j) (nhds z)
      (nhds ((res X z * res X z) i j)) := by
    simp only [Matrix.mul_apply]
    exact tendsto_finsetSum _ fun k _ => (hcont k j).tendsto.const_mul _
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hprod.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev, self_mem_nhdsWithin] with w hw hne
  have hne' : w - z ≠ 0 := sub_ne_zero.mpr hne
  have h := congrFun (congrFun (res_sub_res X hX w z hw hz) i) j
  have h' := congrFun (congrFun (res_sub_res X hX z w hz hw) i) j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h h'
  rw [slope_def_field]
  field_simp
  linear_combination h'

end RBMTransitionEdge

end
