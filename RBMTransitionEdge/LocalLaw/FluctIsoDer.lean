module

public import RBMTransitionEdge.LocalLaw.ResPolyDer
public import RBMTransitionEdge.LocalLaw.FluctPrelim

@[expose] public section

/-!
# Derivatives of the self-energy correction of the isotropic forms

The derivative of `(H̲G)_{xy}` of (2.30) [eq:HGline] in one entry and its Wirtinger derivatives
along a Hermitian slice; `(H̲G)_{xy}` as a resolvent polynomial; the bound on its
derivatives on the good event, without a bound on `‖H‖`; and the order-`k` terms of the
isotropic expansion of Lemma 2.11 [lem:complex_cumu].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The derivative of `(H̲G)_{xy}` of (2.30) [eq:HGline] in the direction `E_{ab}`:
`x̄_a (G y)_b - (H̲G)_{x e_a} (G y)_b - N⁻¹ Σ_r G_{ra} G_{br} t^r(x)^* G y`. -/
def hgDer (D N : ℕ) (θ : ℝ) (H Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (x y : Idx D N → ℂ)
    (a b : Idx D N) : ℂ :=
  starRingEnd ℂ (x a) * (res (H + Λ) z *ᵥ y) b -
    (star x ⬝ᵥ (hgUnder D N θ H Λ z *ᵥ Pi.single a 1)) * (res (H + Λ) z *ᵥ y) b -
    (N : ℂ)⁻¹ * ∑ r, res (H + Λ) z r a * res (H + Λ) z b r *
      (star (tiltV D N θ x r) ⬝ᵥ (res (H + Λ) z *ᵥ y))

private lemma FID_slice_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  have := symArr_isHermitian (setEntry h i j w)
  rwa [symArr_setEntry, symArr_of_isHermitian h hh] at this

private lemma FID_cs {ι : Type*} [Fintype ι] (x w : ι → ℂ) :
    ‖star x ⬝ᵥ w‖ ≤ Real.sqrt (∑ k, ‖x k‖ ^ 2) * Real.sqrt (∑ k, ‖w k‖ ^ 2) := by
  calc ‖star x ⬝ᵥ w‖ = ‖∑ k, star (x k) * w k‖ := rfl
    _ ≤ ∑ k, ‖star (x k) * w k‖ := norm_sum_le _ _
    _ = ∑ k, ‖x k‖ * ‖w k‖ := by simp
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

private lemma FID_sTheta_diag (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ) :
    sTheta D N θ R = Matrix.diagonal (fun k : Idx D N =>
      ∑ r, ((varProf D N θ k r : ℝ) : ℂ) * R r r) := by
  ext p q
  by_cases h : p = q
  · subst h
    have h1 : sTheta D N θ R p p = (θ : ℂ) * ((D : ℂ) * ntr (R * Ea D N p.1)) +
        ((1 - θ : ℝ) : ℂ) * ntr R := by
      simp [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Ea]
    rw [h1, Matrix.diagonal_apply_eq]
    have hD : (D : ℂ) ≠ 0 := by
      have := p.1.pos
      exact_mod_cast this.ne'
    have hN : (N : ℂ) ≠ 0 := by
      have := p.2.pos
      exact_mod_cast this.ne'
    simp only [ntr, Matrix.trace, Matrix.diag, Matrix.mul_apply, Ea, Matrix.diagonal_apply,
      Fintype.card_prod, Fintype.card_fin, varProf]
    push_cast
    simp only [mul_ite, mul_zero, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e1 : (∑ x : Idx D N, ∑ x_1 : Idx D N,
        if x_1 = x then if x_1.1 = p.1 then R x x_1 * 1 else 0 else 0) =
        ∑ x : Idx D N, if x.1 = p.1 then R x x else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x.1 = p.1 <;> simp [hx]
    have e2 : ∀ x : Idx D N, (θ : ℂ) * ((if p.1 = x.1 then ((N : ℝ)⁻¹ : ℝ) else 0 : ℝ) : ℂ) *
        R x x = (θ : ℂ) * (N : ℂ)⁻¹ * (if x.1 = p.1 then R x x else 0) := by
      intro x
      by_cases hx : x.1 = p.1
      · simp [hx]
      · have : ¬ p.1 = x.1 := fun h => hx h.symm
        simp [hx, this]
    rw [e1]
    simp only [e2, ← Finset.mul_sum]
    field_simp
  · simp [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Ea, h]

private lemma FID_dot_mulVec_conj {ι : Type*} [Fintype ι] (Λ : Matrix ι ι ℂ) (x w : ι → ℂ) :
    star x ⬝ᵥ (Λ *ᵥ w) = star (Λᴴ *ᵥ x) ⬝ᵥ w := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

private lemma FID_hg_eq (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (x y : Idx D N → ℂ) :
    star x ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ y) =
      star x ⬝ᵥ y + z * (star x ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y)) -
        star (Λᴴ *ᵥ x) ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y) +
        ∑ k, star (x k) * (∑ r, ((varProf D N θ k r : ℝ) : ℂ) * res (Matrix.of h + Λ) z r r) *
          (res (Matrix.of h + Λ) z *ᵥ y) k := by
  set G := res (Matrix.of h + Λ) z with hG
  have hHΛ : (Matrix.of h + Λ).IsHermitian := hh.add hΛ
  have hres := (res_mul_sub (Matrix.of h + Λ) hHΛ z hz).1
  have hHG : Matrix.of h * G = 1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G := by
    have : Matrix.of h * G = (Matrix.of h + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G -
        (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G := by
      rw [← Matrix.sub_mul]
      congr 1
      abel
    rw [this, hres]
  have hform : hgUnder D N θ (Matrix.of h) Λ z =
      1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G + sTheta D N θ G * G := by
    unfold hgUnder
    rw [← hG, hHG]
  rw [hform, FID_sTheta_diag, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  have hdiag : ∀ (d w : Idx D N → ℂ), Matrix.diagonal d *ᵥ w = fun k => d k * w k :=
    fun d w => funext fun k => Matrix.mulVec_diagonal d w k
  rw [hdiag]
  simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    FID_dot_mulVec_conj]
  have e : (star x ⬝ᵥ fun k => (∑ r, ((varProf D N θ k r : ℝ) : ℂ) * G r r) * (G *ᵥ y) k) =
      ∑ k, star (x k) * (∑ r, ((varProf D N θ k r : ℝ) : ℂ) * G r r) * (G *ᵥ y) k := by
    simp only [dotProduct, Pi.star_apply, mul_assoc]
  rw [e]
  ring

/-- The tilted vectors give `N⁻¹ t^r(x)^* w = Σ_k x̄_k s_{kr} w_k`. -/
private lemma FID_tilt_dot (D N : ℕ) (θ : ℝ) (x w : Idx D N → ℂ) (r : Idx D N) :
    (N : ℂ)⁻¹ * (star (tiltV D N θ x r) ⬝ᵥ w) =
      ∑ k, star (x k) * ((varProf D N θ k r : ℝ) : ℂ) * w k := by
  have hN : (N : ℂ) ≠ 0 := by
    have := r.2.pos
    exact_mod_cast this.ne'
  simp only [dotProduct, Pi.star_apply, tiltV, Complex.star_def, map_mul, Complex.conj_ofReal,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  field_simp

/-- `(E_a)ᴴ x` is `x` restricted to the block `a`. -/
private lemma FID_Ea_apply (D N : ℕ) (a : Fin D) (x : Idx D N → ℂ) (k : Idx D N) :
    ((Ea D N a)ᴴ *ᵥ x) k = if k.1 = a then x k else 0 := by
  have : (Ea D N a)ᴴ = Ea D N a := by
    unfold Ea
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext p
    by_cases h : p.1 = a <;> simp [h]
  rw [this]
  unfold Ea
  rw [Matrix.mulVec_diagonal]
  by_cases h : k.1 = a <;> simp [h]

/-- The profile splits as `s_{kr} = (θ/N) 1(k, r in one block) + (1 - θ)/(DN)`. -/
private lemma FID_prof_dot (D N : ℕ) (θ : ℝ) (x w : Idx D N → ℂ) (r : Idx D N) :
    ∑ k, star (x k) * ((varProf D N θ k r : ℝ) : ℂ) * w k =
      ((θ : ℂ) / N) * (star ((Ea D N r.1)ᴴ *ᵥ x) ⬝ᵥ w) +
        (((1 - θ : ℝ) : ℂ) / ((D : ℂ) * N)) * (star x ⬝ᵥ w) := by
  simp only [dotProduct, Pi.star_apply, FID_Ea_apply, varProf, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : k.1 = r.1
  · simp [h]
    ring
  · simp [h]
    ring

/-- The terms of `(H̲G)_{xy}` without the profile: `x^* y`, `z x^* G y` and `-(Λ^* x)^* G y`. -/
private def FID_Pb (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (x y : Idx D N → ℂ) :
    ResPoly D N :=
  [(star x ⬝ᵥ y, []), (z, [(x, y, Λ, z)]), (-1, [(Λᴴ *ᵥ x, y, Λ, z)])]

/-- The terms `Σ_r c_r G_{rr} v_r^* G y` of the profile part. -/
private def FID_Pr (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (y : Idx D N → ℂ)
    (c : Idx D N → ℂ) (v : Idx D N → Idx D N → ℂ) : ResPoly D N :=
  (Finset.univ : Finset (Idx D N)).toList.map fun r =>
    (c r, [(Pi.single r 1, Pi.single r 1, Λ, z), (v r, y, Λ, z)])

private lemma FID_eval_Pb (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (x y : Idx D N → ℂ) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (FID_Pb D N Λ z x y) h = star x ⬝ᵥ y +
      z * (star x ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y)) -
        star (Λᴴ *ᵥ x) ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y) := by
  simp [FID_Pb, resPolyEval, resMonoEval, resFactorEval]
  ring

private lemma FID_eval_Pr (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (y : Idx D N → ℂ) (c : Idx D N → ℂ) (v : Idx D N → Idx D N → ℂ)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (FID_Pr D N Λ z y c v) h = ∑ r, c r *
      (res (Matrix.of h + Λ) z r r * (star (v r) ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y))) := by
  unfold FID_Pr resPolyEval
  rw [List.map_map]
  rw [← Finset.sum_map_toList]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  simp [resMonoEval, resFactorEval]

/-- The polynomial of the proof of the derivative: the terms of `(H̲G)_{xy}` with the tilted
vectors `t^r(x)`. -/
private def FID_Pt (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (x y : Idx D N → ℂ) : ResPoly D N :=
  FID_Pb D N Λ z x y ++ FID_Pr D N Λ z y (fun _ => (N : ℂ)⁻¹) (tiltV D N θ x)

private lemma FID_eval_Pt (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (x y : Idx D N → ℂ) :
    resPolyEval (FID_Pt D N θ Λ z x y) h = star x ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ y) := by
  rw [FID_hg_eq D N θ Λ hΛ z hz h hh, FID_Pt, resPolyEval_append, FID_eval_Pb, FID_eval_Pr]
  congr 1
  have e1 : ∀ r : Idx D N, (N : ℂ)⁻¹ * (res (Matrix.of h + Λ) z r r *
      (star (tiltV D N θ x r) ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y))) =
      ∑ k, star (x k) * (((varProf D N θ k r : ℝ) : ℂ) * res (Matrix.of h + Λ) z r r) *
        (res (Matrix.of h + Λ) z *ᵥ y) k := by
    intro r
    rw [mul_left_comm, FID_tilt_dot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

private lemma FID_resPolyD_append {D N : ℕ} (a b : Idx D N) (c : ℂ) (P Q : ResPoly D N) :
    resPolyD a b c (P ++ Q) = resPolyD a b c P ++ resPolyD a b c Q := by
  simp [resPolyD, List.flatMap_append]

private lemma FID_resPolyD_map {D N : ℕ} {α : Type*} (a b : Idx D N) (c : ℂ) (L : List α)
    (g : α → ℂ × ResMono D N) :
    resPolyD a b c (L.map g) = L.flatMap fun r => resPolyD a b c [g r] := by
  induction L with
  | nil => simp [resPolyD]
  | cons r L ih =>
    rw [List.map_cons, ← List.singleton_append, FID_resPolyD_append, ih]
    simp

private lemma FID_eval_flatMap {D N : ℕ} {α : Type*} (L : List α) (F : α → ResPoly D N)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (L.flatMap F) h = (L.map fun r => resPolyEval (F r) h).sum := by
  induction L with
  | nil => simp [resPolyEval]
  | cons r L ih =>
    rw [List.flatMap_cons, resPolyEval_append, ih, List.map_cons, List.sum_cons]

private lemma FID_eval_dPb (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (x y : Idx D N → ℂ) (a b : Idx D N) (c : ℂ) (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (resPolyD a b c (FID_Pb D N Λ z x y)) h =
      -c * ((z * (star x ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ Pi.single a 1)) -
        star (Λᴴ *ᵥ x) ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ Pi.single a 1)) *
          (res (Matrix.of h + Λ) z *ᵥ y) b) := by
  simp [FID_Pb, resPolyD, resMonoD, resPolyEval, resMonoEval, resFactorEval]
  ring

private lemma FID_eval_dPr (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (y : Idx D N → ℂ) (c₀ : Idx D N → ℂ) (v : Idx D N → Idx D N → ℂ) (a b : Idx D N) (c : ℂ)
    (h : Idx D N → Idx D N → ℂ) :
    resPolyEval (resPolyD a b c (FID_Pr D N Λ z y c₀ v)) h = -c * ∑ r, c₀ r *
      (res (Matrix.of h + Λ) z r a * res (Matrix.of h + Λ) z b r *
          (star (v r) ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y)) +
        res (Matrix.of h + Λ) z r r * (star (v r) ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ Pi.single a 1)) *
          (res (Matrix.of h + Λ) z *ᵥ y) b) := by
  unfold FID_Pr
  rw [FID_resPolyD_map, FID_eval_flatMap, Finset.mul_sum, ← Finset.sum_map_toList]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  simp [resPolyD, resMonoD, resPolyEval, resMonoEval, resFactorEval]
  ring

private lemma FID_eval_dPt (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (x y : Idx D N → ℂ) (a b : Idx D N) (c : ℂ) :
    resPolyEval (resPolyD a b c (FID_Pt D N θ Λ z x y)) h =
      c * hgDer D N θ (Matrix.of h) Λ z x y a b := by
  have hF := FID_eval_Pt D N θ Λ hΛ z hz h hh x (Pi.single a 1)
  rw [FID_Pt, FID_resPolyD_append, resPolyEval_append, FID_eval_dPb, FID_eval_dPr]
  unfold hgDer
  rw [← hF, FID_Pt, resPolyEval_append, FID_eval_Pb, FID_eval_Pr]
  simp only [dotProduct_single, Pi.star_apply, mul_one, Complex.star_def, mul_add,
    Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

private lemma FID_pairs_Pt (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (x y : Idx D N → ℂ) : ∀ t ∈ FID_Pt D N θ Λ z x y, ∀ f ∈ t.2, f.2.2 = (Λ, z) := by
  intro t ht f hf
  simp only [FID_Pt, FID_Pb, FID_Pr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at ht
  rcases ht with (rfl | rfl | rfl) | ⟨r, rfl⟩
  · simp at hf
  · simp at hf; rw [hf]
  · simp at hf; rw [hf]
  · simp at hf; rcases hf with rfl | rfl <;> rfl

/-- The first Wirtinger derivatives of `(H̲G)_{xy}` of (2.30) [eq:HGline] along a Hermitian slice
`w ↦ setEntry h i j w`: `∂_w = c · hgDer(i, j)` and `∂_{w̄} = c · hgDer(j, i)`, with `c = 1` for
`i ≠ j` and `c = 1/2` for `i = j`. -/
theorem hgUnder_dW (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (x y : Idx D N → ℂ) (w : ℂ) :
    dW (fun w' => star x ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h i j w')) Λ z *ᵥ y)) w =
        (if i = j then 1 / 2 else 1) *
          hgDer D N θ (Matrix.of (setEntry h i j w)) Λ z x y i j ∧
      dWbar (fun w' => star x ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h i j w')) Λ z *ᵥ y)) w =
        (if i = j then 1 / 2 else 1) *
          hgDer D N θ (Matrix.of (setEntry h i j w)) Λ z x y j i := by
  have hP : ∀ t ∈ FID_Pt D N θ Λ z x y, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
    intro t ht f hf
    rw [FID_pairs_Pt D N θ Λ z x y t ht f hf]
    exact ⟨hΛ, hz.ne'⟩
  have hF : (fun w' => star x ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h i j w')) Λ z *ᵥ y)) =
      fun w' => resPolyEval (FID_Pt D N θ Λ z x y) (setEntry h i j w') :=
    funext fun w' => (FID_eval_Pt D N θ Λ hΛ z hz _ (FID_slice_herm h hh i j w') x y).symm
  rw [hF]
  have hd := resPoly_dW h hh i j _ hP
  refine ⟨?_, ?_⟩
  · rw [congrFun hd.1 w]
    exact FID_eval_dPt D N θ Λ hΛ z hz _ (FID_slice_herm h hh i j w) x y i j _
  · rw [congrFun hd.2 w]
    exact FID_eval_dPt D N θ Λ hΛ z hz _ (FID_slice_herm h hh i j w) x y j i _

/-- The polynomial of the statement: the terms of `(H̲G)_{xy}` with the block projections. -/
private def FID_Pq (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (x y : Idx D N → ℂ) : ResPoly D N :=
  FID_Pb D N Λ z x y ++ FID_Pr D N Λ z y (fun _ => (θ : ℂ) / N)
      (fun r => (Ea D N r.1)ᴴ *ᵥ x) ++
    FID_Pr D N Λ z y (fun _ => ((1 - θ : ℝ) : ℂ) / ((D : ℂ) * N)) (fun _ => x)

private lemma FID_eval_Pq (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (x y : Idx D N → ℂ) :
    resPolyEval (FID_Pq D N θ Λ z x y) h =
      star x ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ y) := by
  rw [FID_hg_eq D N θ Λ hΛ z hz h hh, FID_Pq, resPolyEval_append, resPolyEval_append,
    FID_eval_Pb, FID_eval_Pr, FID_eval_Pr, add_assoc]
  congr 1
  have e1 : ∀ r : Idx D N, (∑ k, star (x k) * (((varProf D N θ k r : ℝ) : ℂ) *
      res (Matrix.of h + Λ) z r r) * (res (Matrix.of h + Λ) z *ᵥ y) k) =
      (θ : ℂ) / N * (res (Matrix.of h + Λ) z r r * (star ((Ea D N r.1)ᴴ *ᵥ x) ⬝ᵥ
        (res (Matrix.of h + Λ) z *ᵥ y))) +
      ((1 - θ : ℝ) : ℂ) / ((D : ℂ) * N) * (res (Matrix.of h + Λ) z r r *
        (star x ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y))) := by
    intro r
    have := FID_prof_dot D N θ x (res (Matrix.of h + Λ) z *ᵥ y) r
    calc _ = res (Matrix.of h + Λ) z r r * ∑ k, star (x k) * ((varProf D N θ k r : ℝ) : ℂ) *
          (res (Matrix.of h + Λ) z *ᵥ y) k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by rw [this]; ring
  have e2 : (∑ k, star (x k) * (∑ r, ((varProf D N θ k r : ℝ) : ℂ) * res (Matrix.of h + Λ) z r r) *
      (res (Matrix.of h + Λ) z *ᵥ y) k) =
      ∑ k, ∑ r, star (x k) * (((varProf D N θ k r : ℝ) : ℂ) * res (Matrix.of h + Λ) z r r) *
        (res (Matrix.of h + Λ) z *ᵥ y) k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [e2, Finset.sum_comm]
  simp only [e1, Finset.sum_add_distrib]

private lemma FID_wt_Pr_const (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (y : Idx D N → ℂ) (c : ℂ) (v : Idx D N → Idx D N → ℂ) :
    ((FID_Pr D N Λ z y (fun _ => c) v).map fun t => ‖t.1‖).sum = ((D * N : ℕ) : ℝ) * ‖c‖ := by
  unfold FID_Pr
  rw [List.map_map]
  have : ((fun t : ℂ × ResMono D N => ‖t.1‖) ∘ fun r : Idx D N =>
      (c, [(Pi.single r 1, Pi.single r 1, Λ, z), (v r, y, Λ, z)])) = fun _ => ‖c‖ := rfl
  rw [this, Finset.sum_map_toList]
  simp [Fintype.card_prod]

private lemma FID_wt_Pq (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (x y : Idx D N → ℂ)
    (hx : ∑ k, ‖x k‖ ^ 2 ≤ 1) (hy : ∑ k, ‖y k‖ ^ 2 ≤ 1) :
    ((FID_Pq D N θ Λ z x y).map fun t => ‖t.1‖).sum ≤ ((D : ℝ) + 3) * (1 + ‖z‖) := by
  have hxy : ‖star x ⬝ᵥ y‖ ≤ 1 := by
    refine (FID_cs x y).trans ?_
    have h1 : Real.sqrt (∑ k, ‖x k‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hx
    have h2 : Real.sqrt (∑ k, ‖y k‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hy
    nlinarith [Real.sqrt_nonneg (∑ k, ‖x k‖ ^ 2), Real.sqrt_nonneg (∑ k, ‖y k‖ ^ 2)]
  simp only [FID_Pq, FID_Pb, List.map_append, List.sum_append, FID_wt_Pr_const]
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hz0 := norm_nonneg z
  have e1 : ((D * N : ℕ) : ℝ) * ‖(θ : ℂ) / N‖ ≤ D * θ := by
    rw [norm_div, Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg hθ0]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp; positivity
    · have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      push_cast
      field_simp
      exact le_rfl
  have e2 : ((D * N : ℕ) : ℝ) * ‖((1 - θ : ℝ) : ℂ) / ((D : ℂ) * N)‖ ≤ 1 - θ := by
    rw [norm_div, Complex.norm_real, norm_mul, Complex.norm_natCast, Complex.norm_natCast,
      Real.norm_of_nonneg (by linarith)]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp; linarith
    rcases Nat.eq_zero_or_pos D with hD0 | hD0
    · subst hD0; simp; linarith
    · have h1 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have h2 : (D : ℝ) ≠ 0 := by exact_mod_cast hD0.ne'
      push_cast
      field_simp
      exact le_rfl
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, norm_neg, norm_one]
  nlinarith [mul_nonneg hD hz0]

/-- `(H̲G)_{xy}` of (2.30) [eq:HGline] is, on Hermitian arrays, a resolvent polynomial in
`G(z) = (h + Λ - z)⁻¹` of degree `≤ 2` over the vectors `x`, `Λ^* x`, `E_a x`, `y` and the
standard basis, with weight `≤ (D + 3)(1 + |z|)`. -/
theorem hgUnder_resPoly (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (x y : Idx D N → ℂ) (hx : ∑ k, ‖x k‖ ^ 2 ≤ 1) (hy : ∑ k, ‖y k‖ ^ 2 ≤ 1) :
    ∃ P : ResPoly D N, (∀ t ∈ P, t.2.length ≤ 2 ∧ ∀ f ∈ t.2,
        (f.1 = x ∨ f.1 = Λᴴ *ᵥ x ∨ (∃ a, f.1 = (Ea D N a)ᴴ *ᵥ x) ∨
          ∃ k, f.1 = Pi.single k 1) ∧
        (f.2.1 = y ∨ ∃ k, f.2.1 = Pi.single k 1) ∧ f.2.2 = (Λ, z)) ∧
      (P.map fun t => ‖t.1‖).sum ≤ ((D : ℝ) + 3) * (1 + ‖z‖) ∧
      ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
        resPolyEval P h = star x ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ y) := by
  refine ⟨FID_Pq D N θ Λ z x y, ?_, FID_wt_Pq D N θ hθ0 hθ1 Λ z x y hx hy,
    fun h hh => FID_eval_Pq D N θ Λ hΛ z hz h hh x y⟩
  intro t ht
  simp only [FID_Pq, FID_Pb, FID_Pr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at ht
  rcases ht with ((rfl | rfl | rfl) | ⟨r, rfl⟩) | ⟨r, rfl⟩
  · simp
  · refine ⟨by simp, fun f hf => ?_⟩
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨Or.inl rfl, Or.inl rfl, rfl⟩
  · refine ⟨by simp, fun f hf => ?_⟩
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨Or.inr (Or.inl rfl), Or.inl rfl, rfl⟩
  · refine ⟨by simp, fun f hf => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨Or.inr (Or.inr (Or.inr ⟨r, rfl⟩)), Or.inr ⟨r, rfl⟩, rfl⟩
    · exact ⟨Or.inr (Or.inr (Or.inl ⟨r.1, rfl⟩)), Or.inl rfl, rfl⟩
  · refine ⟨by simp, fun f hf => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨Or.inr (Or.inr (Or.inr ⟨r, rfl⟩)), Or.inr ⟨r, rfl⟩, rfl⟩
    · exact ⟨Or.inl rfl, Or.inl rfl, rfl⟩

private lemma FID_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
    (x w : ι → ℂ) :
    ‖star x ⬝ᵥ (T *ᵥ w)‖ ≤
      opNorm T * (Real.sqrt (∑ k, ‖x k‖ ^ 2) * Real.sqrt (∑ k, ‖w k‖ ^ 2)) := by
  have e : star x ⬝ᵥ (T *ᵥ w) =
      inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanLin T (WithLp.toLp 2 w)) := by
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
  have hx' : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = Real.sqrt (∑ k, ‖x k‖ ^ 2) :=
    EuclideanSpace.norm_eq _
  have hw' : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ ι)‖ = Real.sqrt (∑ k, ‖w k‖ ^ 2) :=
    EuclideanSpace.norm_eq _
  have h1 : Matrix.toEuclideanLin T (WithLp.toLp 2 w) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 w) := rfl
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 w)‖ ≤
      opNorm T * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ ι)‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [e, h1, ← hx', ← hw']
  calc ‖inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 w))‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 w)‖ := norm_inner_le_norm _ _
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
          (opNorm T * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ ι)‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = _ := by ring

private lemma FID_ward_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (v : ι → ℂ) (Υ : ℝ)
    (hv : (star v ⬝ᵥ (res X z *ᵥ v)).im ≤ Υ) :
    Real.sqrt (∑ k, ‖(res X z *ᵥ v) k‖ ^ 2) ≤ Real.sqrt (Υ / z.im) := by
  rw [ward_vec X hX z hz v]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hv hz.le)

private lemma FID_lam_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (hΛn : opNorm Λ ≤ 1 / 10) (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (u v : ι → ℂ) (Υ : ℝ) (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1)
    (hv : (star v ⬝ᵥ (res X z *ᵥ v)).im ≤ Υ) :
    ‖star (Λᴴ *ᵥ u) ⬝ᵥ (res X z *ᵥ v)‖ ≤ Real.sqrt (Υ / z.im) / 10 := by
  have hw := FID_ward_le X hX z hz v Υ hv
  have hw0 := Real.sqrt_nonneg (∑ k, ‖(res X z *ᵥ v) k‖ ^ 2)
  have hxn : Real.sqrt (∑ k, ‖u k‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hu
  rw [← FID_dot_mulVec_conj]
  refine (FID_form_le Λ u (res X z *ᵥ v)).trans ?_
  have h1 : Real.sqrt (∑ k, ‖u k‖ ^ 2) * Real.sqrt (∑ k, ‖(res X z *ᵥ v) k‖ ^ 2) ≤
      1 * Real.sqrt (Υ / z.im) := mul_le_mul hxn hw hw0 zero_le_one
  have h2 : 0 ≤ opNorm Λ := norm_nonneg _
  nlinarith

/-! ### The bound on the derivatives of a factor with a Ward-bounded leading vector -/

/-- The sum of the moduli of the coefficients of a resolvent polynomial. -/
private def FID_wt {D N : ℕ} (P : ResPoly D N) : ℝ := (P.map fun t => ‖t.1‖).sum

private lemma FID_wt_nonneg {D N : ℕ} (P : ResPoly D N) : 0 ≤ FID_wt P :=
  List.sum_nonneg fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _

private lemma FID_wt_cons {D N : ℕ} (t : ℂ × ResMono D N) (P : ResPoly D N) :
    FID_wt (t :: P) = ‖t.1‖ + FID_wt P := by
  simp [FID_wt]

private lemma FID_wt_append {D N : ℕ} (P Q : ResPoly D N) :
    FID_wt (P ++ Q) = FID_wt P + FID_wt Q := by
  simp [FID_wt, List.map_append, List.sum_append]

/-- One derivative of a monomial of degree `d` is `d` terms with coefficient `-c`. -/
private lemma FID_wt_resMonoD {D N : ℕ} (a b : Idx D N) (c : ℂ) (m : ResMono D N) :
    FID_wt (resMonoD a b c m) = m.length * ‖c‖ := by
  induction m with
  | nil => simp [resMonoD, FID_wt]
  | cons f m ih =>
    have e : FID_wt ((resMonoD a b c m).map fun t => (t.1, f :: t.2)) =
        FID_wt (resMonoD a b c m) := by
      simp [FID_wt, Function.comp_def]
    simp only [resMonoD]
    rw [FID_wt_cons, e, ih]
    simp only [norm_neg, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

private lemma FID_wt_map_mul {D N : ℕ} (c₀ : ℂ) (Q : ResPoly D N) :
    FID_wt (Q.map fun s => (c₀ * s.1, s.2)) = ‖c₀‖ * FID_wt Q := by
  induction Q with
  | nil => simp [FID_wt]
  | cons t Q ih =>
    rw [List.map_cons, FID_wt_cons, ih, FID_wt_cons]
    simp only [norm_mul]
    ring

private lemma FID_wt_resPolyD_le {D N : ℕ} (a b : Idx D N) (c : ℂ) (hc : ‖c‖ ≤ 1) (m : ℕ)
    (P : ResPoly D N) (hP : ∀ t ∈ P, t.2.length ≤ m) :
    FID_wt (resPolyD a b c P) ≤ m * FID_wt P := by
  induction P with
  | nil => simp [resPolyD, FID_wt]
  | cons t P ih =>
    have ih' := ih fun u hu => hP u (List.mem_cons_of_mem _ hu)
    have e : resPolyD a b c (t :: P) =
        ((resMonoD a b c t.2).map fun s => (t.1 * s.1, s.2)) ++ resPolyD a b c P := by
      simp [resPolyD]
    have h2 : (t.2.length : ℝ) ≤ m := by exact_mod_cast hP t List.mem_cons_self
    rw [e, FID_wt_append, FID_wt_map_mul, FID_wt_resMonoD, FID_wt_cons]
    have h3 := norm_nonneg t.1
    have h4 : ‖t.1‖ * (t.2.length * ‖c‖) ≤ m * ‖t.1‖ := by
      calc ‖t.1‖ * (t.2.length * ‖c‖) ≤ ‖t.1‖ * (m * 1) := by
            gcongr
        _ = m * ‖t.1‖ := by ring
    nlinarith

/-- The factors of the terms of `resMonoD a b c m`: each is a factor of `m`, or one of the two
factors that replace it; the length goes up by one. -/
private lemma FID_resMonoD_mem {D N : ℕ} (a b : Idx D N) (c : ℂ) (m : ResMono D N) :
    ∀ s ∈ resMonoD a b c m, s.2.length = m.length + 1 ∧ ∀ g ∈ s.2, ∃ f ∈ m,
      g = f ∨ g = (f.1, Pi.single a 1, f.2.2.1, f.2.2.2) ∨
        g = (Pi.single b 1, f.2.1, f.2.2.1, f.2.2.2) := by
  induction m with
  | nil => intro s hs; simp [resMonoD] at hs
  | cons f m ih =>
    intro s hs
    simp only [resMonoD, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | ⟨t, ht, rfl⟩
    · refine ⟨by simp, fun g hg => ?_⟩
      simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact ⟨f, List.mem_cons_self, Or.inr (Or.inl rfl)⟩
      · exact ⟨f, List.mem_cons_self, Or.inr (Or.inr rfl)⟩
      · exact ⟨g, List.mem_cons_of_mem _ hg, Or.inl rfl⟩
    · obtain ⟨h1, h3⟩ := ih t ht
      refine ⟨by simp [h1], fun g hg => ?_⟩
      simp only [List.mem_cons] at hg
      rcases hg with hg | hg
      · exact ⟨f, List.mem_cons_self, Or.inl hg⟩
      · obtain ⟨f', hf', hg'⟩ := h3 g hg
        exact ⟨f', List.mem_cons_of_mem _ hf', hg'⟩

/-- Every term has a leading factor `x₀^* G v`, `v ∈ V`, followed by factors over `V`; at most
`m` factors, all with the pair `p`. -/
private def FID_hd {D N : ℕ} (x₀ : Idx D N → ℂ) (V : Set (Idx D N → ℂ))
    (p : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (m : ℕ) (P : ResPoly D N) : Prop :=
  ∀ t ∈ P, ∃ (f₀ : ResFactor D N) (r : ResMono D N), t.2 = f₀ :: r ∧ f₀.1 = x₀ ∧
    f₀.2.1 ∈ V ∧ f₀.2.2 = p ∧ r.length + 1 ≤ m ∧ ∀ f ∈ r, f.1 ∈ V ∧ f.2.1 ∈ V ∧ f.2.2 = p

private lemma FID_hd_resPolyD {D N : ℕ} (x₀ : Idx D N → ℂ) (V : Set (Idx D N → ℂ))
    (p : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (a b : Idx D N) (c : ℂ)
    (ha : Pi.single a 1 ∈ V) (hb : Pi.single b 1 ∈ V) (m : ℕ) (P : ResPoly D N)
    (hP : FID_hd x₀ V p m P) : FID_hd x₀ V p (m + 1) (resPolyD a b c P) := by
  intro u hu
  unfold resPolyD at hu
  rw [List.mem_flatMap] at hu
  obtain ⟨t, ht, hu⟩ := hu
  rw [List.mem_map] at hu
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨f₀, r, ht2, hf1, hf2, hf3, hlen, hr⟩ := hP t ht
  rw [ht2] at hs
  simp only [resMonoD, List.mem_cons, List.mem_map] at hs
  rcases hs with rfl | ⟨t', ht', rfl⟩
  · refine ⟨(f₀.1, Pi.single a 1, f₀.2.2.1, f₀.2.2.2),
      (Pi.single b 1, f₀.2.1, f₀.2.2.1, f₀.2.2.2) :: r, rfl, hf1, ha, hf3, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro f hf
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact ⟨hb, hf2, hf3⟩
      · exact hr f hf
  · obtain ⟨h1, h3⟩ := FID_resMonoD_mem a b c r t' ht'
    refine ⟨f₀, t'.2, rfl, hf1, hf2, hf3, by omega, ?_⟩
    intro g hg
    obtain ⟨f, hfm, hgf⟩ := h3 g hg
    obtain ⟨hf1', hf2', hf3'⟩ := hr f hfm
    rcases hgf with h | h | h <;> rw [h]
    · exact ⟨hf1', hf2', hf3'⟩
    · exact ⟨hf1', ha, hf3'⟩
    · exact ⟨hb, hf2', hf3'⟩

private lemma FID_hd_iter {D N : ℕ} (x₀ : Idx D N → ℂ) (V : Set (Idx D N → ℂ))
    (p : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (a b : Idx D N) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (ha : Pi.single a 1 ∈ V) (hb : Pi.single b 1 ∈ V) (n m : ℕ) (P : ResPoly D N)
    (hP : FID_hd x₀ V p m P) :
    FID_hd x₀ V p (m + n) ((resPolyD a b c)^[n] P) ∧
      FID_wt ((resPolyD a b c)^[n] P) ≤ ((m + n : ℕ) : ℝ) ^ n * FID_wt P := by
  induction n with
  | zero => exact ⟨hP, by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Function.iterate_succ_apply']
    have h3 := FID_hd_resPolyD x₀ V p a b c ha hb (m + n) _ h1
    have h4 := FID_wt_resPolyD_le a b c hc (m + n) _ fun t ht => by
      obtain ⟨f₀, r, ht2, -, -, -, hlen, -⟩ := h1 t ht
      rw [ht2]
      simpa using hlen
    refine ⟨h3, ?_⟩
    have h5 : ((m + n : ℕ) : ℝ) * FID_wt ((resPolyD a b c)^[n] P) ≤
        ((m + n : ℕ) : ℝ) * (((m + n : ℕ) : ℝ) ^ n * FID_wt P) :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    have h6 : ((m + n : ℕ) : ℝ) ^ (n + 1) ≤ ((m + (n + 1) : ℕ) : ℝ) ^ (n + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ_of_le le_rfl) _
    calc FID_wt (resPolyD a b c ((resPolyD a b c)^[n] P))
        ≤ ((m + n : ℕ) : ℝ) * FID_wt ((resPolyD a b c)^[n] P) := h4
      _ ≤ ((m + n : ℕ) : ℝ) * (((m + n : ℕ) : ℝ) ^ n * FID_wt P) := h5
      _ = ((m + n : ℕ) : ℝ) ^ (n + 1) * FID_wt P := by ring
      _ ≤ ((m + (n + 1) : ℕ) : ℝ) ^ (n + 1) * FID_wt P :=
        mul_le_mul_of_nonneg_right h6 (FID_wt_nonneg P)

private lemma FID_mono_le {D N : ℕ} (m : ResMono D N) (h' : Idx D N → Idx D N → ℂ) (Γ : ℝ)
    (hΓ : 0 ≤ Γ) (hm : ∀ f ∈ m, ‖resFactorEval f h'‖ ≤ Γ) :
    ‖resMonoEval m h'‖ ≤ Γ ^ m.length := by
  induction m with
  | nil => simp [resMonoEval]
  | cons f m ih =>
    have ih' := ih fun g hg => hm g (List.mem_cons_of_mem _ hg)
    simp only [resMonoEval, List.map_cons, List.prod_cons, norm_mul, List.length_cons,
      pow_succ] at ih' ⊢
    rw [mul_comm (Γ ^ m.length)]
    exact mul_le_mul (hm f List.mem_cons_self) ih' (norm_nonneg _) hΓ

private lemma FID_eval_cons {D N : ℕ} (t : ℂ × ResMono D N) (P : ResPoly D N)
    (h' : Idx D N → Idx D N → ℂ) :
    resPolyEval (t :: P) h' = t.1 * resMonoEval t.2 h' + resPolyEval P h' := by
  simp [resPolyEval]

private lemma FID_factor_eq {D N : ℕ} (f : ResFactor D N)
    (p : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (hp : f.2.2 = p) (h' : Idx D N → Idx D N → ℂ) :
    resFactorEval f h' = resFactorEval (f.1, f.2.1, p.1, p.2) h' := by
  subst hp
  rfl

/-- The value of a polynomial whose terms have a leading factor bounded by `ρ₀` and at most
`m - 1` further factors bounded by `Γ ≥ 1`. -/
private lemma FID_hd_eval_le {D N : ℕ} (x₀ : Idx D N → ℂ) (V : Set (Idx D N → ℂ))
    (p : Matrix (Idx D N) (Idx D N) ℂ × ℂ) (h' : Idx D N → Idx D N → ℂ) (Γ ρ₀ : ℝ)
    (hΓ : 1 ≤ Γ) (hρ : 0 ≤ ρ₀)
    (h1 : ∀ v ∈ V, ‖resFactorEval (x₀, v, p.1, p.2) h'‖ ≤ ρ₀)
    (h2 : ∀ x ∈ V, ∀ y ∈ V, ‖resFactorEval (x, y, p.1, p.2) h'‖ ≤ Γ) (m : ℕ)
    (P : ResPoly D N) (hP : FID_hd x₀ V p m P) :
    ‖resPolyEval P h'‖ ≤ FID_wt P * (ρ₀ * Γ ^ (m - 1)) := by
  have hΓ0 : 0 ≤ Γ := by linarith
  induction P with
  | nil => simp [resPolyEval, FID_wt]
  | cons t P ih =>
    have ih' := ih fun u hu => hP u (List.mem_cons_of_mem _ hu)
    obtain ⟨f₀, r, ht2, hf1, hf2, hf3, hlen, hr⟩ := hP t List.mem_cons_self
    have hmono : ‖resMonoEval t.2 h'‖ ≤ ρ₀ * Γ ^ (m - 1) := by
      rw [ht2]
      simp only [resMonoEval, List.map_cons, List.prod_cons, norm_mul]
      have e1 : ‖resFactorEval f₀ h'‖ ≤ ρ₀ := by
        rw [FID_factor_eq f₀ p hf3, hf1]
        exact h1 _ hf2
      have e2 : ‖resMonoEval r h'‖ ≤ Γ ^ (m - 1) := by
        refine (FID_mono_le r h' Γ hΓ0 fun f hf => ?_).trans (pow_le_pow_right₀ hΓ (by omega))
        obtain ⟨hx, hy, hp⟩ := hr f hf
        rw [FID_factor_eq f p hp]
        exact h2 _ hx _ hy
      exact mul_le_mul e1 e2 (norm_nonneg _) hρ
    rw [FID_eval_cons, FID_wt_cons]
    calc ‖t.1 * resMonoEval t.2 h' + resPolyEval P h'‖
        ≤ ‖t.1 * resMonoEval t.2 h'‖ + ‖resPolyEval P h'‖ := norm_add_le _ _
      _ ≤ ‖t.1‖ * (ρ₀ * Γ ^ (m - 1)) + FID_wt P * (ρ₀ * Γ ^ (m - 1)) := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hmono (norm_nonneg _)) ih'
      _ = (‖t.1‖ + FID_wt P) * (ρ₀ * Γ ^ (m - 1)) := by ring

private lemma FID_iter_append {D N : ℕ} (a b : Idx D N) (c : ℂ) (n : ℕ) (P Q : ResPoly D N) :
    (resPolyD a b c)^[n] (P ++ Q) = (resPolyD a b c)^[n] P ++ (resPolyD a b c)^[n] Q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih, FID_resPolyD_append]

/-- The terms `x^* y` and `z x^* G y` of `(H̲G)_{xy}`. -/
private def FID_Pb0 (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (x y : Idx D N → ℂ) :
    ResPoly D N :=
  [(star x ⬝ᵥ y, []), (z, [(x, y, Λ, z)])]

/-- The term `-(Λ^* x)^* G y` of `(H̲G)_{xy}`. -/
private def FID_Ph (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (x y : Idx D N → ℂ) :
    ResPoly D N :=
  [(-1, [(Λᴴ *ᵥ x, y, Λ, z)])]

/-- The terms of `(H̲G)_{xy}` over the vectors `x`, `y`, `e_r`, `t^r(x)`. -/
private def FID_Pv (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (x y : Idx D N → ℂ) : ResPoly D N :=
  FID_Pb0 D N Λ z x y ++ FID_Pr D N Λ z y (fun _ => (N : ℂ)⁻¹) (tiltV D N θ x)

private lemma FID_eval_Pv_Ph (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (x y : Idx D N → ℂ) :
    resPolyEval (FID_Pv D N θ Λ z x y ++ FID_Ph D N Λ z x y) h =
      star x ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ y) := by
  rw [← FID_eval_Pt D N θ Λ hΛ z hz h hh x y]
  have e : FID_Pt D N θ Λ z x y = (FID_Pb0 D N Λ z x y ++ FID_Ph D N Λ z x y) ++
      FID_Pr D N Λ z y (fun _ => (N : ℂ)⁻¹) (tiltV D N θ x) := rfl
  rw [e, FID_Pv]
  simp only [resPolyEval_append]
  ring

private lemma FID_pairs_Pv_Ph (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (x y : Idx D N → ℂ) :
    ∀ t ∈ FID_Pv D N θ Λ z x y ++ FID_Ph D N Λ z x y, ∀ f ∈ t.2, f.2.2 = (Λ, z) := by
  intro t ht f hf
  simp only [FID_Pv, FID_Ph, FID_Pb0, FID_Pr, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at ht
  rcases ht with ((rfl | rfl) | ⟨r, rfl⟩) | rfl
  · simp at hf
  · simp at hf; rw [hf]
  · simp at hf; rcases hf with rfl | rfl <;> rfl
  · simp at hf; rw [hf]

/-- The derivatives of `(H̲G)_{uy}` on the good event, without a bound on `‖H‖`: for fixed
`D, a, b` there is `c` such that, if `u`, `y`, the standard basis and the tilted vectors `t^r(u)`
lie in `V` (norms `≤ 1`), `1 ≤ Γ`, `η ≤ Υ` and `setEntry h i j w` is in the good event on `V`,
then `|∂_w^a ∂_{w̄}^b (H̲G)_{uy}(w)| ≤ c (1 + |z|) Γ^{a+b+2} (Υ/η)^{1/2}`. -/
theorem hgUnder_wirt_le (D a b : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (N : ℕ) (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ z : ℂ, 0 < z.im → ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      ∀ (i j : Idx D N) (w : ℂ) (u y : Idx D N → ℂ) (V : Finset (Idx D N → ℂ)) (Γ Υ : ℝ),
      u ∈ V → y ∈ V → (∀ k, Pi.single k 1 ∈ V) → (∀ r, tiltV D N θ u r ∈ V) →
      (∀ x ∈ V, ∑ k, ‖x k‖ ^ 2 ≤ 1) → 1 ≤ Γ → z.im ≤ Υ →
      setEntry h i j w ∈ goodSet Λ z V Γ Υ →
      ‖wirt a b (fun w' => star u ⬝ᵥ
          (hgUnder D N θ (Matrix.of (setEntry h i j w')) Λ z *ᵥ y)) w‖ ≤
        c * (1 + ‖z‖) * Γ ^ (a + b + 2) * Real.sqrt (Υ / z.im) := by
  refine ⟨((a + b + 2 : ℕ) : ℝ) ^ (a + b) * ((D : ℝ) + 1) + ((1 + a + b : ℕ) : ℝ) ^ (a + b),
    by positivity, ?_⟩
  intro N θ hθ0 hθ1 Λ hΛ hΛn z hz h hh i j w u y V Γ Υ hu hy hV ht hVn hΓ hΥ hgood
  have hhH : (Matrix.of (setEntry h i j w)).IsHermitian := FID_slice_herm h hh i j w
  have hρ1 : 1 ≤ Real.sqrt (Υ / z.im) := Real.one_le_sqrt.mpr ((one_le_div hz).mpr hΥ)
  have hΓ0 : 0 ≤ Γ := by linarith
  have hz0 := norm_nonneg z
  have hc : ‖(if i = j then (1 / 2 : ℂ) else 1)‖ ≤ 1 := by
    split_ifs
    · norm_num
    · simp
  have hΞ : ∀ p ∈ ({(Λ, z)} : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)),
      p.1.IsHermitian ∧ p.2.im ≠ 0 := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hΛ, hz.ne'⟩
  have hF : (fun w' => star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h i j w')) Λ z *ᵥ y)) =
      fun w' => resPolyEval (FID_Pv D N θ Λ z u y ++ FID_Ph D N Λ z u y) (setEntry h i j w') :=
    funext fun w' => (FID_eval_Pv_Ph D N θ Λ hΛ z hz _ (FID_slice_herm h hh i j w') u y).symm
  have hPVH : ∀ t ∈ FID_Pv D N θ Λ z u y ++ FID_Ph D N Λ z u y, ∀ f ∈ t.2,
      f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 := by
    intro t ht f hf
    rw [FID_pairs_Pv_Ph D N θ Λ z u y t ht f hf]
    exact ⟨hΛ, hz.ne'⟩
  have hPV : ∀ t ∈ FID_Pv D N θ Λ z u y, ∀ f ∈ t.2, f.2.2.1.IsHermitian ∧ f.2.2.2.im ≠ 0 :=
    fun t ht => hPVH t (List.mem_append_left _ ht)
  have key : wirt a b (fun w' => resPolyEval (FID_Pv D N θ Λ z u y ++ FID_Ph D N Λ z u y)
      (setEntry h i j w')) w =
      wirt a b (fun w' => resPolyEval (FID_Pv D N θ Λ z u y) (setEntry h i j w')) w +
        resPolyEval ((resPolyD i j (if i = j then 1 / 2 else 1))^[a]
          ((resPolyD j i (if i = j then 1 / 2 else 1))^[b] (FID_Ph D N Λ z u y)))
          (setEntry h i j w) := by
    rw [resPoly_wirt h hh i j _ hPVH a b, resPoly_wirt h hh i j _ hPV a b]
    simp only [FID_iter_append, resPolyEval_append]
  rw [hF, key]
  refine (norm_add_le _ _).trans ?_
  have hG : ∀ p ∈ ({(Λ, z)} : Set (Matrix (Idx D N) (Idx D N) ℂ × ℂ)), ∀ x ∈ (↑V : Set _),
      ∀ y ∈ (↑V : Set _), ‖resFactorEval (x, y, p.1, p.2) (setEntry h i j w)‖ ≤ Γ := by
    intro p hp x hx y hy
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact (hgood x hx y hy).1
  -- the part over `V`
  have hVpart := resPoly_wirt_le h hh i j (↑V : Set _) {(Λ, z)} (hV i) (hV j) hΞ
    (FID_Pv D N θ Λ z u y) 2 (by
      intro t ht
      simp only [FID_Pv, FID_Pb0, FID_Pr, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at ht
      rcases ht with (rfl | rfl) | ⟨r, rfl⟩
      · simp
      · refine ⟨by simp, fun f hf => ?_⟩
        simp only [List.mem_singleton] at hf
        subst hf
        exact ⟨hu, hy, rfl⟩
      · refine ⟨by simp, fun f hf => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl
        · exact ⟨hV r, hV r, rfl⟩
        · exact ⟨ht r, hy, rfl⟩) Γ hΓ w hG a b
  have hwt : ((FID_Pv D N θ Λ z u y).map fun t => ‖t.1‖).sum ≤ (D + 1) * (1 + ‖z‖) := by
    have hxy : ‖star u ⬝ᵥ y‖ ≤ 1 := by
      refine (FID_cs u y).trans ?_
      have h1 : Real.sqrt (∑ k, ‖u k‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (hVn u hu)
      have h2 : Real.sqrt (∑ k, ‖y k‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (hVn y hy)
      nlinarith [Real.sqrt_nonneg (∑ k, ‖u k‖ ^ 2), Real.sqrt_nonneg (∑ k, ‖y k‖ ^ 2)]
    have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have e1 : ((D * N : ℕ) : ℝ) * ‖((N : ℂ))⁻¹‖ ≤ D := by
      rw [norm_inv, Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN; simp
      · have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        push_cast
        field_simp
        exact le_rfl
    simp only [FID_Pv, FID_Pb0, List.map_append, List.sum_append, FID_wt_Pr_const,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    nlinarith [mul_nonneg hD hz0]
  -- the part with the leading factor `(Λ^* u)^* G y`
  have hH1 : ∀ v ∈ (↑V : Set (Idx D N → ℂ)),
      ‖resFactorEval (Λᴴ *ᵥ u, v, (Λ, z).1, (Λ, z).2) (setEntry h i j w)‖ ≤
        Real.sqrt (Υ / z.im) / 10 := fun v hv =>
    FID_lam_bound Λ hΛn _ (hhH.add hΛ) z hz u v Υ (hVn u hu) ((hgood v hv v hv).2)
  have hd0 : FID_hd (Λᴴ *ᵥ u) (↑V : Set (Idx D N → ℂ)) (Λ, z) 1 (FID_Ph D N Λ z u y) := by
    intro t ht
    simp only [FID_Ph, List.mem_singleton] at ht
    subst ht
    exact ⟨(Λᴴ *ᵥ u, y, Λ, z), [], rfl, rfl, hy, rfl, by simp, by simp⟩
  obtain ⟨g1, w1⟩ := FID_hd_iter (Λᴴ *ᵥ u) (↑V : Set (Idx D N → ℂ)) (Λ, z) j i
    (if i = j then (1 / 2 : ℂ) else 1) hc (hV j) (hV i) b 1 _ hd0
  obtain ⟨g2, w2⟩ := FID_hd_iter (Λᴴ *ᵥ u) (↑V : Set (Idx D N → ℂ)) (Λ, z) i j
    (if i = j then (1 / 2 : ℂ) else 1) hc (hV i) (hV j) a (1 + b) _ g1
  have hev := FID_hd_eval_le (Λᴴ *ᵥ u) (↑V : Set (Idx D N → ℂ)) (Λ, z) (setEntry h i j w) Γ
    (Real.sqrt (Υ / z.im) / 10) hΓ (by positivity) hH1
    (fun x hx y hy => hG (Λ, z) rfl x hx y hy) (1 + b + a) _ g2
  have hwt1 : FID_wt (FID_Ph D N Λ z u y) = 1 := by simp [FID_wt, FID_Ph]
  rw [hwt1, mul_one] at w1
  have hwH : FID_wt ((resPolyD i j (if i = j then (1 / 2 : ℂ) else 1))^[a]
      ((resPolyD j i (if i = j then (1 / 2 : ℂ) else 1))^[b] (FID_Ph D N Λ z u y))) ≤
      ((1 + a + b : ℕ) : ℝ) ^ (a + b) := by
    have hn : ((1 + b : ℕ) : ℝ) ≤ ((1 + a + b : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hn2 : ((1 + b + a : ℕ) : ℝ) = ((1 + a + b : ℕ) : ℝ) := by
      congr 1; omega
    rw [hn2] at w2
    calc _ ≤ _ := w2
      _ ≤ ((1 + a + b : ℕ) : ℝ) ^ a * ((1 + a + b : ℕ) : ℝ) ^ b := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact w1.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hn b)
      _ = _ := by rw [pow_add]
  have e1 : 1 + b + a - 1 = a + b := by omega
  rw [e1] at hev
  have e2 : 2 + a + b = a + b + 2 := by omega
  rw [e2] at hVpart
  set ρ := Real.sqrt (Υ / z.im) with hρ
  set K1 : ℝ := ((a + b + 2 : ℕ) : ℝ) ^ (a + b) with hK1
  set K2 : ℝ := ((1 + a + b : ℕ) : ℝ) ^ (a + b) with hK2
  have hK10 : 0 ≤ K1 := by positivity
  have hK20 : 0 ≤ K2 := by positivity
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hA : 0 ≤ Γ ^ (a + b + 2) := by positivity
  have hAn : Γ ^ (a + b) ≤ Γ ^ (a + b + 2) := pow_le_pow_right₀ hΓ (by omega)
  have hB : 1 ≤ 1 + ‖z‖ := by linarith
  have hV' : ‖wirt a b (fun w' => resPolyEval (FID_Pv D N θ Λ z u y) (setEntry h i j w')) w‖ ≤
      K1 * (D + 1) * ((1 + ‖z‖) * Γ ^ (a + b + 2)) * ρ := by
    have h1 : K1 * ((FID_Pv D N θ Λ z u y).map fun t => ‖t.1‖).sum *
        Γ ^ (a + b + 2) ≤ K1 * ((D + 1) * (1 + ‖z‖)) * Γ ^ (a + b + 2) := by
      gcongr
    refine hVpart.trans (h1.trans ?_)
    have h2 : 0 ≤ K1 * (D + 1) * ((1 + ‖z‖) * Γ ^ (a + b + 2)) := by positivity
    calc K1 * ((D + 1) * (1 + ‖z‖)) * Γ ^ (a + b + 2)
        = K1 * (D + 1) * ((1 + ‖z‖) * Γ ^ (a + b + 2)) := by ring
      _ ≤ K1 * (D + 1) * ((1 + ‖z‖) * Γ ^ (a + b + 2)) * ρ := by
        nlinarith [hρ1]
  have hH' : ‖resPolyEval ((resPolyD i j (if i = j then 1 / 2 else 1))^[a]
      ((resPolyD j i (if i = j then 1 / 2 else 1))^[b] (FID_Ph D N Λ z u y)))
        (setEntry h i j w)‖ ≤ K2 * ((1 + ‖z‖) * Γ ^ (a + b + 2)) * ρ := by
    refine hev.trans ?_
    have h1 : FID_wt ((resPolyD i j (if i = j then (1 / 2 : ℂ) else 1))^[a]
        ((resPolyD j i (if i = j then (1 / 2 : ℂ) else 1))^[b] (FID_Ph D N Λ z u y))) *
          (ρ / 10 * Γ ^ (a + b)) ≤ K2 * (ρ / 10 * Γ ^ (a + b)) :=
      mul_le_mul_of_nonneg_right hwH (by positivity)
    refine h1.trans ?_
    have h3 : ρ / 10 * Γ ^ (a + b) ≤ (1 + ‖z‖) * Γ ^ (a + b + 2) * ρ := by
      have h4 : 0 ≤ Γ ^ (a + b) := by positivity
      have hρ0 : (0 : ℝ) ≤ ρ := by linarith
      nlinarith [mul_nonneg h4 hρ0, mul_le_mul_of_nonneg_right hAn hρ0,
        mul_le_mul_of_nonneg_right hB (mul_nonneg hA hρ0)]
    calc K2 * (ρ / 10 * Γ ^ (a + b)) ≤ K2 * ((1 + ‖z‖) * Γ ^ (a + b + 2) * ρ) :=
          mul_le_mul_of_nonneg_left h3 hK20
      _ = K2 * ((1 + ‖z‖) * Γ ^ (a + b + 2)) * ρ := by ring
  calc _ ≤ K1 * (D + 1) * ((1 + ‖z‖) * Γ ^ (a + b + 2)) * ρ +
        K2 * ((1 + ‖z‖) * Γ ^ (a + b + 2)) * ρ := add_le_add hV' hH'
    _ = _ := by ring

/-- The order-`k` part of the isotropic expansion: with `f = G_{jv} (H̲G)_{uv}^{p-1}
conj((H̲G)_{uv})^p`, `Σ_{i,j} ū_i Σ_{a ≤ k} 𝒞^{(a, k-a+1)}(h_{ji}) E ∂_w^a ∂_{w̄}^{k-a} f /
(a! (k-a)!)`, the terms of Lemma 2.11 [lem:complex_cumu] for `E h_{ij} f = E h̄_{ji} f`. -/
def isoTerm (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (u v : Idx D N → ℂ) (p k : ℕ) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (u i) * ∑ a ∈ Finset.range (k + 1),
    ccum (μ.map fun h => h j i) a (k - a + 1) / ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
      ∫ h, wirt a (k - a) (fun w => (res (Matrix.of (setEntry h j i w) + Λ) z *ᵥ v) j *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of (setEntry h j i w)) Λ z *ᵥ v)) ^ p)
        (h j i) ∂μ

end RBMTransitionEdge

end
