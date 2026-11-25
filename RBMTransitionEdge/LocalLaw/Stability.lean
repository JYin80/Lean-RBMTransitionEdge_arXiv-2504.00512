module

public import RBMTransitionEdge.LocalLaw.Dyson
public import RBMTransitionEdge.Det.Block

@[expose] public section

/-!
# Stability of the vector equation

The good bound of the three regimes, the Fourier diagonalization of `1 − M̂σ_θ` ((3.1) [def_ML], (A.25)
[eq_lambdak]), the dichotomy for the vector equation and the monotonicity of the good bound.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The good bound of the stability of the vector equation in its three regimes: `K_L r̄ / d` in
the linear regime `r̄ ≤ c_L d²`; `K_A √r̄` in the quadratic regime with `a ≤ K₁ √r̄`; `K_B √r̄` in
the quadratic regime with `a > K₁ √r̄`. -/
def stabBound (cL K₁ KL KA KB rbar d a : ℝ) : ℝ :=
  if rbar ≤ cL * d ^ 2 then KL * rbar / d
  else if a ≤ K₁ * Real.sqrt rbar then KA * Real.sqrt rbar else KB * Real.sqrt rbar

/-! ### The Euclidean norm and the Fourier basis of `ℂ^D` -/

/-- `|x|` is the norm of `x` in `EuclideanSpace ℂ (Fin D)`. -/
private lemma Stability_vnorm_eq {D : ℕ} (x : Fin D → ℂ) :
    vnorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin D))‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

private lemma Stability_vnorm_nonneg {D : ℕ} (x : Fin D → ℂ) : 0 ≤ vnorm x := Real.sqrt_nonneg _

private lemma Stability_vnorm_sq {D : ℕ} (x : Fin D → ℂ) : vnorm x ^ 2 = ∑ a, ‖x a‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private lemma Stability_vnorm_add {D : ℕ} (x y : Fin D → ℂ) :
    vnorm (x + y) ≤ vnorm x + vnorm y := by
  simp only [Stability_vnorm_eq, WithLp.toLp_add]
  exact norm_add_le _ _

private lemma Stability_vnorm_sub {D : ℕ} (x y : Fin D → ℂ) :
    vnorm (x - y) ≤ vnorm x + vnorm y := by
  simp only [Stability_vnorm_eq, WithLp.toLp_sub]
  exact norm_sub_le _ _

private lemma Stability_vnorm_smul {D : ℕ} (c : ℂ) (x : Fin D → ℂ) :
    vnorm (c • x) = ‖c‖ * vnorm x := by
  simp only [Stability_vnorm_eq, WithLp.toLp_smul]
  exact norm_smul _ _

private lemma Stability_coord_le {D : ℕ} (x : Fin D → ℂ) (a : Fin D) : ‖x a‖ ≤ vnorm x := by
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun b => ‖x b‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)

private lemma Stability_D_le_sq (D : ℕ) : (D : ℝ) ≤ (D : ℝ) ^ 2 := by
  exact_mod_cast Nat.le_self_pow two_ne_zero D

private lemma Stability_vnorm_le_of_coord {D : ℕ} (x : Fin D → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ a, ‖x a‖ ≤ K) : vnorm x ≤ D * K := by
  rw [vnorm, Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hK, ?_⟩
  calc ∑ a, ‖x a‖ ^ 2 ≤ ∑ _a : Fin D, K ^ 2 :=
        Finset.sum_le_sum fun a _ => pow_le_pow_left₀ (norm_nonneg _) (h a) 2
    _ = D * K ^ 2 := by simp
    _ ≤ D ^ 2 * K ^ 2 := mul_le_mul_of_nonneg_right (Stability_D_le_sq D) (sq_nonneg K)
    _ = (D * K) ^ 2 := by ring

private lemma Stability_sum_le_of_coord {D : ℕ} (x : Fin D → ℂ) (K : ℝ)
    (h : ∀ a, ‖x a‖ ≤ K) : ‖∑ a, x a‖ ≤ D * K := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a, ‖x a‖ ≤ ∑ _a : Fin D, K := Finset.sum_le_sum fun a _ => h a
    _ = D * K := by simp

private lemma Stability_vnorm_le_mul {D : ℕ} (x y : Fin D → ℂ) (k : ℝ) (hk : 0 ≤ k)
    (h : ∀ a, ‖x a‖ ≤ k * ‖y a‖) : vnorm x ≤ k * vnorm y := by
  have e : k * vnorm y = Real.sqrt (k ^ 2 * ∑ a, ‖y a‖ ^ 2) := by
    rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk, vnorm]
  rw [e, vnorm]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h a) 2

private lemma Stability_mul_le_vnorm {D : ℕ} (x y : Fin D → ℂ) (k : ℝ) (hk : 0 ≤ k)
    (h : ∀ a, k * ‖y a‖ ≤ ‖x a‖) : k * vnorm y ≤ vnorm x := by
  have e : k * vnorm y = Real.sqrt (k ^ 2 * ∑ a, ‖y a‖ ^ 2) := by
    rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk, vnorm]
  rw [e, vnorm]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg hk (norm_nonneg _)) (h a) 2

/-- `Σ_a ‖v_a‖² = v^* v`. -/
private lemma Stability_sumsq_eq {D : ℕ} (v : Fin D → ℂ) :
    ((∑ a, ‖v a‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl


/-- `u_l(a) = D^{-1/2} ζ^{l a}` with `ζ = e^{2πi/D}`. -/
private lemma Stability_fv (D : ℕ) (l a : Fin D) :
    fourierVec D l a = ((Real.sqrt D)⁻¹ : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I / D) ^ ((l : ℕ) * (a : ℕ)) := by
  unfold fourierVec
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- `u_0(a) = D^{-1/2}`. -/
private lemma Stability_fv_zero (D : ℕ) (l a : Fin D) (hl : (l : ℕ) = 0) :
    fourierVec D l a = ((Real.sqrt D)⁻¹ : ℂ) := by
  simp [fourierVec, hl]

/-- The Fourier vectors are orthonormal: `Σ_a u_l(a)^* u_k(a) = δ_{lk}`. -/
private lemma Stability_orth (D : ℕ) (hD : D ≠ 0) (l k : Fin D) :
    ∑ a, star (fourierVec D l a) * fourierVec D k a = if l = k then 1 else 0 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / D) with hζdef
  have hζ : IsPrimitiveRoot ζ D := Complex.isPrimitiveRoot_exp D hD
  have hζ1 : ‖ζ‖ = 1 := hζ.norm'_eq_one hD
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζ1
    exact zero_ne_one hζ1
  have hstar : star ζ = ζ⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hζ1]
    simp
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD
  set w : ℂ := ζ ^ ((k : ℤ) - (l : ℤ)) with hw
  have hterm : ∀ a : Fin D, star (fourierVec D l a) * fourierVec D k a =
      (D : ℂ)⁻¹ * w ^ (a : ℕ) := by
    intro a
    rw [Stability_fv, Stability_fv, star_mul', star_pow, hstar]
    have hs : star (((Real.sqrt D)⁻¹ : ℝ) : ℂ) = (((Real.sqrt D)⁻¹ : ℝ) : ℂ) :=
      Complex.conj_ofReal _
    have hsq : (((Real.sqrt D)⁻¹ : ℝ) : ℂ) * (((Real.sqrt D)⁻¹ : ℝ) : ℂ) = (D : ℂ)⁻¹ := by
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hDpos.le]
      push_cast
      rfl
    have hpow : ζ⁻¹ ^ ((l : ℕ) * (a : ℕ)) * ζ ^ ((k : ℕ) * (a : ℕ)) = w ^ (a : ℕ) := by
      rw [hw, ← zpow_natCast (ζ ^ ((k : ℤ) - (l : ℤ))) (a : ℕ), ← _root_.zpow_mul, inv_pow,
        ← zpow_natCast ζ ((l : ℕ) * (a : ℕ)), ← zpow_natCast ζ ((k : ℕ) * (a : ℕ)),
        ← _root_.zpow_neg, ← zpow_add₀ hζ0]
      congr 1
      push_cast
      ring
    push_cast at hs hsq ⊢
    rw [hs]
    calc (↑√↑D)⁻¹ * ζ⁻¹ ^ ((l : ℕ) * (a : ℕ)) * ((↑√↑D)⁻¹ * ζ ^ ((k : ℕ) * (a : ℕ)))
        = ((↑√↑D)⁻¹ * (↑√↑D)⁻¹) * (ζ⁻¹ ^ ((l : ℕ) * (a : ℕ)) * ζ ^ ((k : ℕ) * (a : ℕ))) := by ring
      _ = (D : ℂ)⁻¹ * w ^ (a : ℕ) := by rw [hsq, hpow]
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun i => w ^ i) D]
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  by_cases hlk : l = k
  · subst hlk
    simp [hw, hD']
  · simp only [hlk, ↓reduceIte]
    have hw1 : w ≠ 1 := by
      intro h
      rw [hw, hζ.zpow_eq_one_iff_dvd] at h
      have h0 := Int.eq_zero_of_abs_lt_dvd h (by
        have := l.isLt
        have := k.isLt
        rw [abs_lt]
        constructor <;> omega)
      exact hlk (Fin.ext (by omega))
    have hwD : w ^ D = 1 := by
      rw [hw, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
        hζ.pow_eq_one, _root_.one_zpow]
    rw [geom_sum_eq hw1, hwD]
    simp

/-- The unitary matrix whose columns are the Fourier vectors `u_l`. -/
private def Stability_U (D : ℕ) : Matrix (Fin D) (Fin D) ℂ := Matrix.of fun a l => fourierVec D l a

private lemma Stability_UU (D : ℕ) : (Stability_U D)ᴴ * Stability_U D = 1 := by
  by_cases hD : D = 0
  · subst hD
    ext l
    exact l.elim0
  ext l k
  rw [Matrix.mul_apply, Matrix.one_apply, ← Stability_orth D hD l k]
  rfl

private lemma Stability_UU' (D : ℕ) : Stability_U D * (Stability_U D)ᴴ = 1 :=
  mul_eq_one_comm.mp (Stability_UU D)

/-- Parseval: `|U^* x| = |x|`. -/
private lemma Stability_parseval {D : ℕ} (x : Fin D → ℂ) :
    vnorm ((Stability_U D)ᴴ *ᵥ x) = vnorm x := by
  have h : ((∑ a, ‖((Stability_U D)ᴴ *ᵥ x) a‖ ^ 2 : ℝ) : ℂ) = ((∑ a, ‖x a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Stability_sumsq_eq, Stability_sumsq_eq, star_mulVec, conjTranspose_conjTranspose,
      ← dotProduct_mulVec, mulVec_mulVec, Stability_UU', one_mulVec]
  rw [vnorm, vnorm, Complex.ofReal_injective h]

/-- The coefficient `(U^* v)_l = Σ_a u_l(a)^* v_a`. -/
private lemma Stability_coef {D : ℕ} (v : Fin D → ℂ) (l : Fin D) :
    ((Stability_U D)ᴴ *ᵥ v) l = ∑ a, star (fourierVec D l a) * v a := by
  simp [Stability_U, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]

/-- The `0`-th coefficient is `D^{-1/2} Σ_a v_a`. -/
private lemma Stability_coef_zero {D : ℕ} (v : Fin D → ℂ) (l : Fin D) (hl : (l : ℕ) = 0) :
    ((Stability_U D)ᴴ *ᵥ v) l = ((Real.sqrt D)⁻¹ : ℂ) * ∑ a, v a := by
  rw [Stability_coef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Stability_fv_zero D l a hl]
  simp [Complex.conj_ofReal]

/-- `Σ_a u_l(a) = 0` for `l ≠ 0`. -/
private lemma Stability_sum_fv {D : ℕ} (l : Fin D) (hl : (l : ℕ) ≠ 0) :
    ∑ a, fourierVec D l a = 0 := by
  have hD : D ≠ 0 := by
    intro h
    subst h
    exact l.elim0
  have h0 := Stability_orth D hD ⟨0, Nat.pos_of_ne_zero hD⟩ l
  have hne : (⟨0, Nat.pos_of_ne_zero hD⟩ : Fin D) ≠ l := fun h => hl (by rw [← h])
  simp only [hne, ↓reduceIte] at h0
  have h1 : ((Real.sqrt D)⁻¹ : ℂ) * ∑ a, fourierVec D l a = 0 := by
    rw [← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Stability_fv_zero D ⟨0, Nat.pos_of_ne_zero hD⟩ a rfl]
    simp [Complex.conj_ofReal]
  have hs : ((Real.sqrt D)⁻¹ : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt D := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hD)
    exact inv_ne_zero (by exact_mod_cast this.ne')
  exact (mul_eq_zero.mp h1).resolve_left hs

/-- A matrix with `T u_l = ν_l u_l` for every `l` acts on the Fourier coefficients by
multiplication: `(U^* T v)_l = ν_l (U^* v)_l`. -/
private lemma Stability_coef_mulVec {D : ℕ} (T : Matrix (Fin D) (Fin D) ℂ) (ν : Fin D → ℂ)
    (hT : ∀ l, T *ᵥ fourierVec D l = ν l • fourierVec D l) (v : Fin D → ℂ) (l : Fin D) :
    ((Stability_U D)ᴴ *ᵥ (T *ᵥ v)) l = ν l * ((Stability_U D)ᴴ *ᵥ v) l := by
  have h1 : T * Stability_U D = Stability_U D * Matrix.diagonal ν := by
    ext a k
    rw [Matrix.mul_diagonal]
    have := congrFun (hT k) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply]
    simp only [Stability_U, Matrix.of_apply]
    rw [this, mul_comm]
  have h2 : (Stability_U D)ᴴ * T = Matrix.diagonal ν * (Stability_U D)ᴴ := by
    calc (Stability_U D)ᴴ * T = (Stability_U D)ᴴ * T * (Stability_U D * (Stability_U D)ᴴ) := by
          rw [Stability_UU', Matrix.mul_one]
      _ = (Stability_U D)ᴴ * (T * Stability_U D) * (Stability_U D)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal ν * (Stability_U D)ᴴ := by
          rw [h1, ← Matrix.mul_assoc, Stability_UU, Matrix.one_mul]
  rw [mulVec_mulVec, h2, ← mulVec_mulVec, mulVec_diagonal]

/-- If `T u_l = ν_l u_l` and `‖ν_l‖ ≤ k`, then `|T v| ≤ k |v|`. -/
private lemma Stability_vnorm_mulVec_le {D : ℕ} (T : Matrix (Fin D) (Fin D) ℂ) (ν : Fin D → ℂ)
    (hT : ∀ l, T *ᵥ fourierVec D l = ν l • fourierVec D l) (k : ℝ) (hk : 0 ≤ k)
    (hν : ∀ l, ‖ν l‖ ≤ k) (v : Fin D → ℂ) : vnorm (T *ᵥ v) ≤ k * vnorm v := by
  rw [← Stability_parseval (T *ᵥ v), ← Stability_parseval v]
  refine Stability_vnorm_le_mul _ _ k hk fun l => ?_
  rw [Stability_coef_mulVec T ν hT, norm_mul]
  exact mul_le_mul_of_nonneg_right (hν l) (norm_nonneg _)

/-- If `T u_l = ν_l u_l` and `‖ν_l‖ ≥ k ≥ 0`, then `|T v| ≥ k |v|`. -/
private lemma Stability_vnorm_mulVec_ge {D : ℕ} (T : Matrix (Fin D) (Fin D) ℂ) (ν : Fin D → ℂ)
    (hT : ∀ l, T *ᵥ fourierVec D l = ν l • fourierVec D l) (k : ℝ) (hk : 0 ≤ k)
    (hν : ∀ l, k ≤ ‖ν l‖) (v : Fin D → ℂ) : k * vnorm v ≤ vnorm (T *ᵥ v) := by
  rw [← Stability_parseval (T *ᵥ v), ← Stability_parseval v]
  refine Stability_mul_le_vnorm _ _ k hk fun l => ?_
  rw [Stability_coef_mulVec T ν hT, norm_mul]
  exact mul_le_mul_of_nonneg_right (hν l) (norm_nonneg _)

/-- `(σ_θ v)_a = θ v_a + (1 - θ) D⁻¹ Σ_b v_b`. -/
private lemma Stability_sig_apply (D : ℕ) (θ : ℝ) (v : Fin D → ℂ) (a : Fin D) :
    (sigTheta D θ *ᵥ v) a = (θ : ℂ) * v a + ((1 - θ : ℝ) : ℂ) * ((D : ℂ)⁻¹ * ∑ b, v b) := by
  have hJ : (Matrix.of fun (_ _ : Fin D) => (1 : ℂ)) *ᵥ v = fun _ => ∑ b, v b := by
    ext
    simp [Matrix.mulVec, dotProduct]
  simp only [sigTheta, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hJ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- `σ_θ u_l = θ_l u_l` with `θ_0 = 1` and `θ_l = θ` for `l ≠ 0`; `D ≥ 1`. -/
private lemma Stability_sig_eigvec (D : ℕ) (θ : ℝ) (l : Fin D) :
    sigTheta D θ *ᵥ fourierVec D l =
      (if (l : ℕ) = 0 then 1 else (θ : ℂ)) • fourierVec D l := by
  have hD : D ≠ 0 := by
    intro h
    subst h
    exact l.elim0
  funext a
  rw [Stability_sig_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hl : (l : ℕ) = 0
  · simp only [hl, ↓reduceIte, one_mul]
    simp only [Stability_fv_zero D l _ hl, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
    field_simp
    push_cast
    ring
  · simp only [hl, ↓reduceIte, Stability_sum_fv l hl, mul_zero, add_zero]

/-- Each entry of `Q_t(y)_a = Σ_{b,c} t_{abc} y_b y_c` is at most `D² T |y|²` when
`‖t_{abc}‖ ≤ T`. -/
private lemma Stability_quad_coord {D : ℕ} (t : Fin D → Fin D → Fin D → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (ht : ∀ a b c, ‖t a b c‖ ≤ T) (y : Fin D → ℂ) (a : Fin D) :
    ‖quadForm t y a‖ ≤ D ^ 2 * T * vnorm y ^ 2 := by
  unfold quadForm
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b, ‖∑ c, t a b c * y b * y c‖ ≤ ∑ _b : Fin D, ∑ _c : Fin D, T * vnorm y * vnorm y := by
        refine Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (ht a b c) (Stability_coord_le y b) (norm_nonneg _) hT)
          (Stability_coord_le y c) (norm_nonneg _) (mul_nonneg hT (Stability_vnorm_nonneg y))
    _ = D ^ 2 * T * vnorm y ^ 2 := by simp; ring

/-- `|Q_t(y)| ≤ D³ T |y|²` when `‖t_{abc}‖ ≤ T`. -/
private lemma Stability_quad_le {D : ℕ} (t : Fin D → Fin D → Fin D → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (ht : ∀ a b c, ‖t a b c‖ ≤ T) (y : Fin D → ℂ) :
    vnorm (quadForm t y) ≤ D ^ 3 * T * vnorm y ^ 2 := by
  have h := Stability_vnorm_le_of_coord (quadForm t y) _ (by positivity)
    (Stability_quad_coord t T hT ht y)
  calc vnorm (quadForm t y) ≤ D * (D ^ 2 * T * vnorm y ^ 2) := h
    _ = D ^ 3 * T * vnorm y ^ 2 := by ring

/-- `Q_q(y) = q₀ (y_a²)_a + Q_e(y)` with `e_{abc} = q_{abc} - q₀ δ_{abc}`. -/
private lemma Stability_quad_split {D : ℕ} (q : Fin D → Fin D → Fin D → ℂ) (q₀ : ℂ)
    (y : Fin D → ℂ) :
    quadForm q y = q₀ • (fun a => y a ^ 2) +
      quadForm (fun a b c => q a b c - (if a = b ∧ b = c then q₀ else 0)) y := by
  funext a
  simp only [quadForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
  have h : ∑ b, ∑ c, (if a = b ∧ b = c then q₀ else 0) * y b * y c = q₀ * y a ^ 2 := by
    rw [Finset.sum_eq_single a, Finset.sum_eq_single a]
    · simp [sq, mul_assoc]
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [Ne.symm hb]
    · simp
  rw [h]
  ring

/-- `|y|² ≤ D |(y_a²)_a|` (Cauchy–Schwarz). -/
private lemma Stability_sq_lower {D : ℕ} (y : Fin D → ℂ) :
    vnorm y ^ 2 ≤ D * vnorm (fun a => y a ^ 2) := by
  have hR : vnorm (fun a => y a ^ 2) ^ 2 = ∑ a, (‖y a‖ ^ 2) ^ 2 := by
    rw [Stability_vnorm_sq]
    simp [norm_pow]
  have hCS : (∑ a, ‖y a‖ ^ 2) ^ 2 ≤ D * ∑ a, (‖y a‖ ^ 2) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a : Fin D => ‖y a‖ ^ 2)
    simpa using this
  rw [Stability_vnorm_sq]
  have h0 : 0 ≤ ∑ a, ‖y a‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : 0 ≤ (D : ℝ) * vnorm (fun a => y a ^ 2) :=
    mul_nonneg (Nat.cast_nonneg _) (Stability_vnorm_nonneg _)
  refine (pow_le_pow_iff_left₀ h0 h1 two_ne_zero).mp ?_
  calc (∑ a, ‖y a‖ ^ 2) ^ 2 ≤ D * ∑ a, (‖y a‖ ^ 2) ^ 2 := hCS
    _ ≤ (D : ℝ) ^ 2 * ∑ a, (‖y a‖ ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right (Stability_D_le_sq D)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = (D * vnorm (fun a => y a ^ 2)) ^ 2 := by rw [mul_pow, hR]

/-- The linear regime in numbers. -/
private lemma Stability_regL (Cs C' ρ d rbar n : ℝ) (hCs : 0 < Cs) (hC' : 0 ≤ C') (hd : 0 < d)
    (hn : 0 ≤ n) (h8 : 8 * Cs ^ 2 * ρ ^ 2 * C' ≤ 1) (hL : rbar ≤ ρ ^ 2 * d ^ 2)
    (hS : d * n ≤ Cs * (rbar + C' * n ^ 2)) (h2 : n ≤ 2 * (2 * Cs * rbar / d)) :
    n ≤ 2 * Cs * rbar / d := by
  rw [le_div_iff₀ hd]
  have h2' : n * d ≤ 4 * Cs * rbar := by
    have := (le_div_iff₀ hd).mp (show n ≤ 4 * Cs * rbar / d by
      calc n ≤ 2 * (2 * Cs * rbar / d) := h2
        _ = 4 * Cs * rbar / d := by ring)
    exact this
  have h3 : n * d ≤ 4 * Cs * ρ ^ 2 * d * d := by nlinarith
  have h4 : n ≤ 4 * Cs * ρ ^ 2 * d := le_of_mul_le_mul_right (by linarith) hd
  have h5 : Cs * (C' * n ^ 2) ≤ d * n / 2 := by
    have e1 : Cs * (C' * n ^ 2) = (Cs * C' * n) * n := by ring
    have e2 : Cs * C' * n ≤ Cs * C' * (4 * Cs * ρ ^ 2 * d) :=
      mul_le_mul_of_nonneg_left h4 (mul_nonneg hCs.le hC')
    have e3 : Cs * C' * (4 * Cs * ρ ^ 2 * d) = (8 * Cs ^ 2 * ρ ^ 2 * C') * (d / 2) := by ring
    have e4 : (8 * Cs ^ 2 * ρ ^ 2 * C') * (d / 2) ≤ d / 2 := by nlinarith
    rw [e1]
    calc Cs * C' * n * n ≤ (d / 2) * n := mul_le_mul_of_nonneg_right (by linarith) hn
      _ = d * n / 2 := by ring
  nlinarith

/-- The quadratic regime A in numbers. -/
private lemma Stability_regA (Dr Cu K₁ K₃ cq ρ KA σ₀ s d a n : ℝ) (hDr : 0 < Dr) (hCu : 0 < Cu)
    (hK₃ : 0 ≤ K₃) (hcq : 0 < cq) (hρ : 0 < ρ) (hs : 0 < s) (hn : 0 ≤ n)
    (hsσ : s ≤ σ₀) (hρd : ρ * d < s) (ha : a ≤ K₁ * s)
    (hKA1 : 32 * Dr * Cu * (1 + ρ * K₁) ≤ cq * ρ * KA) (hKA2 : 32 * Dr ≤ cq * KA ^ 2)
    (hK : 32 * Dr * KA * K₃ * σ₀ ≤ cq) (hKA : 0 < KA)
    (h : cq * n ^ 2 ≤ 8 * Dr * (Cu * (d + a) * n + s ^ 2 + K₃ * n ^ 3))
    (h2 : n ≤ 2 * (KA * s)) : n ≤ KA * s := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hK3n : 16 * Dr * K₃ * n ≤ cq := by
    have : 16 * Dr * K₃ * n ≤ 16 * Dr * K₃ * (2 * (KA * s)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h' : 16 * Dr * K₃ * (2 * (KA * s)) ≤ 32 * Dr * KA * K₃ * σ₀ := by
      have : 16 * Dr * K₃ * (2 * (KA * s)) = (32 * Dr * KA * K₃) * s := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hsσ (by positivity)
    linarith
  have hcub : 8 * Dr * (K₃ * n ^ 3) ≤ cq / 2 * n ^ 2 := by
    have : 8 * Dr * (K₃ * n ^ 3) = (16 * Dr * K₃ * n) * (n ^ 2 / 2) := by ring
    rw [this]
    calc (16 * Dr * K₃ * n) * (n ^ 2 / 2) ≤ cq * (n ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hK3n (by positivity)
      _ = cq / 2 * n ^ 2 := by ring
  have hlin : ρ * (Cu * (d + a)) ≤ Cu * (1 + ρ * K₁) * s := by
    have : ρ * (d + a) ≤ s + ρ * (K₁ * s) := by nlinarith
    nlinarith
  have hmain : cq * ρ / 2 * n ^ 2 ≤ 8 * Dr * (Cu * (1 + ρ * K₁) * s) * n + 8 * Dr * ρ * s ^ 2 := by
    have e1 : cq / 2 * n ^ 2 ≤ 8 * Dr * (Cu * (d + a)) * n + 8 * Dr * s ^ 2 := by nlinarith
    have e2 : 8 * Dr * (ρ * (Cu * (d + a))) * n ≤ 8 * Dr * (Cu * (1 + ρ * K₁) * s) * n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlin (by positivity)) hn
    nlinarith
  have hn0 : 0 < n := lt_of_le_of_lt (by positivity) hlt
  have t1 : 8 * Dr * (Cu * (1 + ρ * K₁) * s) * n < cq * ρ / 4 * n ^ 2 := by
    have : 8 * Dr * (Cu * (1 + ρ * K₁) * s) * n = (32 * Dr * Cu * (1 + ρ * K₁)) * s * n / 4 := by
      ring
    rw [this]
    have h1 : (32 * Dr * Cu * (1 + ρ * K₁)) * s * n ≤ (cq * ρ * KA) * s * n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKA1 hs.le) hn
    have h3 : (cq * ρ * KA) * s * n < (cq * ρ) * n * n := by
      have : (cq * ρ * KA) * s * n = (cq * ρ) * (KA * s) * n := by ring
      rw [this]
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlt (by positivity)) hn0
    nlinarith
  have t2 : 8 * Dr * ρ * s ^ 2 < cq * ρ / 4 * n ^ 2 := by
    have h1 : 32 * Dr * ρ * s ^ 2 ≤ cq * KA ^ 2 * ρ * s ^ 2 := by
      have := mul_le_mul_of_nonneg_right hKA2 (by positivity : 0 ≤ ρ * s ^ 2)
      nlinarith
    have h3 : (KA * s) ^ 2 < n ^ 2 := by
      exact pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
    have h4 : cq * ρ * (KA * s) ^ 2 < cq * ρ * n ^ 2 := mul_lt_mul_of_pos_left h3 (by positivity)
    nlinarith
  linarith

/-- The transverse bound of the quadratic regime B in numbers. -/
private lemma Stability_regB_trans (cB ε' KB K₁ Cq s a nw R : ℝ) (hcB : 0 < cB) (hε' : 0 < ε')
    (hKB : 0 < KB) (hCq : 0 ≤ Cq) (hs : 0 < s) (ha : K₁ * s < a)
    (hK1 : 2 + 4 * Cq * KB ^ 2 ≤ cB * ε' * KB * K₁)
    (h : cB * a * nw ≤ R) (hR : R ≤ (2 + 4 * Cq * KB ^ 2) * s ^ 2) : nw ≤ ε' * KB * s := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hK₁ : 0 < K₁ := by
    have : 0 < cB * ε' * KB * K₁ := lt_of_lt_of_le (by positivity) hK1
    have h0 : 0 < cB * ε' * KB := by positivity
    exact pos_of_mul_pos_right this h0.le
  have e1 : cB * (K₁ * s) * nw < cB * a * nw := by
    have hnw0 : 0 < nw := lt_of_le_of_lt (by positivity) hlt
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left ha hcB) hnw0
  have e2 : cB * (K₁ * s) * (ε' * KB * s) < cB * (K₁ * s) * nw :=
    mul_lt_mul_of_pos_left hlt (by positivity)
  have e3 : cB * (K₁ * s) * (ε' * KB * s) = (cB * ε' * KB * K₁) * s ^ 2 := by ring
  have e4 : (2 + 4 * Cq * KB ^ 2) * s ^ 2 ≤ (cB * ε' * KB * K₁) * s ^ 2 :=
    mul_le_mul_of_nonneg_right hK1 (sq_nonneg s)
  linarith

/-- The mean mode of the quadratic regime B in numbers. -/
private lemma Stability_regB_mean (Dr C₁ cq ρ KB ε' ε₀ s d n nw nf : ℝ) (hDr : 0 < Dr)
    (hC₁ : 0 < C₁) (hcq : 0 < cq) (hρ : 0 < ρ) (hKB : 0 < KB) (hs : 0 < s)
    (hn : 0 ≤ n) (hρd : ρ * d < s) (hlow : KB * s < n) (hup : n ≤ 2 * (KB * s))
    (hnw : nw ≤ ε' * KB * s) (hnw0 : 0 ≤ nw) (hnf : nf ≤ 2 * s ^ 2)
    (hKB1 : 16 * C₁ * Dr ≤ cq * ρ * KB) (hKB2 : 16 * Dr ≤ cq * KB ^ 2)
    (hε'c : 8 * (1 + cq) * ε' ^ 2 ≤ cq) (hε₀c : 32 * Dr ^ 3 * ε₀ ≤ cq)
    (h : cq * (n ^ 2 - nw ^ 2) ≤ C₁ * d * Dr * n + Dr * nf + nw ^ 2 + Dr ^ 3 * ε₀ * n ^ 2) :
    False := by
  set X := (KB * s) ^ 2 with hX
  have hXn : X < n ^ 2 := pow_lt_pow_left₀ hlow (by positivity) two_ne_zero
  have t1 : (1 + cq) * nw ^ 2 ≤ cq / 8 * X := by
    have : nw ^ 2 ≤ (ε' * KB * s) ^ 2 := pow_le_pow_left₀ hnw0 hnw 2
    have e : (ε' * KB * s) ^ 2 = ε' ^ 2 * X := by rw [hX]; ring
    rw [e] at this
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1 + cq)
    have h' : (1 + cq) * (ε' ^ 2 * X) ≤ cq / 8 * X := by
      have : (1 + cq) * (ε' ^ 2 * X) = ((8 * (1 + cq) * ε' ^ 2) / 8) * X := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have t2 : C₁ * d * Dr * n ≤ cq / 8 * X := by
    have e1 : ρ * (C₁ * d * Dr * n) ≤ (C₁ * Dr * n) * s := by
      have : ρ * (C₁ * d * Dr * n) = (C₁ * Dr * n) * (ρ * d) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hρd.le (by positivity)
    have e2 : (C₁ * Dr * n) * s ≤ (C₁ * Dr * (2 * (KB * s))) * s :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hup (by positivity)) hs.le
    have e3 : (C₁ * Dr * (2 * (KB * s))) * s = (16 * C₁ * Dr) * KB * s ^ 2 / 8 := by ring
    have e4 : (16 * C₁ * Dr) * KB * s ^ 2 / 8 ≤ (cq * ρ * KB) * KB * s ^ 2 / 8 := by
      have := mul_le_mul_of_nonneg_right hKB1 (by positivity : (0 : ℝ) ≤ KB * s ^ 2)
      nlinarith
    have e5 : (cq * ρ * KB) * KB * s ^ 2 / 8 = ρ * (cq / 8 * X) := by rw [hX]; ring
    have : ρ * (C₁ * d * Dr * n) ≤ ρ * (cq / 8 * X) := by linarith
    exact le_of_mul_le_mul_left this hρ
  have t3 : Dr * nf ≤ cq / 8 * X := by
    have e1 : Dr * nf ≤ Dr * (2 * s ^ 2) := mul_le_mul_of_nonneg_left hnf hDr.le
    have e2 : Dr * (2 * s ^ 2) = (16 * Dr) * s ^ 2 / 8 := by ring
    have e3 : (16 * Dr) * s ^ 2 / 8 ≤ (cq * KB ^ 2) * s ^ 2 / 8 := by
      have := mul_le_mul_of_nonneg_right hKB2 (sq_nonneg s)
      linarith
    have e4 : (cq * KB ^ 2) * s ^ 2 / 8 = cq / 8 * X := by rw [hX]; ring
    linarith
  have t4 : Dr ^ 3 * ε₀ * n ^ 2 ≤ cq / 32 * n ^ 2 := by
    have : Dr ^ 3 * ε₀ ≤ cq / 32 := by linarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg n)
  have hX0 : 0 ≤ X := by positivity
  nlinarith

/-- The mean `m = D⁻¹ Σ_a x_a`. -/
private def Stability_mean {D : ℕ} (x : Fin D → ℂ) : ℂ := (∑ a, x a) / D

/-- The transverse part `x - m 𝟙`. -/
private def Stability_perp {D : ℕ} (x : Fin D → ℂ) : Fin D → ℂ := fun a => x a - Stability_mean x

private lemma Stability_sum_x {D : ℕ} (hD : 1 ≤ D) (x : Fin D → ℂ) :
    ∑ a, x a = D * Stability_mean x := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  rw [Stability_mean]
  field_simp

private lemma Stability_sum_perp {D : ℕ} (hD : 1 ≤ D) (x : Fin D → ℂ) :
    ∑ a, Stability_perp x a = 0 := by
  simp only [Stability_perp, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Stability_sum_x hD x]
  ring

/-- `|x|² = D |m|² + |x - m 𝟙|²`. -/
private lemma Stability_pyth {D : ℕ} (hD : 1 ≤ D) (x : Fin D → ℂ) :
    vnorm x ^ 2 = D * ‖Stability_mean x‖ ^ 2 + vnorm (Stability_perp x) ^ 2 := by
  have hxw : ∀ a, x a = Stability_mean x + Stability_perp x a := fun a => by
    simp [Stability_perp]
  have h1 : ((vnorm x ^ 2 : ℝ) : ℂ) =
      ((D * ‖Stability_mean x‖ ^ 2 + vnorm (Stability_perp x) ^ 2 : ℝ) : ℂ) := by
    rw [Stability_vnorm_sq, Stability_vnorm_sq]
    push_cast
    simp only [← Complex.conj_mul']
    have hx : ∀ a, (starRingEnd ℂ) (x a) * x a = (starRingEnd ℂ) (Stability_mean x +
        Stability_perp x a) * (Stability_mean x + Stability_perp x a) := fun a => by rw [← hxw a]
    rw [Finset.sum_congr rfl fun a _ => hx a]
    simp only [map_add, add_mul, mul_add, Finset.sum_add_distrib]
    have h1 : ∑ a, (starRingEnd ℂ) (Stability_mean x) * Stability_perp x a = 0 := by
      rw [← Finset.mul_sum, Stability_sum_perp hD x, mul_zero]
    have h2 : ∑ a, (starRingEnd ℂ) (Stability_perp x a) * Stability_mean x = 0 := by
      rw [← Finset.sum_mul, ← map_sum, Stability_sum_perp hD x, map_zero, zero_mul]
    simp only [h1, h2, add_zero, zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  exact_mod_cast h1

/-- The transverse bound: if `L u_l = μ_l u_l` and `|μ_l| ≥ k ≥ 0` for `l ≠ 0`, then
`k |x - m 𝟙| ≤ |L x|`. -/
private lemma Stability_trans {D : ℕ} (hD : 1 ≤ D) (L : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ)
    (hL : ∀ l, L *ᵥ fourierVec D l = μ l • fourierVec D l) (k : ℝ) (hk : 0 ≤ k)
    (hN2 : ∀ l : Fin D, (l : ℕ) ≠ 0 → k ≤ ‖μ l‖) (x : Fin D → ℂ) :
    k * vnorm (Stability_perp x) ≤ vnorm (L *ᵥ x) := by
  rw [← Stability_parseval (Stability_perp x), ← Stability_parseval (L *ᵥ x)]
  refine Stability_mul_le_vnorm _ _ k hk fun l => ?_
  by_cases hl : (l : ℕ) = 0
  · rw [Stability_coef_zero _ l hl, Stability_sum_perp hD x, mul_zero, norm_zero, mul_zero]
    exact norm_nonneg _
  · have hcw : ((Stability_U D)ᴴ *ᵥ Stability_perp x) l = ((Stability_U D)ᴴ *ᵥ x) l := by
      rw [Stability_coef, Stability_coef]
      simp only [Stability_perp, mul_sub, Finset.sum_sub_distrib]
      have : ∑ a, star (fourierVec D l a) * Stability_mean x = 0 := by
        rw [← Finset.sum_mul, ← star_sum, Stability_sum_fv l hl, star_zero, zero_mul]
      rw [this, sub_zero]
    rw [hcw, Stability_coef_mulVec L μ hL x l, norm_mul]
    exact mul_le_mul_of_nonneg_right (hN2 l hl) (norm_nonneg _)

/-- The mean-mode identity: with `y = σ_θ x`, `e = q - q₀ δ` and `f = L x - Q(y)`,
`q₀ D m² = μ_0 D m - Σ_a f_a - q₀ θ² Σ_a w_a² - Σ_a Q_e(y)_a`, where `w = x - m 𝟙`. -/
private lemma Stability_mean_eq {D : ℕ} (hD : 1 ≤ D) (θ : ℝ) (L : Matrix (Fin D) (Fin D) ℂ)
    (μ : Fin D → ℂ) (hL : ∀ l, L *ᵥ fourierVec D l = μ l • fourierVec D l)
    (q : Fin D → Fin D → Fin D → ℂ) (q₀ : ℂ) (x : Fin D → ℂ) :
    q₀ * (D * Stability_mean x ^ 2) = μ ⟨0, hD⟩ * (D * Stability_mean x) -
      (∑ a, (L *ᵥ x - quadForm q (sigTheta D θ *ᵥ x)) a) -
      q₀ * (θ : ℂ) ^ 2 * (∑ a, Stability_perp x a ^ 2) -
      ∑ a, quadForm (fun a b c => q a b c - (if a = b ∧ b = c then q₀ else 0))
        (sigTheta D θ *ᵥ x) a := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hSx := Stability_sum_x hD x
  have hSw := Stability_sum_perp hD x
  have hxw : ∀ a, x a = Stability_mean x + Stability_perp x a := fun a => by
    simp [Stability_perp]
  have hSL : ∑ a, (L *ᵥ x) a = μ ⟨0, hD⟩ * ∑ a, x a := by
    have h1 := Stability_coef_mulVec L μ hL x ⟨0, hD⟩
    rw [Stability_coef_zero _ _ rfl, Stability_coef_zero _ _ rfl] at h1
    have hs : ((Real.sqrt D)⁻¹ : ℂ) ≠ 0 := by
      have : (0 : ℝ) < Real.sqrt D := Real.sqrt_pos.mpr hDpos
      exact inv_ne_zero (by exact_mod_cast this.ne')
    refine mul_left_cancel₀ hs ?_
    rw [h1]
    ring
  have hyw : ∀ a, (sigTheta D θ *ᵥ x) a = Stability_mean x + (θ : ℂ) * Stability_perp x a := by
    intro a
    rw [Stability_sig_apply, hSx, hxw a]
    have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
    field_simp
    push_cast
    ring
  have hSy2 : ∑ a, (sigTheta D θ *ᵥ x) a ^ 2 =
      D * Stability_mean x ^ 2 + (θ : ℂ) ^ 2 * ∑ a, Stability_perp x a ^ 2 := by
    rw [Finset.sum_congr rfl fun a _ => by rw [hyw a]]
    have : ∀ a, (Stability_mean x + (θ : ℂ) * Stability_perp x a) ^ 2 =
        Stability_mean x ^ 2 + (2 * Stability_mean x * θ) * Stability_perp x a +
          (θ : ℂ) ^ 2 * Stability_perp x a ^ 2 := fun a => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hSw, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hSQ : ∑ a, quadForm q (sigTheta D θ *ᵥ x) a =
      q₀ * (∑ a, (sigTheta D θ *ᵥ x) a ^ 2) +
        ∑ a, quadForm (fun a b c => q a b c - (if a = b ∧ b = c then q₀ else 0))
          (sigTheta D θ *ᵥ x) a := by
    rw [Stability_quad_split q q₀ (sigTheta D θ *ᵥ x)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  rw [hSL, hSQ, hSy2, hSx]
  ring

/-- The mean-mode inequality: `c_q (|x|² - |w|²) ≤ C₁ d D |x| + D |f| + |w|² + D³ ε₀ |x|²`. -/
private lemma Stability_mean_le {D : ℕ} (hD : 1 ≤ D) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (L : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ)
    (hL : ∀ l, L *ᵥ fourierVec D l = μ l • fourierVec D l) (C₁ d cq ε₀ : ℝ) (hε₀ : 0 ≤ ε₀)
    (hμ0 : ‖μ ⟨0, hD⟩‖ ≤ C₁ * d) (q : Fin D → Fin D → Fin D → ℂ) (q₀ : ℂ) (hcq : cq ≤ ‖q₀‖)
    (hq1 : ‖q₀‖ ≤ 1)
    (he : ∀ a b c, ‖q a b c - (if a = b ∧ b = c then q₀ else 0)‖ ≤ ε₀) (x : Fin D → ℂ) :
    cq * (vnorm x ^ 2 - vnorm (Stability_perp x) ^ 2) ≤
      C₁ * d * D * vnorm x + D * vnorm (L *ᵥ x - quadForm q (sigTheta D θ *ᵥ x)) +
        vnorm (Stability_perp x) ^ 2 + (D : ℝ) ^ 3 * ε₀ * vnorm x ^ 2 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  set m := Stability_mean x with hm
  set w := Stability_perp x with hw
  set y := sigTheta D θ *ᵥ x with hy
  set f := L *ᵥ x - quadForm q y with hf
  set e : Fin D → Fin D → Fin D → ℂ := fun a b c => q a b c - (if a = b ∧ b = c then q₀ else 0)
    with he_def
  have key := Stability_mean_eq hD θ L μ hL q q₀ x
  have hnorm : ‖q₀‖ * (D * ‖m‖ ^ 2) ≤ ‖μ ⟨0, hD⟩‖ * (D * ‖m‖) + ‖∑ a, f a‖ +
      ‖q₀‖ * θ ^ 2 * ‖∑ a, w a ^ 2‖ + ‖∑ a, quadForm e y a‖ := by
    have e1 : ‖q₀ * (D * m ^ 2)‖ = ‖q₀‖ * (D * ‖m‖ ^ 2) := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have e2 : ‖μ ⟨0, hD⟩ * (D * m)‖ = ‖μ ⟨0, hD⟩‖ * (D * ‖m‖) := by
      rw [norm_mul, norm_mul, Complex.norm_natCast]
    have e3 : ‖q₀ * (θ : ℂ) ^ 2 * ∑ a, w a ^ 2‖ = ‖q₀‖ * θ ^ 2 * ‖∑ a, w a ^ 2‖ := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [← e1, key, ← e2, ← e3]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans ?_) le_rfl
    exact add_le_add (norm_sub_le _ _) le_rfl
  have hn2 := Stability_pyth hD x
  have hm_le : ‖m‖ ≤ vnorm x := by
    have h1 : ‖∑ a, x a‖ ≤ D * vnorm x := Stability_sum_le_of_coord x _ (Stability_coord_le x)
    rw [Stability_sum_x hD x, norm_mul, Complex.norm_natCast] at h1
    exact le_of_mul_le_mul_left h1 hDpos
  have hfs : ‖∑ a, f a‖ ≤ D * vnorm f := Stability_sum_le_of_coord f _ (Stability_coord_le f)
  have hws : ‖∑ a, w a ^ 2‖ ≤ vnorm w ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    rw [Stability_vnorm_sq]
    simp [norm_pow]
  have hyle : vnorm y ≤ vnorm x := by
    have := Stability_vnorm_mulVec_le (sigTheta D θ) _ (Stability_sig_eigvec D θ) 1 zero_le_one
      (fun l => by
        split_ifs
        · simp
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ0]
          exact hθ1) x
    linarith
  have hEs : ‖∑ a, quadForm e y a‖ ≤ (D : ℝ) ^ 3 * ε₀ * vnorm x ^ 2 := by
    have h1 := Stability_sum_le_of_coord (quadForm e y) _ (Stability_quad_coord e ε₀ hε₀ he y)
    have h2 : vnorm y ^ 2 ≤ vnorm x ^ 2 := pow_le_pow_left₀ (Stability_vnorm_nonneg y) hyle 2
    calc ‖∑ a, quadForm e y a‖ ≤ D * ((D : ℝ) ^ 2 * ε₀ * vnorm y ^ 2) := h1
      _ ≤ D * ((D : ℝ) ^ 2 * ε₀ * vnorm x ^ 2) := by gcongr
      _ = (D : ℝ) ^ 3 * ε₀ * vnorm x ^ 2 := by ring
  have t0 : cq * (vnorm x ^ 2 - vnorm w ^ 2) ≤ ‖q₀‖ * (D * ‖m‖ ^ 2) := by
    rw [hn2]
    have : (D : ℝ) * ‖m‖ ^ 2 + vnorm w ^ 2 - vnorm w ^ 2 = D * ‖m‖ ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hcq (by positivity)
  have t1 : ‖μ ⟨0, hD⟩‖ * (D * ‖m‖) ≤ C₁ * d * D * vnorm x := by
    have := mul_le_mul hμ0 (mul_le_mul_of_nonneg_left hm_le hDpos.le) (by positivity)
      ((norm_nonneg _).trans hμ0)
    linarith
  have t2 : ‖q₀‖ * θ ^ 2 * ‖∑ a, w a ^ 2‖ ≤ vnorm w ^ 2 := by
    have hθ2 : θ ^ 2 ≤ 1 := pow_le_one₀ hθ0 hθ1
    have h1 : ‖q₀‖ * θ ^ 2 ≤ 1 := by
      have := mul_le_mul hq1 hθ2 (sq_nonneg θ) zero_le_one
      linarith
    calc ‖q₀‖ * θ ^ 2 * ‖∑ a, w a ^ 2‖ ≤ 1 * vnorm w ^ 2 :=
          mul_le_mul h1 hws (norm_nonneg _) zero_le_one
      _ = vnorm w ^ 2 := one_mul _
  linarith

/-- The lower bound of the quadratic term: `c_q |y|² ≤ 2 D |Q(y)|` when `c_q ≤ |q₀|` and
`32 D⁴ ε₀ ≤ c_q`. -/
private lemma Stability_quad_ge {D : ℕ} (q : Fin D → Fin D → Fin D → ℂ) (q₀ : ℂ) (cq ε₀ : ℝ)
    (hε₀ : 0 ≤ ε₀) (hcq : cq ≤ ‖q₀‖) (hε₀c : 32 * (D : ℝ) ^ 4 * ε₀ ≤ cq)
    (he : ∀ a b c, ‖q a b c - (if a = b ∧ b = c then q₀ else 0)‖ ≤ ε₀) (y : Fin D → ℂ) :
    cq * vnorm y ^ 2 ≤ 2 * D * vnorm (quadForm q y) := by
  set e : Fin D → Fin D → Fin D → ℂ := fun a b c => q a b c - (if a = b ∧ b = c then q₀ else 0)
    with he_def
  have hsplit := Stability_quad_split q q₀ y
  have h1 : q₀ • (fun a => y a ^ 2) = quadForm q y - quadForm e y := by
    rw [hsplit]; abel
  have h2 : ‖q₀‖ * vnorm (fun a => y a ^ 2) ≤ vnorm (quadForm q y) + vnorm (quadForm e y) := by
    rw [← Stability_vnorm_smul, h1]
    exact Stability_vnorm_sub _ _
  have h3 : vnorm (quadForm e y) ≤ (D : ℝ) ^ 3 * ε₀ * vnorm y ^ 2 :=
    Stability_quad_le e ε₀ hε₀ he y
  have h4 := Stability_sq_lower y
  have hcq0 : 0 ≤ cq := le_trans (by positivity) hε₀c
  have h5 : cq * vnorm y ^ 2 ≤ cq * (D * vnorm (fun a => y a ^ 2)) :=
    mul_le_mul_of_nonneg_left h4 hcq0
  have h6 : cq * (D * vnorm (fun a => y a ^ 2)) ≤ D * (‖q₀‖ * vnorm (fun a => y a ^ 2)) := by
    have := mul_le_mul_of_nonneg_right hcq (Stability_vnorm_nonneg (fun a => y a ^ 2))
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    nlinarith
  have h7 : (D : ℝ) * (‖q₀‖ * vnorm (fun a => y a ^ 2)) ≤
      D * vnorm (quadForm q y) + D * ((D : ℝ) ^ 3 * ε₀ * vnorm y ^ 2) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (h2.trans (by linarith)) (Nat.cast_nonneg D)
  have h8 : (D : ℝ) * ((D : ℝ) ^ 3 * ε₀ * vnorm y ^ 2) ≤ cq / 32 * vnorm y ^ 2 := by
    have : (D : ℝ) * ((D : ℝ) ^ 3 * ε₀ * vnorm y ^ 2) = ((D : ℝ) ^ 4 * ε₀) * vnorm y ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hQ0 : 0 ≤ (D : ℝ) * vnorm (quadForm q y) :=
    mul_nonneg (Nat.cast_nonneg D) (Stability_vnorm_nonneg _)
  have hy0 : 0 ≤ cq * vnorm y ^ 2 := mul_nonneg hcq0 (sq_nonneg _)
  linarith

/-- The dichotomy of the stability step of Lemma 2.9 [lem_loc] for given constants satisfying the
closing inequalities of the linear and the two quadratic regimes. -/
private lemma Stability_core (D : ℕ) (hD : 1 ≤ D) (Cs Cu C₁ cB cq K₃ : ℝ) (hCs : 0 < Cs)
    (hCu : 0 < Cu) (hC₁ : 0 < C₁) (hcB : 0 < cB) (hcq : 0 < cq) (hK₃ : 0 ≤ K₃)
    (ρ K₁ KA KB σ₀ ε₀ ε' : ℝ) (hρ : 0 < ρ) (hK₁ : 0 < K₁) (hKA : 0 < KA) (hKB : 0 < KB)
    (hσ₀ : 0 < σ₀) (hε' : 0 < ε') (hε₀1 : ε₀ ≤ 1)
    (h8 : 8 * Cs ^ 2 * ρ ^ 2 * (2 * (D : ℝ) ^ 3 + K₃) ≤ 1)
    (hKB1 : 16 * C₁ * D ≤ cq * ρ * KB) (hKB2 : 16 * (D : ℝ) ≤ cq * KB ^ 2)
    (hε'c : 8 * (1 + cq) * ε' ^ 2 ≤ cq) (hε₀c : 32 * (D : ℝ) ^ 4 * ε₀ ≤ cq)
    (hK1 : 2 + 4 * (2 * (D : ℝ) ^ 3) * KB ^ 2 ≤ cB * ε' * KB * K₁)
    (h8K : 8 * K₃ * KB ^ 3 * σ₀ ≤ 1) (h2K₁ : 2 * K₁ * σ₀ ≤ 1)
    (hKA1 : 32 * D * Cu * (1 + ρ * K₁) ≤ cq * ρ * KA) (hKA2 : 32 * (D : ℝ) ≤ cq * KA ^ 2)
    (hK : 32 * D * KA * K₃ * σ₀ ≤ cq) :
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ (L : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ),
      (∀ l, L *ᵥ fourierVec D l = μ l • fourierVec D l) →
      ∀ d a : ℝ, 0 < d → 1 - θ ≤ a →
      (∀ l, d / Cs ≤ ‖μ l‖) → (∀ l, ‖μ l‖ ≤ Cu * (d + a)) →
      (∀ l : Fin D, (l : ℕ) = 0 → ‖μ l‖ ≤ C₁ * d) →
      (∀ l : Fin D, (l : ℕ) ≠ 0 → cB * a ≤ ‖μ l‖) →
      ∀ (q : Fin D → Fin D → Fin D → ℂ) (q₀ : ℂ) (εq : ℝ), cq ≤ ‖q₀‖ → ‖q₀‖ ≤ 1 → εq ≤ ε₀ →
      (∀ a' b c, ‖q a' b c - (if a' = b ∧ b = c then q₀ else 0)‖ ≤ εq) →
      ∀ (rbar : ℝ) (x : Fin D → ℂ), 0 < rbar → rbar ≤ σ₀ ^ 2 → vnorm x ≤ 1 →
      vnorm (L *ᵥ x - quadForm q (sigTheta D θ *ᵥ x)) ≤ rbar + K₃ * vnorm x ^ 3 →
        vnorm x ≤ stabBound (ρ ^ 2) K₁ (2 * Cs) KA KB rbar d a ∨
          2 * stabBound (ρ ^ 2) K₁ (2 * Cs) KA KB rbar d a < vnorm x := by
  intro θ hθ0 hθ1 L μ hL d a hd ha hS hU hN1 hN2 q q₀ εq hcq0 hq1 hεq hq rbar x hr hr₀ hx1 hres
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hn0 : 0 ≤ vnorm x := Stability_vnorm_nonneg x
  have hs0 : 0 < Real.sqrt rbar := Real.sqrt_pos.mpr hr
  have hss : Real.sqrt rbar ^ 2 = rbar := Real.sq_sqrt hr.le
  have hsσ : Real.sqrt rbar ≤ σ₀ := by
    rw [← Real.sqrt_sq hσ₀.le]
    exact Real.sqrt_le_sqrt hr₀
  have ha0 : 0 ≤ a := by linarith
  have he : ∀ a b c, ‖q a b c - (if a = b ∧ b = c then q₀ else 0)‖ ≤ ε₀ :=
    fun a b c => (hq a b c).trans hεq
  have hε₀0 : 0 ≤ ε₀ := (norm_nonneg _).trans (he ⟨0, hD⟩ ⟨0, hD⟩ ⟨0, hD⟩)
  have hqb : ∀ a b c, ‖q a b c‖ ≤ 2 := by
    intro a b c
    have h1 : q a b c = (q a b c - (if a = b ∧ b = c then q₀ else 0)) +
        (if a = b ∧ b = c then q₀ else 0) := by ring
    have h2 : ‖(if a = b ∧ b = c then q₀ else 0)‖ ≤ 1 := by
      split_ifs
      · exact hq1
      · simp
    rw [h1]
    exact (norm_add_le _ _).trans (by linarith [he a b c])
  have hσ := Stability_sig_eigvec D θ
  have hyle : vnorm (sigTheta D θ *ᵥ x) ≤ vnorm x := by
    have := Stability_vnorm_mulVec_le (sigTheta D θ) _ hσ 1 zero_le_one (fun l => by
      split_ifs
      · simp
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ0]
        exact hθ1) x
    linarith
  have hyge : θ * vnorm x ≤ vnorm (sigTheta D θ *ᵥ x) :=
    Stability_vnorm_mulVec_ge (sigTheta D θ) _ hσ θ hθ0 (fun l => by
      split_ifs
      · simpa using hθ1
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ0]) x
  have hy0 : 0 ≤ vnorm (sigTheta D θ *ᵥ x) := Stability_vnorm_nonneg _
  have hf : vnorm (L *ᵥ x - quadForm q (sigTheta D θ *ᵥ x)) ≤
      Real.sqrt rbar ^ 2 + K₃ * vnorm x ^ 3 := by rw [hss]; exact hres
  have hQ : vnorm (quadForm q (sigTheta D θ *ᵥ x)) ≤ 2 * (D : ℝ) ^ 3 * vnorm x ^ 2 := by
    have h1 := Stability_quad_le q 2 zero_le_two hqb (sigTheta D θ *ᵥ x)
    have h2 : vnorm (sigTheta D θ *ᵥ x) ^ 2 ≤ vnorm x ^ 2 := pow_le_pow_left₀ hy0 hyle 2
    have h3 : (D : ℝ) ^ 3 * 2 * vnorm (sigTheta D θ *ᵥ x) ^ 2 ≤ (D : ℝ) ^ 3 * 2 * vnorm x ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hLx : vnorm (L *ᵥ x) ≤ vnorm (L *ᵥ x - quadForm q (sigTheta D θ *ᵥ x)) +
      vnorm (quadForm q (sigTheta D θ *ᵥ x)) := by
    have : L *ᵥ x = (L *ᵥ x - quadForm q (sigTheta D θ *ᵥ x)) +
        quadForm q (sigTheta D θ *ᵥ x) := by abel
    conv_lhs => rw [this]
    exact Stability_vnorm_add _ _
  have hn3 : vnorm x ^ 3 ≤ vnorm x ^ 2 := by
    have : vnorm x ^ 3 = vnorm x * vnorm x ^ 2 := by ring
    rw [this]
    exact mul_le_of_le_one_left (sq_nonneg _) hx1
  unfold stabBound
  split_ifs with hLr hA
  · -- the linear regime
    rcases le_or_gt (vnorm x) (2 * (2 * Cs * rbar / d)) with h2 | h2
    · left
      have hlow : (d / Cs) * vnorm x ≤ vnorm (L *ᵥ x) :=
        Stability_vnorm_mulVec_ge L μ hL (d / Cs) (by positivity) hS x
      have hS' : d * vnorm x ≤ Cs * (rbar + (2 * (D : ℝ) ^ 3 + K₃) * vnorm x ^ 2) := by
        have e1 : d * vnorm x = Cs * ((d / Cs) * vnorm x) := by field_simp
        rw [e1]
        refine mul_le_mul_of_nonneg_left ?_ hCs.le
        have : K₃ * vnorm x ^ 3 ≤ K₃ * vnorm x ^ 2 := mul_le_mul_of_nonneg_left hn3 hK₃
        rw [hss] at hf
        linarith
      exact Stability_regL Cs (2 * (D : ℝ) ^ 3 + K₃) ρ d rbar (vnorm x) hCs (by positivity) hd
        hn0 h8 hLr hS' h2
    · exact Or.inr h2
  · -- the quadratic regime A
    have hρd : ρ * d < Real.sqrt rbar := by
      refine lt_of_pow_lt_pow_left₀ 2 hs0.le ?_
      rw [hss, mul_pow]
      exact not_le.mp hLr
    rcases le_or_gt (vnorm x) (2 * (KA * Real.sqrt rbar)) with h2 | h2
    · left
      have hθ2 : 1 / 2 ≤ θ := by
        have : K₁ * Real.sqrt rbar ≤ K₁ * σ₀ := mul_le_mul_of_nonneg_left hsσ hK₁.le
        linarith
      have hny : vnorm x ≤ 2 * vnorm (sigTheta D θ *ᵥ x) := by
        have := mul_le_mul_of_nonneg_right hθ2 hn0
        linarith
      have hlowQ := Stability_quad_ge q q₀ cq ε₀ hε₀0 hcq0 hε₀c he (sigTheta D θ *ᵥ x)
      have hQx : vnorm (quadForm q (sigTheta D θ *ᵥ x)) ≤
          vnorm (L *ᵥ x) + vnorm (L *ᵥ x - quadForm q (sigTheta D θ *ᵥ x)) := by
        have : quadForm q (sigTheta D θ *ᵥ x) =
            L *ᵥ x - (L *ᵥ x - quadForm q (sigTheta D θ *ᵥ x)) := by abel
        conv_lhs => rw [this]
        exact Stability_vnorm_sub _ _
      have hLu : vnorm (L *ᵥ x) ≤ Cu * (d + a) * vnorm x :=
        Stability_vnorm_mulVec_le L μ hL (Cu * (d + a)) (by positivity) hU x
      have hmain : cq * vnorm x ^ 2 ≤
          8 * D * (Cu * (d + a) * vnorm x + Real.sqrt rbar ^ 2 + K₃ * vnorm x ^ 3) := by
        have h1 : vnorm x ^ 2 ≤ (2 * vnorm (sigTheta D θ *ᵥ x)) ^ 2 :=
          pow_le_pow_left₀ hn0 hny 2
        have h2 : cq * vnorm x ^ 2 ≤ 4 * (cq * vnorm (sigTheta D θ *ᵥ x) ^ 2) := by
          have := mul_le_mul_of_nonneg_left h1 hcq.le
          linarith
        have h3 : vnorm (quadForm q (sigTheta D θ *ᵥ x)) ≤
            Cu * (d + a) * vnorm x + Real.sqrt rbar ^ 2 + K₃ * vnorm x ^ 3 := by linarith
        have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 8 * D)
        linarith
      exact Stability_regA D Cu K₁ K₃ cq ρ KA σ₀ (Real.sqrt rbar) d a (vnorm x) hDpos hCu hK₃
        hcq hρ hs0 hn0 hsσ hρd hA hKA1 hKA2 hK hKA hmain h2
    · exact Or.inr h2
  · -- the quadratic regime B
    have hρd : ρ * d < Real.sqrt rbar := by
      refine lt_of_pow_lt_pow_left₀ 2 hs0.le ?_
      rw [hss, mul_pow]
      exact not_le.mp hLr
    have ha' : K₁ * Real.sqrt rbar < a := not_le.mp hA
    rcases le_or_gt (vnorm x) (2 * (KB * Real.sqrt rbar)) with h2 | h2
    · left
      by_contra hlow
      replace hlow := not_le.mp hlow
      have htv := Stability_trans hD L μ hL (cB * a) (by positivity) hN2 x
      have hnf : vnorm (L *ᵥ x - quadForm q (sigTheta D θ *ᵥ x)) ≤ 2 * Real.sqrt rbar ^ 2 := by
        have h1 : vnorm x ^ 3 ≤ (2 * (KB * Real.sqrt rbar)) ^ 3 := pow_le_pow_left₀ hn0 h2 3
        have h2' : K₃ * vnorm x ^ 3 ≤ (8 * K₃ * KB ^ 3 * Real.sqrt rbar) * Real.sqrt rbar ^ 2 := by
          have h := mul_le_mul_of_nonneg_left h1 hK₃
          have e : K₃ * (2 * (KB * Real.sqrt rbar)) ^ 3 =
              (8 * K₃ * KB ^ 3 * Real.sqrt rbar) * Real.sqrt rbar ^ 2 := by ring
          linarith
        have h3 : (8 * K₃ * KB ^ 3 * Real.sqrt rbar) * Real.sqrt rbar ^ 2 ≤
            1 * Real.sqrt rbar ^ 2 := by
          have : 8 * K₃ * KB ^ 3 * Real.sqrt rbar ≤ 8 * K₃ * KB ^ 3 * σ₀ :=
            mul_le_mul_of_nonneg_left hsσ (by positivity)
          exact mul_le_mul_of_nonneg_right (this.trans h8K) (sq_nonneg _)
        linarith
      have hR : vnorm (L *ᵥ x) ≤ (2 + 4 * (2 * (D : ℝ) ^ 3) * KB ^ 2) * Real.sqrt rbar ^ 2 := by
        have h1 : vnorm x ^ 2 ≤ (2 * (KB * Real.sqrt rbar)) ^ 2 := pow_le_pow_left₀ hn0 h2 2
        have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (D : ℝ) ^ 3)
        have e : 2 * (D : ℝ) ^ 3 * (2 * (KB * Real.sqrt rbar)) ^ 2 =
            4 * (2 * (D : ℝ) ^ 3) * KB ^ 2 * Real.sqrt rbar ^ 2 := by ring
        linarith
      have hnwb := Stability_regB_trans cB ε' KB K₁ (2 * (D : ℝ) ^ 3) (Real.sqrt rbar) a
        (vnorm (Stability_perp x)) _ hcB hε' hKB (by positivity) hs0 ha' hK1 htv hR
      have hmean := Stability_mean_le hD θ hθ0 hθ1 L μ hL C₁ d cq ε₀ hε₀0 (hN1 ⟨0, hD⟩ rfl) q q₀
        hcq0 hq1 he x
      have hε₀c' : 32 * (D : ℝ) ^ 3 * ε₀ ≤ cq := by
        have h1 : (D : ℝ) ^ 3 ≤ (D : ℝ) ^ 4 := by
          have : (1 : ℝ) ≤ D := by exact_mod_cast hD
          exact pow_le_pow_right₀ this (by norm_num)
        have := mul_le_mul_of_nonneg_right h1 hε₀0
        linarith
      exact Stability_regB_mean D C₁ cq ρ KB ε' ε₀ (Real.sqrt rbar) d (vnorm x)
        (vnorm (Stability_perp x)) _ hDpos hC₁ hcq hρ hKB hs0 hn0 hρd hlow h2 hnwb
        (Stability_vnorm_nonneg _) hnf hKB1 hKB2 hε'c hε₀c' hmean
    · exact Or.inr h2

/-- `8 C_s² ρ² C' ≤ 1` for `ρ = 1 / (4 C_s (C' + 1))`. -/
private lemma Stability_h8 (Cs C' : ℝ) (hCs : 0 < Cs) (hC' : 0 ≤ C') :
    8 * Cs ^ 2 * (1 / (4 * Cs * (C' + 1))) ^ 2 * C' ≤ 1 := by
  have e : 8 * Cs ^ 2 * (1 / (4 * Cs * (C' + 1))) ^ 2 * C' = C' / (2 * (C' + 1) ^ 2) := by
    field_simp
    ring
  rw [e, div_le_one (by positivity)]
  nlinarith

/-- `K ≥ T / c` and `K ≥ 1` give `T ≤ c K²`. -/
private lemma Stability_sq_bound (T c K : ℝ) (hc : 0 < c) (h : T / c ≤ K) (h1 : 1 ≤ K) :
    T ≤ c * K ^ 2 := by
  rw [div_le_iff₀ hc] at h
  have h2 : K ≤ K ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 hc.le
  linarith

/-- `8 (1 + c) ε'² ≤ c` for `ε' = c / (8 (c + 1))`. -/
private lemma Stability_eps_bound (c : ℝ) (hc : 0 < c) :
    8 * (1 + c) * (c / (8 * (c + 1))) ^ 2 ≤ c := by
  have e : 8 * (1 + c) * (c / (8 * (c + 1))) ^ 2 = c * (c / (8 * (c + 1))) := by
    field_simp
    ring
  rw [e]
  have : c / (8 * (c + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  nlinarith


/-- The linear part `1 - M̂ σ_θ` of the vector equation is diagonal in the Fourier basis of
(A.25) [eq_lambdak]: `(1 - M̂ σ_θ) u_l = (1 - θ_l λ̂_l) u_l` with `θ_0 = 1` and `θ_l = θ` for
`l ≠ 0`, where `M̂ = M̂(z₁, z₂)` of (3.1) [def_ML], `z₁, z₂ ∉ ℝ` and `D ≥ 2`. -/
theorem stabOp_eigvec (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (z₁ z₂ : ℂ) (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0) (l : Fin D) :
    (1 - Mhat (lam D N A) z₁ z₂ * sigTheta D θ) *ᵥ fourierVec D l =
      (1 - (if (l : ℕ) = 0 then 1 else (θ : ℂ)) * circEig (Mhat (lam D N A) z₁ z₂) l) •
        fourierVec D l := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Stability_sig_eigvec,
    Matrix.mulVec_smul, Mhat_eigvec D hD N A z₁ z₂ h₁ h₂ l, smul_smul, sub_smul, one_smul]

/-- The deterministic stability of the vector equation, with the spectral facts as hypotheses:
for `L` with Fourier eigenvalues `μ_l` (`L u_l = μ_l u_l`) such that `|μ_l| ≥ d / C_s`,
`|μ_l| ≤ C_u (d + a)`, `|μ_0| ≤ C₁ d` and `|μ_l| ≥ c_B a` for `l ≠ 0`, with `a ≥ 1 - θ`, and for
`q` with `|q_{abc} - q₀ δ_{abc}| ≤ ε_q ≤ ε₀` and `c_q ≤ |q₀| ≤ 1`: every `x` with `|x| ≤ 1` and
`|L x - Q(σ_θ x)| ≤ r̄ + K₃ |x|³`, `0 < r̄ ≤ r̄₀`, satisfies `|x| ≤ β` or `|x| > 2β`, where
`β = stabBound c_L K₁ K_L K_A K_B r̄ d a`. The constants depend on `D, C_s, C_u, C₁, c_B, c_q, K₃`
only, and satisfy `K_L √c_L ≤ K_B ≤ K_A` and `K_A √r̄₀ ≤ 1/2`. -/
theorem stab_dichotomy (D : ℕ) (hD : 1 ≤ D) (Cs Cu C₁ cB cq K₃ : ℝ) (hCs : 0 < Cs)
    (hCu : 0 < Cu) (hC₁ : 0 < C₁) (hcB : 0 < cB) (hcq : 0 < cq) (hK₃ : 0 ≤ K₃) :
    ∃ cL K₁ KL KA KB r₀ ε₀ : ℝ, 0 < cL ∧ 0 < K₁ ∧ 0 < KL ∧ 0 < KA ∧ 0 < KB ∧ 0 < r₀ ∧
      0 < ε₀ ∧ KL * Real.sqrt cL ≤ KB ∧ KB ≤ KA ∧ KA * Real.sqrt r₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ (L : Matrix (Fin D) (Fin D) ℂ) (μ : Fin D → ℂ),
      (∀ l, L *ᵥ fourierVec D l = μ l • fourierVec D l) →
      ∀ d a : ℝ, 0 < d → 1 - θ ≤ a →
      (∀ l, d / Cs ≤ ‖μ l‖) → (∀ l, ‖μ l‖ ≤ Cu * (d + a)) →
      (∀ l : Fin D, (l : ℕ) = 0 → ‖μ l‖ ≤ C₁ * d) →
      (∀ l : Fin D, (l : ℕ) ≠ 0 → cB * a ≤ ‖μ l‖) →
      ∀ (q : Fin D → Fin D → Fin D → ℂ) (q₀ : ℂ) (εq : ℝ), cq ≤ ‖q₀‖ → ‖q₀‖ ≤ 1 → εq ≤ ε₀ →
      (∀ a' b c, ‖q a' b c - (if a' = b ∧ b = c then q₀ else 0)‖ ≤ εq) →
      ∀ (rbar : ℝ) (x : Fin D → ℂ), 0 < rbar → rbar ≤ r₀ → vnorm x ≤ 1 →
      vnorm (L *ᵥ x - quadForm q (sigTheta D θ *ᵥ x)) ≤ rbar + K₃ * vnorm x ^ 3 →
        vnorm x ≤ stabBound cL K₁ KL KA KB rbar d a ∨
          2 * stabBound cL K₁ KL KA KB rbar d a < vnorm x := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = 2 * (D : ℝ) ^ 3 + K₃ := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 1 / (4 * Cs * (C' + 1)) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨KB, hKB⟩ : ∃ KB : ℝ, KB = 2 * Cs * ρ + 16 * C₁ * D / (cq * ρ) + 16 * D / cq + 1 :=
    ⟨_, rfl⟩
  have hKB0 : 0 < KB := by rw [hKB]; positivity
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = cq / (8 * (cq + 1)) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = (2 + 4 * (2 * (D : ℝ) ^ 3) * KB ^ 2) / (cB * ε' * KB) :=
    ⟨_, rfl⟩
  have hK₁0 : 0 < K₁ := by rw [hK₁]; positivity
  obtain ⟨KA, hKA⟩ : ∃ KA : ℝ,
      KA = 32 * D * Cu * (1 + ρ * K₁) / (cq * ρ) + 32 * D / cq + KB + 1 := ⟨_, rfl⟩
  have hKA0 : 0 < KA := by rw [hKA]; positivity
  obtain ⟨Sg, hSg⟩ : ∃ Sg : ℝ,
      Sg = 2 * KA + 2 * K₁ + 8 * K₃ * KB ^ 3 + 32 * D * KA * K₃ / cq + 1 := ⟨_, rfl⟩
  have hSg0 : 0 < Sg := by rw [hSg]; positivity
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = 1 / Sg := ⟨_, rfl⟩
  have hσ₀0 : 0 < σ₀ := by rw [hσ₀]; positivity
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = min 1 (cq / (32 * (D : ℝ) ^ 4)) := ⟨_, rfl⟩
  have hε₀0 : 0 < ε₀ := by rw [hε₀]; exact lt_min one_pos (by positivity)
  -- each term `T` of `Sg` satisfies `T σ₀ ≤ 1`
  have hterm : ∀ T : ℝ, T ≤ Sg → T * σ₀ ≤ 1 := by
    intro T hT
    rw [hσ₀, mul_one_div, div_le_one hSg0]
    exact hT
  have p1 : 0 ≤ 8 * K₃ * KB ^ 3 := by positivity
  have p2 : 0 ≤ 32 * D * KA * K₃ / cq := by positivity
  have h2KA : 2 * KA * σ₀ ≤ 1 := hterm _ (by rw [hSg]; linarith)
  have h2K₁ : 2 * K₁ * σ₀ ≤ 1 := hterm _ (by rw [hSg]; linarith)
  have h8K : 8 * K₃ * KB ^ 3 * σ₀ ≤ 1 := hterm _ (by rw [hSg]; linarith)
  have hK : 32 * D * KA * K₃ * σ₀ ≤ cq := by
    have h := hterm (32 * D * KA * K₃ / cq) (by rw [hSg]; linarith)
    have e : 32 * D * KA * K₃ * σ₀ = cq * (32 * D * KA * K₃ / cq * σ₀) := by
      field_simp
    rw [e]
    calc cq * (32 * D * KA * K₃ / cq * σ₀) ≤ cq * 1 := mul_le_mul_of_nonneg_left h hcq.le
      _ = cq := mul_one cq
  have h8 : 8 * Cs ^ 2 * ρ ^ 2 * (2 * (D : ℝ) ^ 3 + K₃) ≤ 1 := by
    rw [← hC', hρ]
    exact Stability_h8 Cs C' hCs hC'0
  have q1 : 0 ≤ 2 * Cs * ρ := by positivity
  have q2 : 0 ≤ 16 * C₁ * D / (cq * ρ) := by positivity
  have q3 : 0 ≤ 16 * (D : ℝ) / cq := by positivity
  have hKB1 : 16 * C₁ * D ≤ cq * ρ * KB := by
    have h : 16 * C₁ * D / (cq * ρ) ≤ KB := by rw [hKB]; linarith
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  have hKB2 : 16 * (D : ℝ) ≤ cq * KB ^ 2 := by
    have h : 16 * (D : ℝ) / cq ≤ KB := by rw [hKB]; linarith
    have h1 : 1 ≤ KB := by rw [hKB]; linarith
    exact Stability_sq_bound _ _ _ hcq h h1
  have hε'c : 8 * (1 + cq) * ε' ^ 2 ≤ cq := by
    rw [hε']
    exact Stability_eps_bound cq hcq
  have hε₀c : 32 * (D : ℝ) ^ 4 * ε₀ ≤ cq := by
    have h : ε₀ ≤ cq / (32 * (D : ℝ) ^ 4) := by rw [hε₀]; exact min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hK1 : 2 + 4 * (2 * (D : ℝ) ^ 3) * KB ^ 2 ≤ cB * ε' * KB * K₁ := by
    rw [hK₁]
    have : cB * ε' * KB ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ this]
  have r1 : 0 ≤ 32 * D * Cu * (1 + ρ * K₁) / (cq * ρ) := by positivity
  have r2 : 0 ≤ 32 * (D : ℝ) / cq := by positivity
  have hKA1 : 32 * D * Cu * (1 + ρ * K₁) ≤ cq * ρ * KA := by
    have h : 32 * D * Cu * (1 + ρ * K₁) / (cq * ρ) ≤ KA := by rw [hKA]; linarith
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  have hKA2 : 32 * (D : ℝ) ≤ cq * KA ^ 2 := by
    have h : 32 * (D : ℝ) / cq ≤ KA := by rw [hKA]; linarith
    have h1 : 1 ≤ KA := by rw [hKA]; linarith
    exact Stability_sq_bound _ _ _ hcq h h1
  have hBA : KB ≤ KA := by rw [hKA]; linarith
  have hLB : 2 * Cs * ρ ≤ KB := by rw [hKB]; linarith
  refine ⟨ρ ^ 2, K₁, 2 * Cs, KA, KB, σ₀ ^ 2, ε₀, by positivity, hK₁0, by positivity, hKA0, hKB0,
    by positivity, hε₀0, ?_, hBA, ?_, ?_⟩
  · rw [Real.sqrt_sq hρ0.le]
    exact hLB
  · rw [Real.sqrt_sq hσ₀0.le]
    linarith
  · have hε₀1 : ε₀ ≤ 1 := by rw [hε₀]; exact min_le_left _ _
    exact Stability_core D hD Cs Cu C₁ cB cq K₃ hCs hCu hC₁ hcB hcq hK₃ ρ K₁ KA KB σ₀ ε₀ ε' hρ0
      hK₁0 hKA0 hKB0 hσ₀0 hε'0 hε₀1 h8 hKB1 hKB2 hε'c hε₀c hK1 h8K h2K₁ hKA1 hKA2 hK

/-- The good bound does not decrease along decreasing `η`: if `K_L √c_L ≤ K_B ≤ K_A`,
`0 < r̄ ≤ r̄'` and `0 < d' ≤ d`, then `stabBound … r̄ d a ≤ stabBound … r̄' d' a`. -/
theorem stabBound_mono (cL K₁ KL KA KB : ℝ) (hcL : 0 < cL) (hK₁ : 0 < K₁) (hKL : 0 < KL)
    (hLB : KL * Real.sqrt cL ≤ KB) (hBA : KB ≤ KA) (rbar rbar' d d' a : ℝ) (hr : 0 < rbar)
    (hrr : rbar ≤ rbar') (hd : 0 < d') (hdd : d' ≤ d) :
    stabBound cL K₁ KL KA KB rbar d a ≤ stabBound cL K₁ KL KA KB rbar' d' a := by
  have hdpos : 0 < d := lt_of_lt_of_le hd hdd
  have hKB : 0 < KB := lt_of_lt_of_le (mul_pos hKL (Real.sqrt_pos.mpr hcL)) hLB
  have hKA : 0 < KA := lt_of_lt_of_le hKB hBA
  have hsq : Real.sqrt rbar ≤ Real.sqrt rbar' := Real.sqrt_le_sqrt hrr
  -- in the linear regime, `K_L r̄ / d ≤ K_L √c_L √r̄`
  have hLin : rbar ≤ cL * d ^ 2 → KL * rbar / d ≤ KB * Real.sqrt rbar := by
    intro h
    have h1 : Real.sqrt rbar ≤ Real.sqrt cL * d := by
      rw [← Real.sqrt_sq hdpos.le, ← Real.sqrt_mul hcL.le]
      exact Real.sqrt_le_sqrt h
    have h2 : rbar ≤ Real.sqrt rbar * (Real.sqrt cL * d) := by
      have := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg rbar)
      rwa [Real.mul_self_sqrt hr.le] at this
    rw [div_le_iff₀ hdpos]
    calc KL * rbar ≤ KL * (Real.sqrt rbar * (Real.sqrt cL * d)) :=
          mul_le_mul_of_nonneg_left h2 hKL.le
      _ = (KL * Real.sqrt cL) * Real.sqrt rbar * d := by ring
      _ ≤ KB * Real.sqrt rbar * d := by gcongr
  unfold stabBound
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · -- linear to linear
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div₀ (by linarith) hrr hd hdd) hKL.le
  · -- linear to quadratic A
    calc KL * rbar / d ≤ KB * Real.sqrt rbar := hLin h1
      _ ≤ KA * Real.sqrt rbar' := mul_le_mul hBA hsq (Real.sqrt_nonneg _) hKA.le
  · -- linear to quadratic B
    calc KL * rbar / d ≤ KB * Real.sqrt rbar := hLin h1
      _ ≤ KB * Real.sqrt rbar' := mul_le_mul_of_nonneg_left hsq hKB.le
  · -- quadratic to linear: impossible
    exfalso
    have : cL * d' ^ 2 ≤ cL * d ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hdd 2) hcL.le
    linarith
  · exact mul_le_mul_of_nonneg_left hsq hKA.le
  · -- quadratic A to quadratic B: impossible
    exfalso
    have : K₁ * Real.sqrt rbar ≤ K₁ * Real.sqrt rbar' := mul_le_mul_of_nonneg_left hsq hK₁.le
    linarith
  · exfalso
    have : cL * d' ^ 2 ≤ cL * d ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hdd 2) hcL.le
    linarith
  · exact mul_le_mul hBA hsq (Real.sqrt_nonneg _) hKA.le
  · exact mul_le_mul_of_nonneg_left hsq hKB.le

end RBMTransitionEdge

end
