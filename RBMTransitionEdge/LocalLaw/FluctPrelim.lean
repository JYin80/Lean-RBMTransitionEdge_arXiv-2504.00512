module

public import RBMTransitionEdge.LocalLaw.Uniform
public import RBMTransitionEdge.LocalLaw.Dyson
public import RBMTransitionEdge.LocalLaw.DysonBounds
public import RBMTransitionEdge.Tools.ResolventIdentities
public import RBMTransitionEdge.Det.Block

@[expose] public section

/-!
# Common tools of the moment inequalities

Tilted vectors of the profile `S_θ`, the good events on which resolvent forms are bounded, Ward's
identity (2.32) [eq_Ward] for a vector, the a priori good event from the bound `|(G - M)_{st}| ≺ φ`
(Definition 2.8 [stoch_domination]), Young's inequality for moments, and the conversion of the
control parameter, for the moment bounds behind Lemma 2.9 [lem_loc].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The tilted vectors `t^r(x)_k = x_k N s_{kr}` of the variance profile `S_θ`; `N s_{kr} ≤ 1`, so
`|t^r(x)| ≤ |x|`. -/
def tiltV (D N : ℕ) (θ : ℝ) (x : Idx D N → ℂ) (r : Idx D N) : Idx D N → ℂ :=
  fun k => x k * (((N : ℝ) * varProf D N θ k r : ℝ) : ℂ)

/-- The good event on a finite vector set `V`: `|x^* G y| ≤ Γ` and `Im x^* G x ≤ Υ` for all
`x, y ∈ V`, with `G = (h + Λ - z)⁻¹`. -/
def goodSet {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (V : Finset (Idx D N → ℂ))
    (Γ Υ : ℝ) : Set (Idx D N → Idx D N → ℂ) :=
  {h | ∀ x ∈ V, ∀ y ∈ V, ‖star x ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ y)‖ ≤ Γ ∧
    (star x ⬝ᵥ (res (Matrix.of h + Λ) z *ᵥ x)).im ≤ Υ}

/-- The vectors of the isotropic expansion of `(H̲G)_{uv}` of (2.30) [eq:HGline]: `u`, `v`,
`Λ^* u`, the block projections `E_a u`, the standard basis, the tilted vectors `t^r(u)` and
their conjugates. -/
def isoVecs (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (u v : Idx D N → ℂ) :
    Finset (Idx D N → ℂ) :=
  {u, v, Λᴴ *ᵥ u} ∪ Finset.univ.image (fun a => (Ea D N a)ᴴ *ᵥ u) ∪
    Finset.univ.image (fun k => Pi.single k 1) ∪ Finset.univ.image (tiltV D N θ u) ∪
      Finset.univ.image (fun r => star (tiltV D N θ u r))

/-- The good event of the isotropic moment inequality: the good event on `isoVecs`, and
`|(H̲G)_{uy}| ≤ λ` for `y = v`, the standard basis and the conjugate tilted vectors of `u`. -/
def isoGood (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (u v : Idx D N → ℂ)
    (Γ Υ lb : ℝ) : Set (Idx D N → Idx D N → ℂ) :=
  goodSet Λ z (isoVecs D N θ Λ u v) Γ Υ ∩
    {h | ∀ y ∈ insert v (Finset.univ.image (fun k => Pi.single k 1) ∪
        Finset.univ.image (fun r => star (tiltV D N θ u r))),
      ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ y)‖ ≤ lb}

/-- The Ward identity (2.32) [eq_Ward] for a vector: `Σ_k |(G y)_k|² = Im(y^* G y)/η`. -/
theorem ward_vec {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (y : ι → ℂ) :
    ∑ k, ‖(res X z *ᵥ y) k‖ ^ 2 = (star y ⬝ᵥ (res X z *ᵥ y)).im / z.im := by
  set R := res X z with hR
  have hη : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  apply Complex.ofReal_injective
  have h1 : ((∑ k, ‖(R *ᵥ y) k‖ ^ 2 : ℝ) : ℂ) =
      ∑ k, ∑ a, ∑ b, starRingEnd ℂ (y a) * y b * (starRingEnd ℂ (R k a) * R k b) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : (R *ᵥ y) k = ∑ b, R k b * y b := rfl
    rw [← Complex.conj_mul', e1, map_sum, Finset.sum_mul_sum]
    simp only [map_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have h2 : ∑ k, ∑ a, ∑ b, starRingEnd ℂ (y a) * y b * (starRingEnd ℂ (R k a) * R k b) =
      ∑ a, ∑ b, starRingEnd ℂ (y a) * y b *
        ((R a b - starRingEnd ℂ (R b a)) / (2 * Complex.I * z.im)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← (ward_sum X hX z hz b a).1, Finset.mul_sum]
  have hw : star y ⬝ᵥ (R *ᵥ y) = ∑ a, ∑ b, starRingEnd ℂ (y a) * y b * R a b := by
    simp only [Matrix.mulVec, dotProduct, Pi.star_apply, Complex.star_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hw' : starRingEnd ℂ (star y ⬝ᵥ (R *ᵥ y)) =
      ∑ a, ∑ b, starRingEnd ℂ (y a) * y b * starRingEnd ℂ (R b a) := by
    rw [hw]
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have h3 : ∑ a, ∑ b, starRingEnd ℂ (y a) * y b *
        ((R a b - starRingEnd ℂ (R b a)) / (2 * Complex.I * z.im)) =
      ((star y ⬝ᵥ (R *ᵥ y)) - starRingEnd ℂ (star y ⬝ᵥ (R *ᵥ y))) / (2 * Complex.I * z.im) := by
    rw [hw', hw, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h1, h2, h3, Complex.sub_conj]
  push_cast
  field_simp

/-- `|x^* T y| ≤ ‖T‖` for `|x|, |y| ≤ 1`. -/
private lemma FluctPrelim_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
    (x y : ι → ℂ) (hx : ∑ k, ‖x k‖ ^ 2 ≤ 1) (hy : ∑ k, ‖y k‖ ^ 2 ≤ 1) :
    ‖star x ⬝ᵥ (T *ᵥ y)‖ ≤ opNorm T := by
  have e : star x ⬝ᵥ (T *ᵥ y) =
      inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanLin T (WithLp.toLp 2 y)) := by
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
  have hx' : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_one.mpr hx
  have hy' : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_one.mpr hy
  have h1 : Matrix.toEuclideanLin T (WithLp.toLp 2 y) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y) := rfl
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y)‖ ≤ opNorm T * 1 :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by unfold opNorm; gcongr)
  rw [e, h1]
  calc ‖inner ℂ (WithLp.toLp 2 x) (Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y))‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ *
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T (WithLp.toLp 2 y)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (opNorm T * 1) := mul_le_mul hx' h2 (norm_nonneg _) zero_le_one
    _ = opNorm T := by ring


/-- `S_θ(R)` is the diagonal matrix with entries `θ D⟨R E_a⟩ + (1 - θ)⟨R⟩`, `a` the block. -/
private lemma FluctPrelim_sTheta_eq (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ) :
    sTheta D N θ R = Matrix.diagonal (fun p : Idx D N =>
      (θ : ℂ) * ((D : ℂ) * ntr (R * Ea D N p.1)) + ((1 - θ : ℝ) : ℂ) * ntr R) := by
  ext p q
  by_cases h : p = q
  · subst h
    simp [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Ea]
  · simp [sTheta, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Ea, h]

/-- The normalized trace on an empty index type vanishes. -/
private lemma FluctPrelim_ntr_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (B : Matrix ι ι ℂ) : ntr B = 0 := by
  simp [ntr, Matrix.trace]

/-- `|⟨R⟩| ≤ ‖R‖`. -/
private lemma FluctPrelim_norm_ntr_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℂ) : ‖ntr R‖ ≤ opNorm R := by
  rcases isEmpty_or_nonempty ι with h | h
  · rw [FluctPrelim_ntr_of_isEmpty, norm_zero]
    exact norm_nonneg _
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    unfold ntr Matrix.trace
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, R.diag i‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, opNorm R := by
          gcongr
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun i _ => norm_apply_le_opNorm R i i)
      _ = opNorm R := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

/-- `|D⟨R E_a⟩| ≤ ‖R‖`. -/
private lemma FluctPrelim_blk_le (D N : ℕ) (a : Fin D) (R : Matrix (Idx D N) (Idx D N) ℂ) :
    ‖(D : ℂ) * ntr (R * Ea D N a)‖ ≤ opNorm R := by
  have hB : 0 ≤ opNorm R := norm_nonneg _
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : IsEmpty (Idx D 0) := ⟨fun p => p.2.elim0⟩
    simp [FluctPrelim_ntr_of_isEmpty, hB]
  · have hD : 0 < D := a.pos
    have htr : (R * Ea D N a).trace = ∑ p : Idx D N, if p.1 = a then R p p else 0 := by
      simp [Matrix.trace, Ea, Matrix.mul_diagonal]
    have hsum : ‖∑ p : Idx D N, if p.1 = a then R p p else 0‖ ≤ N * opNorm R := by
      calc ‖∑ p : Idx D N, if p.1 = a then R p p else 0‖
          ≤ ∑ p : Idx D N, ‖if p.1 = a then R p p else 0‖ := norm_sum_le _ _
        _ ≤ ∑ p : Idx D N, if p.1 = a then opNorm R else 0 :=
          Finset.sum_le_sum fun p _ => by
            split_ifs
            · exact norm_apply_le_opNorm R p p
            · simp
        _ = N * opNorm R := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          simp
    unfold ntr
    rw [htr]
    have hDN : (0 : ℝ) < D * N := by positivity
    calc ‖(D : ℂ) * (((Fintype.card (Idx D N) : ℕ) : ℂ)⁻¹ *
          ∑ p : Idx D N, if p.1 = a then R p p else 0)‖
        = D * (D * N : ℝ)⁻¹ * ‖∑ p : Idx D N, if p.1 = a then R p p else 0‖ := by
          rw [norm_mul, norm_mul, norm_inv]
          simp [Fintype.card_prod]
          ring
      _ ≤ D * (D * N : ℝ)⁻¹ * (N * opNorm R) := by gcongr
      _ = opNorm R := by field_simp

open scoped Matrix.Norms.L2Operator in
/-- The operator norm of a diagonal matrix is the sup norm of its entries. -/
private lemma FluctPrelim_opNorm_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    opNorm (Matrix.diagonal v) = ‖v‖ := by
  unfold opNorm
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]

/-- `‖S_θ(R)‖ ≤ ‖R‖` for `θ ∈ [0, 1]`. -/
private lemma FluctPrelim_opNorm_sTheta (D N : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (R : Matrix (Idx D N) (Idx D N) ℂ) : opNorm (sTheta D N θ R) ≤ opNorm R := by
  rw [FluctPrelim_sTheta_eq, FluctPrelim_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun p => ?_
  calc ‖(θ : ℂ) * ((D : ℂ) * ntr (R * Ea D N p.1)) + ((1 - θ : ℝ) : ℂ) * ntr R‖
      ≤ ‖(θ : ℂ) * ((D : ℂ) * ntr (R * Ea D N p.1))‖ + ‖((1 - θ : ℝ) : ℂ) * ntr R‖ :=
        norm_add_le _ _
    _ = θ * ‖(D : ℂ) * ntr (R * Ea D N p.1)‖ + (1 - θ) * ‖ntr R‖ := by
        rw [norm_mul (θ : ℂ), norm_mul ((1 - θ : ℝ) : ℂ), Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    _ ≤ θ * opNorm R + (1 - θ) * opNorm R := by
        have := h0
        have : 0 ≤ 1 - θ := by linarith
        gcongr
        · exact FluctPrelim_blk_le D N p.1 R
        · exact FluctPrelim_norm_ntr_le R
    _ = opNorm R := by ring

/-- The operator norm of a difference. -/
private lemma FluctPrelim_opNorm_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) : opNorm (X - Y) ≤ opNorm X + opNorm Y := by
  unfold opNorm
  rw [map_sub]
  exact norm_sub_le _ _

/-- `‖I‖ ≤ 1`. -/
private lemma FluctPrelim_opNorm_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] :
    opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-- The deterministic bound `|x^* H̲G y| ≤ 1 + (‖Λ‖ + |z|)/η + 1/η²` for `|x|, |y| ≤ 1`,
Hermitian `H` and `Λ`, `θ ∈ [0, 1]`, from `HG = I - (Λ - z) G` and `‖S_θ(G)‖ ≤ ‖G‖`
((2.30) [eq:HGline]). -/
theorem hgUnder_form_le (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (H Λ : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (x y : Idx D N → ℂ) (hx : ∑ k, ‖x k‖ ^ 2 ≤ 1) (hy : ∑ k, ‖y k‖ ^ 2 ≤ 1) :
    ‖star x ⬝ᵥ (hgUnder D N θ H Λ z *ᵥ y)‖ ≤ 1 + (opNorm Λ + ‖z‖) / z.im + 1 / z.im ^ 2 := by
  refine (FluctPrelim_form_le _ x y hx hy).trans ?_
  set G := res (H + Λ) z with hG
  have hHΛ : (H + Λ).IsHermitian := hH.add hΛ
  have hGn : opNorm G ≤ z.im⁻¹ := opNorm_res_le _ hHΛ z hz
  have hres := (res_mul_sub (H + Λ) hHΛ z hz).1
  have hHG : H * G = 1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G := by
    have : H * G = (H + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G -
        (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G := by
      rw [← Matrix.sub_mul]
      congr 1
      abel
    rw [this, hres]
  have hform : hgUnder D N θ H Λ z =
      1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G + sTheta D N θ G * G := by
    unfold hgUnder
    rw [← hG, hHG]
  have hη : 0 < z.im⁻¹ := inv_pos.mpr hz
  have hG0 : 0 ≤ opNorm G := norm_nonneg _
  have hΛz : opNorm (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ opNorm Λ + ‖z‖ := by
    refine (FluctPrelim_opNorm_sub_le _ _).trans ?_
    rw [opNorm_smul]
    have := FluctPrelim_opNorm_one_le (ι := Idx D N)
    nlinarith [norm_nonneg z]
  have hS : opNorm (sTheta D N θ G * G) ≤ z.im⁻¹ * z.im⁻¹ :=
    (opNorm_mul_le _ _).trans (mul_le_mul
      ((FluctPrelim_opNorm_sTheta D N θ hθ0 hθ1 G).trans hGn) hGn hG0 hη.le)
  have hT : opNorm ((Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G) ≤
      (opNorm Λ + ‖z‖) * z.im⁻¹ :=
    (opNorm_mul_le _ _).trans (mul_le_mul hΛz hGn hG0 ((norm_nonneg _).trans hΛz))
  rw [hform]
  calc opNorm (1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G + sTheta D N θ G * G)
      ≤ opNorm (1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G) +
          opNorm (sTheta D N θ G * G) := opNorm_add_le _ _
    _ ≤ (opNorm (1 : Matrix (Idx D N) (Idx D N) ℂ) +
          opNorm ((Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G)) +
          opNorm (sTheta D N θ G * G) := by
        gcongr
        exact FluctPrelim_opNorm_sub_le _ _
    _ ≤ (1 + (opNorm Λ + ‖z‖) * z.im⁻¹) + z.im⁻¹ * z.im⁻¹ := by
        gcongr
        exact FluctPrelim_opNorm_one_le
    _ = 1 + (opNorm Λ + ‖z‖) / z.im + 1 / z.im ^ 2 := by
        have : (z.im ^ 2)⁻¹ = z.im⁻¹ * z.im⁻¹ := by rw [sq, mul_inv]
        rw [div_eq_mul_inv, one_div, this]

/-! ### Helpers for `apriori_good` -/

section FluctPrelim_Lam

open scoped Matrix.Norms.L2Operator

/-- The embedding of `ℂ^N` as the block `a` of `Idx D N`. -/
private def FluctPrelim_J (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Fin N) ℂ :=
  Matrix.of fun p i => if p = (a, i) then 1 else 0

private lemma FluctPrelim_J_conj_mul (D N : ℕ) (a : Fin D) :
    (FluctPrelim_J D N a)ᴴ * FluctPrelim_J D N a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, FluctPrelim_J, Matrix.of_apply,
    Matrix.one_apply]
  have : ∀ p : Idx D N, star (if p = (a, i) then (1 : ℂ) else 0) * (if p = (a, j) then 1 else 0) =
      if p = (a, i) then (if i = j then 1 else 0) else 0 := by
    intro p
    by_cases h : p = (a, i)
    · subst h
      by_cases hij : i = j <;> simp [hij]
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma FluctPrelim_J_norm (D N : ℕ) (hN : 1 ≤ N) (a : Fin D) :
    ‖FluctPrelim_J D N a‖ ≤ 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (FluctPrelim_J D N a)
  rw [FluctPrelim_J_conj_mul, norm_one] at h1
  have h0 : 0 ≤ ‖FluctPrelim_J D N a‖ := norm_nonneg _
  nlinarith

private lemma FluctPrelim_block_norm (D N : ℕ) (hN : 1 ≤ N) (a b : Fin D)
    (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖FluctPrelim_J D N a * M * (FluctPrelim_J D N b)ᴴ‖ ≤ ‖M‖ := by
  have ha := FluctPrelim_J_norm D N hN a
  have hb := FluctPrelim_J_norm D N hN b
  calc ‖FluctPrelim_J D N a * M * (FluctPrelim_J D N b)ᴴ‖
      ≤ ‖FluctPrelim_J D N a * M‖ * ‖(FluctPrelim_J D N b)ᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖FluctPrelim_J D N a‖ * ‖M‖) * ‖(FluctPrelim_J D N b)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
    _ = ‖M‖ := by ring

private lemma FluctPrelim_block_apply (D N : ℕ) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ)
    (p q : Idx D N) :
    (FluctPrelim_J D N a * M * (FluctPrelim_J D N b)ᴴ) p q =
      if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = a <;> by_cases h2 : q1 = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, FluctPrelim_J, Prod.ext_iff, h1, h2]

private lemma FluctPrelim_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = ∑ a : Fin D, ∑ b : Fin D,
      ((if fwd D a b then FluctPrelim_J D N a * A * (FluctPrelim_J D N b)ᴴ else 0) +
        (if fwd D b a then FluctPrelim_J D N a * Aᴴ * (FluctPrelim_J D N b)ᴴ else 0)) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.add_apply]
  have e1 : ∀ a b : Fin D,
      (if fwd D a b then FluctPrelim_J D N a * A * (FluctPrelim_J D N b)ᴴ else 0) p q =
      if fwd D a b ∧ p.1 = a ∧ q.1 = b then A p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D a b <;> simp [h, FluctPrelim_block_apply]
  have e2 : ∀ a b : Fin D,
      (if fwd D b a then FluctPrelim_J D N a * Aᴴ * (FluctPrelim_J D N b)ᴴ else 0) p q =
      if fwd D b a ∧ p.1 = a ∧ q.1 = b then Aᴴ p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D b a <;> simp [h, FluctPrelim_block_apply]
  simp only [e1, e2, Finset.sum_add_distrib]
  unfold lam
  congr 1
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D p.1 q.1 <;> simp [h]
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D q.1 p.1 <;> simp [h, Matrix.conjTranspose_apply]

/-- `‖Λ‖ ≤ 2 D² ‖A‖` for the interaction `Λ = lam D N A` of (1.3) [matrix_H]. -/
private lemma FluctPrelim_opNorm_lam (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := by
  change ‖lam D N A‖ ≤ 2 * (D : ℝ) ^ 2 * ‖A‖
  rw [FluctPrelim_lam_eq]
  have hb : ∀ a b : Fin D,
      ‖(if fwd D a b then FluctPrelim_J D N a * A * (FluctPrelim_J D N b)ᴴ else 0) +
      (if fwd D b a then FluctPrelim_J D N a * Aᴴ * (FluctPrelim_J D N b)ᴴ else 0)‖ ≤
        2 * ‖A‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D a b then FluctPrelim_J D N a * A * (FluctPrelim_J D N b)ᴴ else 0)‖ ≤
        ‖A‖ := by
      split_ifs
      · exact FluctPrelim_block_norm D N hN a b A
      · simp
    have h2 : ‖(if fwd D b a then FluctPrelim_J D N a * Aᴴ * (FluctPrelim_J D N b)ᴴ else 0)‖ ≤
        ‖A‖ := by
      split_ifs
      · exact (FluctPrelim_block_norm D N hN a b Aᴴ).trans (by rw [Matrix.l2_opNorm_conjTranspose])
      · simp
    linarith
  calc ‖∑ a : Fin D, ∑ b : Fin D, _‖ ≤ ∑ a : Fin D, ‖∑ b : Fin D, _‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin D, ∑ b : Fin D, 2 * ‖A‖ := by
        refine Finset.sum_le_sum fun a _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb a b)
    _ = 2 * (D : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end FluctPrelim_Lam

/-- A form in vectors of norm `≤ 1` is bounded by the same form in unit vectors, for every
matrix `T` simultaneously: either it vanishes identically, or there are unit vectors `s, t` with
`|x^* T y| ≤ |s^* T t|` for all `T`. -/
private lemma FluctPrelim_ball_unit {ι : Type*} [Fintype ι] (x y : ι → ℂ)
    (hx : ∑ k, ‖x k‖ ^ 2 ≤ 1) (hy : ∑ k, ‖y k‖ ^ 2 ≤ 1) :
    (∀ T : Matrix ι ι ℂ, ‖star x ⬝ᵥ (T *ᵥ y)‖ = 0) ∨
      ∃ s t : ι → ℂ, ∑ k, ‖s k‖ ^ 2 = 1 ∧ ∑ k, ‖t k‖ ^ 2 = 1 ∧
        ∀ T : Matrix ι ι ℂ, ‖star x ⬝ᵥ (T *ᵥ y)‖ ≤ ‖star s ⬝ᵥ (T *ᵥ t)‖ := by
  by_cases hx0 : x = 0
  · left
    intro T
    simp [hx0]
  by_cases hy0 : y = 0
  · left
    intro T
    simp [hy0]
  right
  have hpos : ∀ w : ι → ℂ, w ≠ 0 → 0 < ∑ k, ‖w k‖ ^ 2 := by
    intro w hw
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hk) 2)
      (Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ k))
  set rx := Real.sqrt (∑ k, ‖x k‖ ^ 2) with hrx
  set ry := Real.sqrt (∑ k, ‖y k‖ ^ 2) with hry
  have hrx0 : 0 < rx := Real.sqrt_pos.mpr (hpos x hx0)
  have hry0 : 0 < ry := Real.sqrt_pos.mpr (hpos y hy0)
  have hrx1 : rx ≤ 1 := Real.sqrt_le_one.mpr hx
  have hry1 : ry ≤ 1 := Real.sqrt_le_one.mpr hy
  have hrxsq : rx ^ 2 = ∑ k, ‖x k‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
  have hrysq : ry ^ 2 = ∑ k, ‖y k‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
  refine ⟨(((rx⁻¹ : ℝ)) : ℂ) • x, (((ry⁻¹ : ℝ)) : ℂ) • y, ?_, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hrx0), mul_pow, ← Finset.mul_sum, ← hrxsq]
    field_simp
  · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hry0), mul_pow, ← Finset.mul_sum, ← hrysq]
    field_simp
  · intro T
    set s := (((rx⁻¹ : ℝ)) : ℂ) • x with hs
    set t := (((ry⁻¹ : ℝ)) : ℂ) • y with ht
    have hst : star s ⬝ᵥ (T *ᵥ t) = (((rx⁻¹ * ry⁻¹ : ℝ)) : ℂ) * (star x ⬝ᵥ (T *ᵥ y)) := by
      rw [hs, ht]
      simp only [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    rw [hst, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : 1 ≤ rx⁻¹ * ry⁻¹ := by
      have a1 : 1 ≤ rx⁻¹ := one_le_inv₀ hrx0 |>.mpr hrx1
      have a2 : 1 ≤ ry⁻¹ := one_le_inv₀ hry0 |>.mpr hry1
      nlinarith
    exact le_mul_of_one_le_left (norm_nonneg _) h1

/-- The a priori bounds on `M` behind the good event, for `‖Λ‖ ≤ 1/10`, `Im z > 0`:
`‖M‖ ≤ 5/4` and `Im(s^* M s) ≤ (25/16)(η + Im m)|s|²`. -/
private lemma FluctPrelim_det {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) :
    opNorm (MExt Λ z) ≤ 5 / 4 ∧ ∀ s : ι → ℂ, (star s ⬝ᵥ (MExt Λ z *ᵥ s)).im ≤
      25 / 16 * (z.im + (mExt Λ z).im) * ∑ i, ‖s i‖ ^ 2 := by
  have he1 : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  have he2 : MExt Λ z = MSol Λ z := by simp [MExt, MSol, he1]
  rw [he1, he2]
  obtain ⟨-, -, hMn⟩ := mSol_apriori Λ hΛ hℓ z hz
  have hz0 : 0 < ‖z‖ := by
    rw [norm_pos_iff]
    rintro rfl
    simp at hz
  refine ⟨?_, ?_⟩
  · have h1 : (1 - 2 * opNorm Λ)⁻¹ ≤ (4 / 5 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) (by linarith)
    norm_num at h1
    linarith
  · exact (im_mSol_lower Λ hΛ hℓ (1 + ‖z‖)⁻¹ (by positivity) z hz
      (by rw [inv_inv]; linarith)).2

/-- The a priori bound on a finite vector set: under `|(G - M)_{st}| ≺ φ` (Definition 2.8
[stoch_domination]) along a sequence of members, for all `ε₁, D' > 0` and large `N`, uniformly in
`z ∈ Z_N` and in finite sets `V` of vectors of norm `≤ 1`, the good event with
`Γ = 5/4 + N^{ε₁} φ` and `Υ = (41/16) η + (25/16) Im m + N^{ε₁} φ` fails with probability
`≤ |V|² N^{-D'}`. -/
theorem apriori_good (D : ℕ) (δA : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hseq : LLSeq D δA C θ μ A) (Z : ℕ → Set ℂ) (hZ : ∀ N, ∀ z ∈ Z N, 0 < z.im)
    (φ : ℕ → ℂ → ℝ) (hLL : aprioriLL D μ A Z φ) (ε₁ D' : ℝ) (hε₁ : 0 < ε₁) (hD' : 0 < D') :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z ∈ Z N, ∀ V : Finset (Idx D N → ℂ),
      (∀ x ∈ V, ∑ k, ‖x k‖ ^ 2 ≤ 1) →
      μ N (goodSet (lam D N (A N)) z V (5 / 4 + (N : ℝ) ^ ε₁ * φ N z)
          (41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im + (N : ℝ) ^ ε₁ * φ N z))ᶜ ≤
        ENNReal.ofReal ((V.card : ℝ) ^ 2 * (N : ℝ) ^ (-D')) := by
  obtain ⟨N₁, hN₁⟩ := hLL ε₁ hε₁ D' hD'
  have hD1 := hseq.one_le_D
  have hδ := hseq.pos
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 := by
    have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
    have h2 := ht.const_mul (2 * (D : ℝ) ^ 2)
    rw [mul_zero] at h2
    exact eventually_atTop.mp
      ((h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10))).mono fun N h => h.le)
  refine ⟨max (max N₁ N₂) 2, fun N hN z hzN V hV => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 1 ≤ N := by omega
  have hz : 0 < z.im := hZ N z hzN
  have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hNpos⟩)⟩
  have hΛh := lam_isHermitian D N (A N)
  have hΛn : opNorm (lam D N (A N)) ≤ 1 / 10 :=
    (FluctPrelim_opNorm_lam D N hNpos (A N)).trans
      ((mul_le_mul_of_nonneg_left (hseq.small N) (by positivity)).trans (hN₂ N hN2))
  obtain ⟨hMn, hMim⟩ := FluctPrelim_det (lam D N (A N)) hΛh hΛn z hz
  have hIm : 0 < (mExt (lam D N (A N)) z).im := by
    have he1 : mExt (lam D N (A N)) z = mSol (lam D N (A N)) z := by simp [mExt, hz]
    rw [he1]
    exact (mSol_spec _ hΛh z hz).1
  have hunit : ∀ s t : Idx D N → ℂ, ∑ k, ‖s k‖ ^ 2 = 1 → ∑ k, ‖t k‖ ^ 2 = 1 →
      μ N {h | (N : ℝ) ^ ε₁ * φ N z < ‖star s ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z -
        MExt (lam D N (A N)) z) *ᵥ t)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) :=
    fun s t hs ht => hN₁ N hN1 ⟨⟨z, hzN⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  have hNε : 0 < (N : ℝ) ^ ε₁ := Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _
  have hφ : 0 ≤ φ N z := by
    by_contra hneg
    have hneg' : φ N z < 0 := not_le.mp hneg
    obtain ⟨k₀⟩ := this
    have he : ∑ k, ‖(Pi.single k₀ (1 : ℂ) : Idx D N → ℂ) k‖ ^ 2 = 1 := by
      have : ∀ k, ‖(Pi.single k₀ (1 : ℂ) : Idx D N → ℂ) k‖ ^ 2 = if k = k₀ then 1 else 0 := by
        intro k
        by_cases h : k = k₀ <;> simp [h]
      simp [this]
    have hb := hunit _ _ he he
    have huniv : {h : Idx D N → Idx D N → ℂ | (N : ℝ) ^ ε₁ * φ N z <
        ‖star (Pi.single k₀ (1 : ℂ) : Idx D N → ℂ) ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z -
          MExt (lam D N (A N)) z) *ᵥ (Pi.single k₀ (1 : ℂ) : Idx D N → ℂ))‖} = Set.univ :=
      Set.eq_univ_of_forall fun h => by
        simp only [Set.mem_ofPred_eq]
        exact lt_of_lt_of_le (mul_neg_of_pos_of_neg hNε hneg') (norm_nonneg _)
    rw [huniv] at hb
    have := (hseq.mem N).prob
    rw [measure_univ] at hb
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (-D') := ENNReal.one_le_ofReal.mp hb
    have h2 : (N : ℝ) ^ (-D') < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN3) (by linarith)
    linarith
  have hbad : ∀ x y : Idx D N → ℂ, ∑ k, ‖x k‖ ^ 2 ≤ 1 → ∑ k, ‖y k‖ ^ 2 ≤ 1 →
      μ N {h | (N : ℝ) ^ ε₁ * φ N z < ‖star x ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z -
        MExt (lam D N (A N)) z) *ᵥ y)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
    intro x y hx hy
    rcases FluctPrelim_ball_unit x y hx hy with h0 | ⟨s, t, hs, ht, hle⟩
    · have : {h : Idx D N → Idx D N → ℂ | (N : ℝ) ^ ε₁ * φ N z <
          ‖star x ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ y)‖} =
          ∅ := by
        refine Set.eq_empty_of_forall_notMem fun h hh => ?_
        have := h0 (res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z)
        simp only [Set.mem_ofPred_eq, this] at hh
        exact absurd hh (not_lt.mpr (by positivity))
      rw [this, measure_empty]
      exact bot_le
    · refine le_trans (measure_mono ?_) (hunit s t hs ht)
      intro h hh
      exact lt_of_lt_of_le hh (hle _)
  have hsub : (goodSet (lam D N (A N)) z V (5 / 4 + (N : ℝ) ^ ε₁ * φ N z)
      (41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im + (N : ℝ) ^ ε₁ * φ N z))ᶜ ⊆
      ⋃ p ∈ V ×ˢ V, {h : Idx D N → Idx D N → ℂ | (N : ℝ) ^ ε₁ * φ N z <
        ‖star p.1 ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ p.2)‖} := by
    intro h hh
    by_contra hnot
    apply hh
    have hnot' : ∀ u ∈ V, ∀ v ∈ V, ‖star u ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z -
        MExt (lam D N (A N)) z) *ᵥ v)‖ ≤ (N : ℝ) ^ ε₁ * φ N z := by
      intro u hu v hv
      by_contra hlt
      exact hnot (Set.mem_iUnion₂.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, not_le.mp hlt⟩)
    intro x hx y hy
    have hdec : ∀ u v : Idx D N → ℂ,
        star u ⬝ᵥ (res (Matrix.of h + lam D N (A N)) z *ᵥ v) =
          star u ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ v) +
            star u ⬝ᵥ (MExt (lam D N (A N)) z *ᵥ v) := by
      intro u v
      rw [← dotProduct_add, ← Matrix.add_mulVec, sub_add_cancel]
    refine ⟨?_, ?_⟩
    · rw [hdec]
      have h1 := hnot' x hx y hy
      have h2 := FluctPrelim_form_le (MExt (lam D N (A N)) z) x y (hV x hx) (hV y hy)
      calc ‖star x ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ y) +
            star x ⬝ᵥ (MExt (lam D N (A N)) z *ᵥ y)‖
          ≤ ‖star x ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ y)‖ +
            ‖star x ⬝ᵥ (MExt (lam D N (A N)) z *ᵥ y)‖ := norm_add_le _ _
        _ ≤ 5 / 4 + (N : ℝ) ^ ε₁ * φ N z := by linarith
    · rw [hdec, Complex.add_im]
      have h1 := hnot' x hx x hx
      have h2 := hMim x
      have h3 := hV x hx
      have h4 := Complex.im_le_norm (star x ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z -
        MExt (lam D N (A N)) z) *ᵥ x))
      have h5 : 25 / 16 * (z.im + (mExt (lam D N (A N)) z).im) * ∑ i, ‖x i‖ ^ 2 ≤
          25 / 16 * (z.im + (mExt (lam D N (A N)) z).im) :=
        mul_le_of_le_one_right (by positivity) h3
      linarith
  calc μ N (goodSet (lam D N (A N)) z V (5 / 4 + (N : ℝ) ^ ε₁ * φ N z)
        (41 / 16 * z.im + 25 / 16 * (mExt (lam D N (A N)) z).im + (N : ℝ) ^ ε₁ * φ N z))ᶜ
      ≤ μ N (⋃ p ∈ V ×ˢ V, {h : Idx D N → Idx D N → ℂ | (N : ℝ) ^ ε₁ * φ N z <
        ‖star p.1 ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ p.2)‖}) :=
        measure_mono hsub
    _ ≤ ∑ p ∈ V ×ˢ V, μ N {h : Idx D N → Idx D N → ℂ | (N : ℝ) ^ ε₁ * φ N z <
        ‖star p.1 ⬝ᵥ ((res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z) *ᵥ p.2)‖} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ V ×ˢ V, ENNReal.ofReal ((N : ℝ) ^ (-D')) :=
        Finset.sum_le_sum fun p hp => by
          obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
          exact hbad p.1 p.2 (hV _ h1) (hV _ h2)
    _ = ENNReal.ofReal ((V.card : ℝ) ^ 2 * (N : ℝ) ^ (-D')) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul,
          ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
        push_cast
        ring

/-- Young's inequality in the form used after Hölder's: if
`x^{2p} ≤ Σ_{n=1}^{2p} b_n x^{2p-n} + R` with `x ≥ 0` and `b_n ≤ β^n`, then
`x^{2p} ≤ (4pβ)^{2p} + 2R`. -/
theorem young_moment (p : ℕ) (hp : 1 ≤ p) (x β R : ℝ) (b : ℕ → ℝ) (hx : 0 ≤ x) (hβ : 0 ≤ β)
    (hb : ∀ n, b n ≤ β ^ n)
    (h : x ^ (2 * p) ≤ (∑ n ∈ Finset.Icc 1 (2 * p), b n * x ^ (2 * p - n)) + R) :
    x ^ (2 * p) ≤ (4 * p * β) ^ (2 * p) + 2 * R := by
  set q : ℝ := 4 * p with hq
  have hq4 : 4 ≤ q := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hq0 : 0 < q := by linarith
  set m := max x (q * β) with hm
  have hm0 : 0 ≤ m := le_max_of_le_left hx
  have hxm : x ≤ m := le_max_left _ _
  have hβm : β ≤ m * q⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hq0]
    calc β * q = q * β := mul_comm _ _
      _ ≤ m := le_max_right _ _
  have hr0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hr1 : q⁻¹ ≤ 1 / 4 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hq4
  have hterm : ∀ n ∈ Finset.Icc 1 (2 * p), b n * x ^ (2 * p - n) ≤ m ^ (2 * p) * (q⁻¹) ^ n := by
    intro n hn
    have hn2 : n ≤ 2 * p := (Finset.mem_Icc.mp hn).2
    calc b n * x ^ (2 * p - n) ≤ β ^ n * x ^ (2 * p - n) :=
          mul_le_mul_of_nonneg_right (hb n) (pow_nonneg hx _)
      _ ≤ (m * q⁻¹) ^ n * m ^ (2 * p - n) := by gcongr
      _ = m ^ (2 * p) * (q⁻¹) ^ n := by
          rw [mul_pow, mul_comm (m ^ n), mul_assoc, ← pow_add, Nat.add_sub_cancel' hn2]
          ring
  have hgeom : ∑ n ∈ Finset.Icc 1 (2 * p), (q⁻¹) ^ n ≤ 1 / 3 := by
    have e : Finset.Icc 1 (2 * p) = Finset.Ico 1 (2 * p + 1) := rfl
    rw [e]
    refine (geom_sum_Ico_le_of_lt_one hr0 (by linarith)).trans ?_
    rw [pow_one, div_le_iff₀ (by linarith)]
    linarith
  have hS : ∑ n ∈ Finset.Icc 1 (2 * p), b n * x ^ (2 * p - n) ≤ m ^ (2 * p) * (1 / 3) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hgeom (pow_nonneg hm0 _)
  have hmQ : m ^ (2 * p) ≤ x ^ (2 * p) + (q * β) ^ (2 * p) := by
    have h1 : 0 ≤ x ^ (2 * p) := pow_nonneg hx _
    have h2 : 0 ≤ (q * β) ^ (2 * p) := pow_nonneg (by positivity) _
    rcases le_total x (q * β) with hxq | hxq
    · rw [hm, max_eq_right hxq]
      linarith
    · rw [hm, max_eq_left hxq]
      linarith
  have h1 : 0 ≤ x ^ (2 * p) := pow_nonneg hx _
  have h2 : 0 ≤ (q * β) ^ (2 * p) := pow_nonneg (by positivity) _
  nlinarith [hS, hmQ, h]

/-- The conversion of the control of the moment inequalities to the first part of the control
parameter of (2.22) [eq:aniso_local]: for `‖Λ‖ ≤ 1/10`, `η > 0`, `φ ≥ 0`, `a ≥ 1`,
`(((41/16) η + (25/16) Im m + a φ)/(Nη))^{1/2} ≤ (12/5)(1 + |z|) a^{1/2} ((Im m + φ)/(Nη))^{1/2}`. -/
theorem zeta_le_psi (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (hΛn : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (φ a : ℝ)
    (hφ : 0 ≤ φ) (ha : 1 ≤ a) :
    Real.sqrt ((41 / 16 * z.im + 25 / 16 * (mExt Λ z).im + a * φ) / ((N : ℝ) * z.im)) ≤
      12 / 5 * (1 + ‖z‖) * Real.sqrt a *
        Real.sqrt (((mExt Λ z).im + φ) / ((N : ℝ) * z.im)) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hme : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  rw [hme]
  have hI : 0 < (mSol Λ z).im := (mSol_spec Λ hΛ z hz).1
  have hz0 : 0 < ‖z‖ := by
    rw [norm_pos_iff]
    rintro rfl
    simp at hz
  have hlow := (im_mSol_lower Λ hΛ hΛn ‖z‖⁻¹ (inv_pos.mpr hz0) z hz (by rw [inv_inv])).1
  rw [inv_inv] at hlow
  set I := (mSol Λ z).im with hIdef
  set η := z.im with hη
  set t := ‖z‖ with ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNη : 0 < (N : ℝ) * η := mul_pos hN0 hz
  have ha0 : 0 ≤ a := by linarith
  have hu : 1 ≤ (1 + t) ^ 2 := by nlinarith
  have hη' : η ≤ 121 / 100 * (1 + t) ^ 2 * I := by
    refine hlow.trans ?_
    have : (11 / 10 + t) ^ 2 ≤ 121 / 100 * (1 + t) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hI.le
  have hX : 0 ≤ (I + φ) / ((N : ℝ) * η) := div_nonneg (by linarith) hNη.le
  have hmain : 41 / 16 * η + 25 / 16 * I + a * φ ≤ 144 / 25 * (1 + t) ^ 2 * a * (I + φ) := by
    have h1 : 0 ≤ (1 + t) ^ 2 * I := by positivity
    have h2 : 0 ≤ (a - 1) * ((1 + t) ^ 2 * I) := mul_nonneg (by linarith) h1
    have h3 : 0 ≤ ((1 + t) ^ 2 - 1) * (a * φ) := mul_nonneg (by linarith) (by positivity)
    have h4 : 0 ≤ a * φ := by positivity
    nlinarith [h1, h2, h3, h4]
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have hsq : (12 / 5 * (1 + t) * Real.sqrt a * Real.sqrt ((I + φ) / ((N : ℝ) * η))) ^ 2 =
      144 / 25 * (1 + t) ^ 2 * a * ((I + φ) / ((N : ℝ) * η)) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ha0, Real.sq_sqrt hX]
    ring
  rw [hsq, div_le_iff₀ hNη]
  have : 144 / 25 * (1 + t) ^ 2 * a * ((I + φ) / (↑N * η)) * (↑N * η) =
      144 / 25 * (1 + t) ^ 2 * a * (I + φ) := by
    field_simp
  rw [this]
  exact hmain

end RBMTransitionEdge

end
