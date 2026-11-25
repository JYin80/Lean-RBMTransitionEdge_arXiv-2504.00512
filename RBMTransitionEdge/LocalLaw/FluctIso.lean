module

public import RBMTransitionEdge.LocalLaw.FluctIsoOne
public import RBMTransitionEdge.LocalLaw.FluctIsoHigh

@[expose] public section

/-!
# The isotropic fluctuation bounds

The control parameter `Ψ_φ`, the isotropic moment inequality for `(H̲G)_{uv}` of (2.30) [eq:HGline]
in the class, one round of its self-improvement at a single `N` with explicit exponents, the
self-improving step in the form of stochastic domination (Definition 2.8 [stoch_domination]), and
the isotropic `≺` bound behind Lemma 2.9 [lem_loc].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The control parameter `Ψ_φ = √((Im m + φ)/(Nη)) + 1/(Nη)` of the fluctuation bounds, with `φ`
an a priori bound on `|(G - M)_{st}|`; at `φ = 0` it is the size in (2.22) [eq:aniso_local]. -/
def psiPhi {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (N : ℕ) (z : ℂ) (φ : ℝ) :
    ℝ :=
  Real.sqrt (((mExt Λ z).im + φ) / ((N : ℝ) * z.im)) + 1 / ((N : ℝ) * z.im)

/-! ### The form `(H̲G)_{uy}` as a function of the resolvent -/

/-- The diagonal form `S_θ(R) = diag(Σ_r s_{kr} R_{rr})` of the profile map. -/
private lemma FI_sTheta_diag (D N : ℕ) (θ : ℝ) (R : Matrix (Idx D N) (Idx D N) ℂ) :
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

/-- `H̲G = 1 - (Λ - z) M + S_θ(M) M` for a matrix `M` in place of `G` ((2.30) [eq:HGline] with
`H G = 1 - (Λ - z) G`). -/
private def FI_hg (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (M : Matrix (Idx D N) (Idx D N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M +
    Matrix.diagonal (fun k => ∑ r, ((varProf D N θ k r : ℝ) : ℂ) * M r r) * M

/-- The form `u^* (H̲G) y` of `FI_hg`. -/
private def FI_d (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u : Idx D N → ℂ) (M : Matrix (Idx D N) (Idx D N) ℂ) (y : Idx D N → ℂ) : ℂ :=
  star u ⬝ᵥ (FI_hg D N θ Λ z M *ᵥ y)

/-- On Hermitian arrays `u^* (H̲G) y` of (2.30) [eq:HGline] is `FI_d` at `G = (h + Λ - z)⁻¹`. -/
private lemma FI_d_eq (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (u y : Idx D N → ℂ) :
    star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ y) =
      FI_d D N θ Λ z u (res (Matrix.of h + Λ) z) y := by
  have hres := (res_mul_sub (Matrix.of h + Λ) (hh.add hΛ) z hz).1
  have e : hgUnder D N θ (Matrix.of h) Λ z = FI_hg D N θ Λ z (res (Matrix.of h + Λ) z) := by
    unfold hgUnder FI_hg
    rw [FI_sTheta_diag]
    congr 1
    calc Matrix.of h * res (Matrix.of h + Λ) z =
        (Matrix.of h + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z -
          (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * res (Matrix.of h + Λ) z := by
          rw [← Matrix.sub_mul]
          congr 1
          abel
      _ = _ := by rw [hres]
  unfold FI_d
  rw [e]

/-- A continuous function of the resolvent `G = (h + Λ - z)⁻¹` is a.e. strongly measurable and
a.e. bounded for a law of Hermitian arrays: `|G_{kl}| ≤ η⁻¹` confines `G` to a compact set. -/
private lemma FI_bdd {D N : ℕ} {E : Type*} [NormedAddCommGroup E]
    (μ : Measure (Idx D N → Idx D N → ℂ))
    (hherm : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (Φ : Matrix (Idx D N) (Idx D N) ℂ → E)
    (hΦ : Continuous Φ) :
    AEStronglyMeasurable (fun h => Φ (res (Matrix.of h + Λ) z)) μ ∧
      ∃ B : ℝ, ∀ᵐ h ∂μ, ‖Φ (res (Matrix.of h + Λ) z)‖ ≤ B := by
  have hc : Continuous (fun h : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h) + Λ) z) :=
    continuous_pi fun k => continuous_pi fun l =>
      (contDiff_res_symArr Λ hΛ z hz.ne' k l 0).continuous
  have hm : AEStronglyMeasurable (fun h => Φ (res (Matrix.of h + Λ) z)) μ :=
    (hΦ.comp hc).aestronglyMeasurable.congr (by
      filter_upwards [hherm] with h hh
      simp only [Function.comp, symArr_of_isHermitian h hh])
  set S : Set (Matrix (Idx D N) (Idx D N) ℂ) :=
    Set.univ.pi (fun _ => Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) z.im⁻¹)) with hS
  have hSc : IsCompact S :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨hm, B, ?_⟩
  filter_upwards [hherm] with h hh
  refine hB _ fun k _ l _ => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_apply_le_opNorm _ k l).trans (opNorm_res_le _ (hh.add hΛ) z hz)

/-- A continuous function of the resolvent is integrable for a finite law of Hermitian arrays. -/
private lemma FI_int {D N : ℕ} {E : Type*} [NormedAddCommGroup E]
    (μ : Measure (Idx D N → Idx D N → ℂ)) [IsFiniteMeasure μ]
    (hherm : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (Φ : Matrix (Idx D N) (Idx D N) ℂ → E)
    (hΦ : Continuous Φ) :
    Integrable (fun h => Φ (res (Matrix.of h + Λ) z)) μ := by
  obtain ⟨hm, B, hB⟩ := FI_bdd μ hherm Λ hΛ z hz Φ hΦ
  exact Integrable.of_bound hm B hB

/-- Every point of a Hermitian slice is Hermitian. -/
private lemma FI_slice_herm {D N : ℕ} (h : Idx D N → Idx D N → ℂ)
    (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    (Matrix.of (setEntry h i j w)).IsHermitian := by
  have := symArr_isHermitian (setEntry h i j w)
  rwa [symArr_setEntry, symArr_of_isHermitian h hh] at this

/-! ### Vectors -/

/-- `0 ≤ s_{kr} ≤ N⁻¹` for `θ ∈ [0, 1]`. -/
private lemma FI_prof_le (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (k r : Idx D N) :
    0 ≤ varProf D N θ k r ∧ varProf D N θ k r ≤ (N : ℝ)⁻¹ := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast k.1.pos
  have hN : (0 : ℝ) < N := by exact_mod_cast k.2.pos
  have h1 : ((D : ℝ) * N)⁻¹ ≤ (N : ℝ)⁻¹ := by
    rw [mul_inv]
    have : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
    have h2 : 0 ≤ (N : ℝ)⁻¹ := by positivity
    nlinarith
  have h3 : 0 ≤ ((D : ℝ) * N)⁻¹ := by positivity
  unfold varProf
  split_ifs
  · constructor <;> nlinarith [inv_nonneg.mpr hN.le]
  · constructor <;> nlinarith

/-- `|x^* T y| ≤ ‖T‖` for `|x|, |y| ≤ 1`. -/
private lemma FI_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
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

/-- The standard basis vectors have norm `1`. -/
private lemma FI_single_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) :
    ∑ k', ‖(Pi.single k (1 : ℂ) : ι → ℂ) k'‖ ^ 2 = 1 := by
  have : ∀ k' : ι, ‖(Pi.single k (1 : ℂ) : ι → ℂ) k'‖ ^ 2 = if k' = k then 1 else 0 := by
    intro k'
    by_cases h : k' = k <;> simp [h]
  simp [this]

/-- `e_k^* w = w_k`. -/
private lemma FI_single_dot {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) (w : ι → ℂ) :
    star (Pi.single k (1 : ℂ)) ⬝ᵥ w = w k := by
  have : star (Pi.single k (1 : ℂ) : ι → ℂ) = Pi.single k 1 := by
    funext r
    by_cases h : r = k <;> simp [h]
  rw [this, single_one_dotProduct]

/-- The tilted vectors have `|t^r(u)| ≤ |u|`, since `0 ≤ N s_{kr} ≤ 1`. -/
private lemma FI_tilt_norm (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (u : Idx D N → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (r : Idx D N) : ∑ k, ‖tiltV D N θ u r k‖ ^ 2 ≤ 1 := by
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) hu
  have h0 := (FI_prof_le D N θ hθ0 hθ1 k r).1
  have h1 := (FI_prof_le D N θ hθ0 hθ1 k r).2
  have hN : (0 : ℝ) < N := by exact_mod_cast r.2.pos
  have e0 : 0 ≤ (N : ℝ) * varProf D N θ k r := by positivity
  have e1 : (N : ℝ) * varProf D N θ k r ≤ 1 := by
    calc (N : ℝ) * varProf D N θ k r ≤ N * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_left h1 hN.le
      _ = 1 := by field_simp
  simp only [tiltV, norm_mul, Complex.norm_real, Real.norm_of_nonneg e0]
  have : ((N : ℝ) * varProf D N θ k r) ^ 2 ≤ 1 := by nlinarith
  rw [mul_pow]
  exact (mul_le_mul_of_nonneg_left this (sq_nonneg _)).trans (le_of_eq (mul_one _))

/-- `Σ_k |w_k|² = Re(w^* w)`. -/
private lemma FI_sq_eq {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    ((∑ k, ‖w k‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- `|Λ^* u| ≤ 1` for `‖Λ‖ ≤ 1` and `|u| ≤ 1`. -/
private lemma FI_mulVec_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ)
    (hΛh : Λ.IsHermitian) (hΛ : opNorm Λ ≤ 1) (u : ι → ℂ) (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) :
    ∑ k, ‖(Λᴴ *ᵥ u) k‖ ^ 2 ≤ 1 := by
  have e : ((∑ k, ‖(Λᴴ *ᵥ u) k‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ ((Λ * Λᴴ) *ᵥ u) := by
    rw [FI_sq_eq, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have h1 : ‖star u ⬝ᵥ ((Λ * Λᴴ) *ᵥ u)‖ ≤ opNorm (Λ * Λᴴ) := FI_form_le _ u u hu hu
  have h2 : opNorm (Λ * Λᴴ) ≤ opNorm Λ * opNorm Λᴴ := opNorm_mul_le _ _
  have h3 : opNorm Λᴴ = opNorm Λ := by rw [hΛh.eq]
  have h0 : 0 ≤ opNorm Λ := norm_nonneg _
  rw [← e, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
    at h1
  nlinarith

/-- Every vector of `isoVecs` has norm `≤ 1`, for `|u|, |v| ≤ 1`, `‖Λ‖ ≤ 1` and `θ ∈ [0, 1]`. -/
private lemma FI_V_norm (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛh : Λ.IsHermitian) (hΛ : opNorm Λ ≤ 1)
    (u v : Idx D N → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 ≤ 1) (hv : ∑ k, ‖v k‖ ^ 2 ≤ 1) :
    ∀ x ∈ isoVecs D N θ Λ u v, ∑ k, ‖x k‖ ^ 2 ≤ 1 := by
  have ht := FI_tilt_norm D N θ hθ0 hθ1 u hu
  intro x hx
  simp only [isoVecs, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with ((((rfl | rfl | rfl) | ⟨a, rfl⟩) | ⟨k, rfl⟩) | ⟨r, rfl⟩) | ⟨r, rfl⟩
  · exact hu
  · exact hv
  · exact FI_mulVec_norm Λ hΛh hΛ u hu
  · refine le_trans (Finset.sum_le_sum fun k _ => ?_) hu
    have : (Ea D N a)ᴴ = Ea D N a := by
      unfold Ea
      rw [Matrix.diagonal_conjTranspose]
      congr 1
      funext q
      by_cases h : q.1 = a <;> simp [h]
    rw [this]
    unfold Ea
    rw [Matrix.mulVec_diagonal]
    by_cases h : k.1 = a <;> simp [h]
  · exact (FI_single_norm k).le
  · exact ht r
  · simpa using ht r

/-! ### Resolvent polynomials: powers, weights and factors -/

/-- The `n`-th power of a resolvent polynomial. -/
private def FI_pow {D N : ℕ} (P : ResPoly D N) : ℕ → ResPoly D N
  | 0 => [(1, [])]
  | n + 1 => resPolyMul P (FI_pow P n)

private lemma FI_pow_eval {D N : ℕ} (P : ResPoly D N) (h : Idx D N → Idx D N → ℂ) (n : ℕ) :
    resPolyEval (FI_pow P n) h = resPolyEval P h ^ n := by
  induction n with
  | zero => simp [FI_pow, resPolyEval, resMonoEval]
  | succ n ih => rw [FI_pow, resPolyEval_mul, ih, pow_succ, mul_comm]

/-- The sum of the moduli of the coefficients of a resolvent polynomial. -/
private def FI_wt {D N : ℕ} (P : ResPoly D N) : ℝ := (P.map fun t => ‖t.1‖).sum

private lemma FI_wt_nonneg {D N : ℕ} (P : ResPoly D N) : 0 ≤ FI_wt P :=
  List.sum_nonneg fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _

private lemma FI_wt_cons {D N : ℕ} (t : ℂ × ResMono D N) (P : ResPoly D N) :
    FI_wt (t :: P) = ‖t.1‖ + FI_wt P := by
  simp [FI_wt]

private lemma FI_wt_append {D N : ℕ} (P Q : ResPoly D N) :
    FI_wt (P ++ Q) = FI_wt P + FI_wt Q := by
  simp [FI_wt, List.map_append, List.sum_append]

private lemma FI_wt_mul {D N : ℕ} (P Q : ResPoly D N) :
    FI_wt (resPolyMul P Q) = FI_wt P * FI_wt Q := by
  induction P with
  | nil => simp [resPolyMul, FI_wt]
  | cons s P ih =>
    have hrow : ∀ R : ResPoly D N,
        FI_wt (R.map fun t => (s.1 * t.1, s.2 ++ t.2)) = ‖s.1‖ * FI_wt R := by
      intro R
      induction R with
      | nil => simp [FI_wt]
      | cons t R ihR =>
        rw [List.map_cons, FI_wt_cons, ihR, FI_wt_cons, norm_mul]
        ring
    have hsplit : resPolyMul (s :: P) Q
        = (Q.map fun t => (s.1 * t.1, s.2 ++ t.2)) ++ resPolyMul P Q := by
      simp [resPolyMul]
    rw [hsplit, FI_wt_append, hrow, ih, FI_wt_cons]
    ring

private lemma FI_wt_star {D N : ℕ} (P : ResPoly D N) : FI_wt (resPolyStar P) = FI_wt P := by
  induction P with
  | nil => simp [resPolyStar, FI_wt]
  | cons t P ih =>
    have e : resPolyStar (t :: P) = (starRingEnd ℂ t.1,
        t.2.map fun f => (f.2.1, f.1, f.2.2.1, starRingEnd ℂ f.2.2.2)) :: resPolyStar P := rfl
    rw [e, FI_wt_cons, ih, FI_wt_cons, Complex.norm_conj]

private lemma FI_wt_pow {D N : ℕ} (P : ResPoly D N) (W : ℝ) (hW : FI_wt P ≤ W) (n : ℕ) :
    FI_wt (FI_pow P n) ≤ W ^ n := by
  induction n with
  | zero => simp [FI_pow, FI_wt]
  | succ n ih =>
    rw [FI_pow, FI_wt_mul, pow_succ, mul_comm (W ^ n)]
    exact mul_le_mul hW ih (FI_wt_nonneg _) ((FI_wt_nonneg P).trans hW)

/-- Every term has at most `m` factors, each satisfying `Φ`. -/
private def FI_good {D N : ℕ} (m : ℕ) (Φ : ResFactor D N → Prop) (P : ResPoly D N) : Prop :=
  ∀ t ∈ P, t.2.length ≤ m ∧ ∀ f ∈ t.2, Φ f

private lemma FI_good_mul {D N : ℕ} {m n : ℕ} {Φ : ResFactor D N → Prop} {P Q : ResPoly D N}
    (hP : FI_good m Φ P) (hQ : FI_good n Φ Q) : FI_good (m + n) Φ (resPolyMul P Q) := by
  intro t ht
  simp only [resPolyMul, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨s, hs, t', ht', rfl⟩ := ht
  refine ⟨?_, fun f hf => ?_⟩
  · simp only [List.length_append]
    exact Nat.add_le_add (hP s hs).1 (hQ t' ht').1
  · rcases List.mem_append.mp hf with hf | hf
    · exact (hP s hs).2 f hf
    · exact (hQ t' ht').2 f hf

private lemma FI_good_pow {D N : ℕ} {m : ℕ} {Φ : ResFactor D N → Prop} {P : ResPoly D N}
    (hP : FI_good m Φ P) (n : ℕ) : FI_good (m * n) Φ (FI_pow P n) := by
  induction n with
  | zero =>
    intro t ht
    simp only [FI_pow, List.mem_singleton] at ht
    subst ht
    simp
  | succ n ih =>
    have := FI_good_mul hP ih
    rw [show m * (n + 1) = m + m * n by ring]
    exact this

private lemma FI_good_star {D N : ℕ} {m : ℕ} {Φ : ResFactor D N → Prop} {P : ResPoly D N}
    (hΦ : ∀ f, Φ f → Φ (f.2.1, f.1, f.2.2.1, starRingEnd ℂ f.2.2.2))
    (hP : FI_good m Φ P) : FI_good m Φ (resPolyStar P) := by
  intro t ht
  simp only [resPolyStar, List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  refine ⟨by simpa using (hP s hs).1, fun f hf => ?_⟩
  simp only [List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  exact hΦ g ((hP s hs).2 g hg)

private lemma FI_good_mono {D N : ℕ} {m n : ℕ} {Φ : ResFactor D N → Prop} {P : ResPoly D N}
    (hP : FI_good m Φ P) (hmn : m ≤ n) : FI_good n Φ P :=
  fun t ht => ⟨(hP t ht).1.trans hmn, (hP t ht).2⟩

/-! ### Regrouping the expansion by total order -/

/-- `Σ_{p ≤ l} Σ_{q ≤ l - p} T(p, q) = Σ_{k ≤ l} Σ_{a ≤ k} T(a, k - a)`. -/
private lemma FI_regroup {M : Type*} [AddCommMonoid M] (T : ℕ → ℕ → M) (l : ℕ) :
    ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p), T p q =
      ∑ k ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (k + 1), T a (k - a) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have e1 : ∀ p ∈ Finset.range (l + 1 + 1),
        ∑ q ∈ Finset.range (l + 1 + 1 - p), T p q =
          (∑ q ∈ Finset.range (l + 1 - p), T p q) + T p (l + 1 - p) := by
      intro p hp
      have hp' : p ≤ l + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      rw [show l + 1 + 1 - p = (l + 1 - p) + 1 by omega, Finset.sum_range_succ]
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_range_succ
      (fun p => ∑ q ∈ Finset.range (l + 1 - p), T p q), ih, Nat.sub_self, Finset.sum_range_zero,
      add_zero]
    exact (Finset.sum_range_succ (fun k => ∑ a ∈ Finset.range (k + 1), T a (k - a)) (l + 1)).symm

/-! ### The remainder of the expansion in powers of `N` -/

/-- `N^{k/18} = (N^{1/18})^k`. -/
private lemma FI_rpow18 {n : ℝ} (hn : 0 ≤ n) (k : ℕ) :
    n ^ ((k : ℝ) / 18) = (n ^ ((1 : ℝ) / 18)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  congr 1
  ring

/-- `t^a t^{-b} ≤ t^{-c}` for `t ≥ 1` and `a + c ≤ b`. -/
private lemma FI_tpow {t : ℝ} (ht : 1 ≤ t) {a b c : ℕ} (h : a + c ≤ b) :
    t ^ a * (t ^ b)⁻¹ ≤ (t ^ c)⁻¹ := by
  have ht0 : 0 < t := by linarith
  have hb : 0 < t ^ b := pow_pos ht0 b
  have hc : 0 < t ^ c := pow_pos ht0 c
  rw [mul_inv_le_iff₀ hb, ← div_eq_inv_mul, le_div_iff₀ hc, ← pow_add]
  exact pow_le_pow_right₀ ht h

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
private lemma FI_sqrt_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- `x a + y b + w a ≤ (x + y + w)(a + b)` for nonnegative reals. -/
private lemma FI_abc {x y w a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : x * a + y * b + w * a ≤ (x + y + w) * (a + b) := by
  nlinarith [mul_nonneg hx hb, mul_nonneg hy ha, mul_nonneg hw hb]

/-- The remainder of the one-entry expansion at order `ℓ = 16p + 16` with degree `m = 4p - 1`,
truncation `k = 128p + 114`, `M = (24Γ)⁻¹`, summed over `(DN)²` pairs: `≤ c (N^{-p-1} +
N^{21p+18} ε₀^{1/2})` for `1 ≤ Γ ≤ N^{1/6}`, `|z| ≤ N^{1/9}`, `η ≥ N⁻¹` -/
private lemma FI_rem_le (D p : ℕ) (hp : 1 ≤ p) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (N : ℕ) (Γ η zn Wf ε₀ : ℝ) (l m k : ℕ), l = 16 * p + 16 →
      m = 4 * p - 1 → k = 128 * p + 114 → 1 ≤ Γ → Γ ≤ (N : ℝ) ^ ((1 : ℝ) / 6) → 0 ≤ zn →
      zn ≤ (N : ℝ) ^ ((1 : ℝ) / 9) → (N : ℝ)⁻¹ ≤ η → 0 ≤ Wf →
      Wf ≤ (((D : ℝ) + 3) * (1 + zn)) ^ (2 * p) →
      ((D : ℝ) * N) ^ 2 * (Wf * ((N : ℝ) ^ (-((l : ℝ) + 2) / 2) * (6 * Γ) ^ (m + l + 1) +
          (1 + η⁻¹) ^ (m + l + 1) *
            Real.sqrt (max ε₀ 0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^ (-(k : ℝ))))) ≤
        c * ((N : ℝ) ^ (-((p : ℝ) + 1)) + (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀) := by
  set L : ℕ := 20 * p + 16 with hL
  set cW : ℝ := (2 * ((D : ℝ) + 3)) ^ (2 * p) with hcW
  refine ⟨(D : ℝ) ^ 2 * cW * (6 ^ L + 2 ^ L + 2 ^ L * 24 ^ (64 * p + 57)), by positivity, ?_⟩
  intro N Γ η zn Wf ε₀ l m k hl hm hk hΓ1 hΓN hzn0 hzn hη hW0 hW
  -- `N ≥ 1` and `t = N^{1/18} ≥ 1`
  set n : ℝ := (N : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg N
  have hN1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      rw [hn, h0, Nat.cast_zero, Real.zero_rpow (by norm_num)] at hΓN
      linarith
    · rw [hn]
      exact_mod_cast h0
  set t : ℝ := n ^ ((1 : ℝ) / 18) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hN1 (by norm_num)
  have ht0 : 0 < t := by linarith
  have hr : ∀ j : ℕ, n ^ ((j : ℝ) / 18) = t ^ j := fun j => FI_rpow18 hn0 j
  have hn18 : n = t ^ 18 := by
    rw [← hr 18]
    norm_num
  have h6 : n ^ ((1 : ℝ) / 6) = t ^ 3 := by rw [← hr 3]; norm_num
  have h9 : n ^ ((1 : ℝ) / 9) = t ^ 2 := by rw [← hr 2]; norm_num
  have h2 : n ^ ((1 : ℝ) / 2) = t ^ 9 := by rw [← hr 9]; norm_num
  have hlr : n ^ (-((l : ℝ) + 2) / 2) = (t ^ (9 * (l + 2)))⁻¹ := by
    rw [show -((l : ℝ) + 2) / 2 = -(((9 * (l + 2) : ℕ) : ℝ) / 18) by push_cast; ring,
      Real.rpow_neg hn0, hr]
  have hpr : n ^ (-((p : ℝ) + 1)) = (t ^ (18 * (p + 1)))⁻¹ := by
    rw [show -((p : ℝ) + 1) = -(((18 * (p + 1) : ℕ) : ℝ) / 18) by push_cast; ring,
      Real.rpow_neg hn0, hr]
  have hBr : n ^ (21 * (p : ℝ) + 18) = t ^ (18 * (21 * p + 18)) := by
    rw [show 21 * (p : ℝ) + 18 = ((18 * (21 * p + 18) : ℕ) : ℝ) / 18 by push_cast; ring, hr]
  rw [h6] at hΓN
  rw [h9] at hzn
  rw [hlr, hpr, hBr, h2]
  -- the pieces
  have hml : m + l + 1 = L := by rw [hL]; subst hm hl; omega
  rw [hml]
  have hzt : 1 + zn ≤ 2 * t ^ 2 := by
    have : 1 ≤ t ^ 2 := one_le_pow₀ ht1
    linarith
  have hWt : Wf ≤ cW * t ^ (4 * p) := by
    refine hW.trans ?_
    calc (((D : ℝ) + 3) * (1 + zn)) ^ (2 * p) ≤ (((D : ℝ) + 3) * (2 * t ^ 2)) ^ (2 * p) := by
          gcongr
      _ = cW * t ^ (4 * p) := by
          rw [show ((D : ℝ) + 3) * (2 * t ^ 2) = (2 * ((D : ℝ) + 3)) * t ^ 2 by ring, mul_pow,
            ← pow_mul, hcW]
          ring
  have hΓt : (6 * Γ) ^ L ≤ 6 ^ L * t ^ (3 * L) := by
    rw [pow_mul, ← mul_pow]
    gcongr
  have hηt : (1 + η⁻¹) ^ L ≤ 2 ^ L * t ^ (18 * L) := by
    have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
    have h1 : η⁻¹ ≤ n := by
      rw [inv_le_comm₀ hη0 (by linarith)]
      exact hη
    have h2' : 1 + η⁻¹ ≤ 2 * t ^ 18 := by
      have : 1 ≤ t ^ 18 := one_le_pow₀ ht1
      rw [hn18] at h1
      linarith
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2' L
  have hsq : Real.sqrt (max ε₀ 0 + (t ^ 9 * (24 * Γ)⁻¹) ^ (-(k : ℝ))) ≤
      Real.sqrt ε₀ + 24 ^ (64 * p + 57) * (t ^ (6 * (64 * p + 57)))⁻¹ := by
    have hx0 : 0 < t ^ 9 * (24 * Γ)⁻¹ := by positivity
    have hxk : (t ^ 9 * (24 * Γ)⁻¹) ^ (-(k : ℝ)) =
        (((t ^ 9 * (24 * Γ)⁻¹) ^ (64 * p + 57)) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hx0.le, Real.rpow_natCast, ← pow_mul, hk]
      congr 2
      ring
    have hxl : (t ^ 6 * 24⁻¹) ^ (64 * p + 57) ≤ (t ^ 9 * (24 * Γ)⁻¹) ^ (64 * p + 57) := by
      apply pow_le_pow_left₀ (by positivity)
      have hΓ0 : 0 < Γ := by linarith
      rw [mul_inv, ← mul_assoc]
      calc t ^ 6 * 24⁻¹ = t ^ 9 * 24⁻¹ * (t ^ 3)⁻¹ := by
            field_simp
        _ ≤ t ^ 9 * 24⁻¹ * Γ⁻¹ := by gcongr
    have hb : Real.sqrt ((((t ^ 9 * (24 * Γ)⁻¹) ^ (64 * p + 57)) ^ 2)⁻¹) ≤
        24 ^ (64 * p + 57) * (t ^ (6 * (64 * p + 57)))⁻¹ := by
      rw [← inv_pow, Real.sqrt_sq (by positivity)]
      have e : 24 ^ (64 * p + 57) * (t ^ (6 * (64 * p + 57)))⁻¹ =
          ((t ^ 6 * 24⁻¹) ^ (64 * p + 57))⁻¹ := by
        rw [mul_pow, pow_mul, mul_inv, inv_pow, inv_inv, mul_comm]
      rw [e]
      exact inv_anti₀ (by positivity) hxl
    have hm0 : Real.sqrt (max ε₀ 0) = Real.sqrt ε₀ := by
      rcases le_total ε₀ 0 with h | h
      · rw [max_eq_right h, Real.sqrt_zero, Real.sqrt_eq_zero'.mpr h]
      · rw [max_eq_left h]
    rw [hxk]
    refine (FI_sqrt_add (le_max_right _ _) (by positivity)).trans ?_
    rw [hm0]
    linarith
  -- assemble
  have hA : t ^ (36 + 4 * p + 3 * L) * (t ^ (9 * (l + 2)))⁻¹ ≤ (t ^ (18 * (p + 1)))⁻¹ :=
    FI_tpow ht1 (by subst hl; omega)
  have hB : t ^ (36 + 4 * p + 18 * L) ≤ t ^ (18 * (21 * p + 18)) :=
    pow_le_pow_right₀ ht1 (by omega)
  have hC : t ^ (36 + 4 * p + 18 * L) * (t ^ (6 * (64 * p + 57)))⁻¹ ≤ (t ^ (18 * (p + 1)))⁻¹ :=
    FI_tpow ht1 (by omega)
  have hDN : ((D : ℝ) * n) ^ 2 = (D : ℝ) ^ 2 * t ^ 36 := by
    rw [hn18, mul_pow, ← pow_mul]
  have hS0 : 0 ≤ Real.sqrt ε₀ := Real.sqrt_nonneg _
  have hI0 : 0 ≤ (t ^ (6 * (64 * p + 57)))⁻¹ := by positivity
  have hJ0 : 0 ≤ (t ^ (9 * (l + 2)))⁻¹ := by positivity
  have hcW0 : 0 ≤ cW := by positivity
  have hsq0 : 0 ≤ Real.sqrt (max ε₀ 0 + (t ^ 9 * (24 * Γ)⁻¹) ^ (-(k : ℝ))) := Real.sqrt_nonneg _
  calc ((D : ℝ) * n) ^ 2 * (Wf * ((t ^ (9 * (l + 2)))⁻¹ * (6 * Γ) ^ L +
        (1 + η⁻¹) ^ L * Real.sqrt (max ε₀ 0 + (t ^ 9 * (24 * Γ)⁻¹) ^ (-(k : ℝ)))))
      ≤ (D : ℝ) ^ 2 * t ^ 36 * (cW * t ^ (4 * p) * ((t ^ (9 * (l + 2)))⁻¹ * (6 ^ L * t ^ (3 * L)) +
        2 ^ L * t ^ (18 * L) * (Real.sqrt ε₀ +
          24 ^ (64 * p + 57) * (t ^ (6 * (64 * p + 57)))⁻¹))) := by
        rw [hDN]
        have hL6 : (0 : ℝ) ≤ 2 ^ L * t ^ (18 * L) := by positivity
        have hΓ0 : 0 ≤ 6 * Γ := by linarith
        have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
        have hX0 : 0 ≤ (t ^ (9 * (l + 2)))⁻¹ * (6 * Γ) ^ L +
            (1 + η⁻¹) ^ L * Real.sqrt (max ε₀ 0 + (t ^ 9 * (24 * Γ)⁻¹) ^ (-(k : ℝ))) :=
          add_nonneg (mul_nonneg hJ0 (pow_nonneg hΓ0 _)) (mul_nonneg (by positivity) hsq0)
        refine mul_le_mul_of_nonneg_left (mul_le_mul hWt (add_le_add
          (mul_le_mul_of_nonneg_left hΓt hJ0) (mul_le_mul hηt hsq hsq0 hL6)) hX0
          (by positivity)) (by positivity)
    _ = (D : ℝ) ^ 2 * cW * (6 ^ L * (t ^ (36 + 4 * p + 3 * L) * (t ^ (9 * (l + 2)))⁻¹) +
        2 ^ L * (t ^ (36 + 4 * p + 18 * L) * Real.sqrt ε₀) +
        2 ^ L * 24 ^ (64 * p + 57) *
          (t ^ (36 + 4 * p + 18 * L) * (t ^ (6 * (64 * p + 57)))⁻¹)) := by
        rw [pow_add, pow_add, pow_add, pow_add]
        ring
    _ ≤ (D : ℝ) ^ 2 * cW * (6 ^ L * (t ^ (18 * (p + 1)))⁻¹ +
        2 ^ L * (t ^ (18 * (21 * p + 18)) * Real.sqrt ε₀) +
        2 ^ L * 24 ^ (64 * p + 57) * (t ^ (18 * (p + 1)))⁻¹) := by
        have e1 : (0 : ℝ) ≤ 6 ^ L := by positivity
        have e2 : (0 : ℝ) ≤ 2 ^ L := by positivity
        have e3 : (0 : ℝ) ≤ 2 ^ L * 24 ^ (64 * p + 57) := by positivity
        exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hA e1)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB hS0) e2))
          (mul_le_mul_of_nonneg_left hC e3)) (by positivity)
    _ ≤ (D : ℝ) ^ 2 * cW * (6 ^ L + 2 ^ L + 2 ^ L * 24 ^ (64 * p + 57)) *
        ((t ^ (18 * (p + 1)))⁻¹ + t ^ (18 * (21 * p + 18)) * Real.sqrt ε₀) := by
        have h1 : 0 ≤ (t ^ (18 * (p + 1)))⁻¹ := by positivity
        have h2 : 0 ≤ t ^ (18 * (21 * p + 18)) * Real.sqrt ε₀ := by positivity
        have h3 : (0 : ℝ) ≤ 6 ^ L := by positivity
        have h4 : (0 : ℝ) ≤ 2 ^ L := by positivity
        have h5 : (0 : ℝ) ≤ 2 ^ L * 24 ^ (64 * p + 57) := by positivity
        have h6 : 0 ≤ (D : ℝ) ^ 2 * cW := by positivity
        have key : 6 ^ L * (t ^ (18 * (p + 1)))⁻¹ +
            2 ^ L * (t ^ (18 * (21 * p + 18)) * Real.sqrt ε₀) +
            2 ^ L * 24 ^ (64 * p + 57) * (t ^ (18 * (p + 1)))⁻¹ ≤
            (6 ^ L + 2 ^ L + 2 ^ L * 24 ^ (64 * p + 57)) *
              ((t ^ (18 * (p + 1)))⁻¹ + t ^ (18 * (21 * p + 18)) * Real.sqrt ε₀) := by
          exact FI_abc h3 h4 h5 h1 h2
        calc (D : ℝ) ^ 2 * cW * (6 ^ L * (t ^ (18 * (p + 1)))⁻¹ +
              2 ^ L * (t ^ (18 * (21 * p + 18)) * Real.sqrt ε₀) +
              2 ^ L * 24 ^ (64 * p + 57) * (t ^ (18 * (p + 1)))⁻¹)
            ≤ (D : ℝ) ^ 2 * cW * ((6 ^ L + 2 ^ L + 2 ^ L * 24 ^ (64 * p + 57)) *
              ((t ^ (18 * (p + 1)))⁻¹ + t ^ (18 * (21 * p + 18)) * Real.sqrt ε₀)) :=
              mul_le_mul_of_nonneg_left key h6
          _ = _ := by ring

/-! ### The isotropic expansion -/

/-- `𝒞^{(0,1)}(h_{ji}) = E h̄_{ji} = 0` (mean zero). -/
private lemma FI_ccum01 (D N : ℕ) (C : ℕ → ℝ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N C θ μ) (i j : Idx D N) : ccum (μ.map fun h => h j i) 0 1 = 0 := by
  have hprob := hμ.prob
  have hmeas : Measurable fun h : Idx D N → Idx D N → ℂ => h j i :=
    (measurable_pi_apply i).comp (measurable_pi_apply j)
  have hν : IsProbabilityMeasure (μ.map fun h => h j i) :=
    inferInstance
  have hint : ∀ q : ℕ, Integrable (fun w : ℂ => ‖w‖ ^ q) (μ.map fun h => h j i) := by
    intro q
    refine (integrable_map_measure (by fun_prop) hmeas.aemeasurable).mpr ?_
    exact hμ.integrable q j i
  have hrec := moment_ccum_recursion (μ.map fun h => h j i) hint 0 0
  simp only [pow_zero, zero_add, pow_one, one_mul, Finset.range_one, Finset.sum_singleton,
    Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_zero, integral_const, probReal_univ,
    one_smul] at hrec
  rw [← hrec, integral_map hmeas.aemeasurable (by fun_prop), integral_conj, hμ.mean j i, map_zero]

/-- The function `f = G_{jv} (H̲G)_{uv}^{p-1} conj((H̲G)_{uv})^p` of the isotropic expansion. -/
private def FI_F (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (p : ℕ) (j : Idx D N) (h : Idx D N → Idx D N → ℂ) : ℂ :=
  (res (Matrix.of h + Λ) z *ᵥ v) j * (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ (p - 1) *
    starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ p

/-- The order-`k` term of the expansion in the entry `(j, i)`, the summand of `isoTerm`. -/
private def FI_T (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (u v : Idx D N → ℂ) (p : ℕ) (i j : Idx D N)
    (k : ℕ) : ℂ :=
  ∑ a ∈ Finset.range (k + 1),
    ccum (μ.map fun h => h j i) a (k - a + 1) / ((a.factorial * (k - a).factorial : ℕ) : ℂ) *
      ∫ h, wirt a (k - a) (fun w => FI_F D N θ Λ z u v p j (setEntry h j i w)) (h j i) ∂μ

private lemma FI_isoTerm_eq (D N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (u v : Idx D N → ℂ) (p k : ℕ) :
    isoTerm D N θ μ Λ z u v p k =
      ∑ i, ∑ j, starRingEnd ℂ (u i) * FI_T D N θ μ Λ z u v p i j k := rfl

/-- The expansion of `E h_{ij} f` in the entry `(j, i)` to order `ℓ = 16p + 16`
(Lemma 2.11 [lem:complex_cumu], (2.26) [5.16]) with the high-probability remainder of
`expansion_hp`, `M = (24Γ)⁻¹` and truncation `128p + 114`. -/
private lemma FI_entry (D p : ℕ) (hp : 1 ≤ p) (C : ℕ → ℝ) :
    ∃ Ke : ℝ, 0 ≤ Ke ∧ ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ z : ℂ, 0 < z.im → ∀ u v : Idx D N → ℂ, ∑ k, ‖u k‖ ^ 2 ≤ 1 → ∑ k, ‖v k‖ ^ 2 ≤ 1 →
      ∀ Γ Υ lb ε₀ : ℝ, 1 ≤ Γ → μ (isoGood D N θ Λ z u v Γ Υ lb)ᶜ ≤ ENNReal.ofReal ε₀ →
      ∀ i j : Idx D N,
        ‖(∫ h, h i j * FI_F D N θ Λ z u v p j h ∂μ) -
            ∑ k ∈ Finset.range (16 * p + 16 + 1), FI_T D N θ μ Λ z u v p i j k‖ ≤
          Ke * ((((D : ℝ) + 3) * (1 + ‖z‖)) ^ (2 * p) *
            ((N : ℝ) ^ (-(((16 * p + 16 : ℕ) : ℝ) + 2) / 2) *
                (6 * Γ) ^ (4 * p - 1 + (16 * p + 16) + 1) +
              (1 + z.im⁻¹) ^ (4 * p - 1 + (16 * p + 16) + 1) *
                Real.sqrt (max ε₀ 0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^
                  (-((128 * p + 114 : ℕ) : ℝ))))) := by
  obtain ⟨Ke, hKe0, hKe⟩ := expansion_hp (16 * p + 16) (4 * p - 1) (128 * p + 114) C
  refine ⟨Ke, hKe0, ?_⟩
  intro N θ μ hμ hθ0 hθ1 Λ hΛ hΛn z hz u v hu hv Γ Υ lb ε₀ hΓ1 hbad i j
  have hprob := hμ.prob
  set V := isoVecs D N θ Λ u v with hV
  have hVn : ∀ x ∈ V, ∑ r, ‖x r‖ ^ 2 ≤ 1 :=
    FI_V_norm D N θ hθ0 hθ1 Λ hΛ (by linarith) u v hu hv
  have mu : u ∈ V := by simp [hV, isoVecs]
  have mv : v ∈ V := by simp [hV, isoVecs]
  have mL : Λᴴ *ᵥ u ∈ V := by simp [hV, isoVecs]
  have mE : ∀ a, (Ea D N a)ᴴ *ᵥ u ∈ V := by
    intro a
    rw [hV]
    unfold isoVecs
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))))
  have me : ∀ k, (Pi.single k 1 : Idx D N → ℂ) ∈ V := by
    intro k
    rw [hV]
    unfold isoVecs
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))))
  obtain ⟨P, hPf, hPw, hPe⟩ := hgUnder_resPoly D N θ hθ0 hθ1 Λ hΛ z hz u v hu hv
  set W : ℝ := ((D : ℝ) + 3) * (1 + ‖z‖) with hW
  have hW1 : 1 ≤ W := by
    have h0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have h1 := norm_nonneg z
    nlinarith
  set PG : ResPoly D N := [(1, [(Pi.single j 1, v, Λ, z)])] with hPG
  set PF : ResPoly D N :=
    resPolyMul PG (resPolyMul (FI_pow P (p - 1)) (FI_pow (resPolyStar P) p)) with hPF
  set Φ : ResFactor D N → Prop := fun f => f.1 ∈ V ∧ f.2.1 ∈ V ∧ f.2.2.1 = Λ ∧
    (f.2.2.2 = z ∨ f.2.2.2 = starRingEnd ℂ z) with hΦ
  have hΦs : ∀ f, Φ f → Φ (f.2.1, f.1, f.2.2.1, starRingEnd ℂ f.2.2.2) := by
    rintro ⟨x, y, L, ξ⟩ ⟨h1, h2, h3, h4⟩
    refine ⟨h2, h1, h3, ?_⟩
    rcases h4 with h4 | h4
    · exact Or.inr (by simp only at h4 ⊢; rw [h4])
    · exact Or.inl (by simp only at h4 ⊢; rw [h4, Complex.conj_conj])
  have hGP : FI_good 2 Φ P := by
    intro t ht
    refine ⟨(hPf t ht).1, fun f hf => ?_⟩
    obtain ⟨h1, h2, h3⟩ := (hPf t ht).2 f hf
    refine ⟨?_, ?_, by rw [h3], Or.inl (by rw [h3])⟩
    · rcases h1 with h1 | h1 | ⟨a, h1⟩ | ⟨k, h1⟩ <;> rw [h1]
      · exact mu
      · exact mL
      · exact mE a
      · exact me k
    · rcases h2 with h2 | ⟨k, h2⟩ <;> rw [h2]
      · exact mv
      · exact me k
  have hGG : FI_good 1 Φ PG := by
    intro t ht
    rw [hPG, List.mem_singleton] at ht
    subst ht
    refine ⟨by simp, fun f hf => ?_⟩
    rw [List.mem_singleton] at hf
    subst hf
    exact ⟨me j, mv, rfl, Or.inl rfl⟩
  have hGF : FI_good (4 * p - 1) Φ PF :=
    FI_good_mono (FI_good_mul hGG (FI_good_mul (FI_good_pow hGP (p - 1))
      (FI_good_pow (FI_good_star hΦs hGP) p))) (by omega)
  have hPF' : ∀ t ∈ PF, t.2.length ≤ 4 * p - 1 ∧ ∀ f ∈ t.2, f.1 ∈ V ∧ f.2.1 ∈ V ∧
      ∃ q ∈ ({(Λ, z)} : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ)),
        f.2.2 = q ∨ f.2.2 = (q.1, starRingEnd ℂ q.2) := by
    intro t ht
    refine ⟨(hGF t ht).1, fun f hf => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := (hGF t ht).2 f hf
    refine ⟨h1, h2, (Λ, z), Finset.mem_singleton_self _, ?_⟩
    rcases h4 with h4 | h4
    · exact Or.inl (Prod.ext h3 h4)
    · exact Or.inr (Prod.ext h3 h4)
  -- the value of `PF`
  have hPH : ∀ t ∈ P, ∀ f ∈ t.2, f.2.2.1.IsHermitian := by
    intro t ht f hf
    rw [((hPf t ht).2 f hf).2.2]
    exact hΛ
  have hevF : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian →
      resPolyEval PF h = FI_F D N θ Λ z u v p j h := by
    intro h hh
    rw [hPF, resPolyEval_mul, resPolyEval_mul, FI_pow_eval, FI_pow_eval,
      resPolyEval_star P hPH h hh, hPe h hh]
    simp only [hPG, resPolyEval, resMonoEval, resFactorEval, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil, FI_single_dot, FI_F]
    ring
  -- the weight of `PF`
  have hwF : (PF.map fun t => ‖t.1‖).sum ≤ W ^ (2 * p) := by
    change FI_wt PF ≤ W ^ (2 * p)
    have hG1 : FI_wt PG = 1 := by simp [hPG, FI_wt]
    have hwP : FI_wt P ≤ W := hPw
    rw [hPF, FI_wt_mul, FI_wt_mul, hG1, one_mul]
    have h1 := FI_wt_pow P W hwP (p - 1)
    have h2 := FI_wt_pow (resPolyStar P) W (by rw [FI_wt_star]; exact hwP) p
    calc FI_wt (FI_pow P (p - 1)) * FI_wt (FI_pow (resPolyStar P) p) ≤ W ^ (p - 1) * W ^ p :=
          mul_le_mul h1 h2 (FI_wt_nonneg _) (by positivity)
      _ = W ^ (p - 1 + p) := by rw [pow_add]
      _ ≤ W ^ (2 * p) := pow_le_pow_right₀ hW1 (by omega)
  -- the bad event of the expansion
  have hbadE : μ {h | ∃ q ∈ ({(Λ, z)} : Finset (Matrix (Idx D N) (Idx D N) ℂ × ℂ)),
      ∃ x ∈ V, ∃ y ∈ V, Γ < ‖resFactorEval (x, y, q.1, q.2) (symArr h)‖} ≤
        ENNReal.ofReal (max ε₀ 0) := by
    refine le_trans (measure_mono_ae ?_) (hbad.trans (ENNReal.ofReal_le_ofReal
      (le_max_left _ _)))
    filter_upwards [hμ.herm] with h hh hmem hgood
    obtain ⟨q, hq, x, hx, y, hy, hlt⟩ := hmem
    rw [Finset.mem_singleton] at hq
    subst hq
    rw [symArr_of_isHermitian h hh] at hlt
    exact absurd ((hgood.1 x hx y hy).1) (not_le.mpr hlt)
  have hM : 24 * (24 * Γ)⁻¹ * Γ ≤ 1 := by
    have hΓ0 : Γ ≠ 0 := by positivity
    field_simp
    exact le_rfl
  have key := hKe D N θ μ hμ {(Λ, z)} z.im hz (by
      intro q hq
      rw [Finset.mem_singleton] at hq
      subst hq
      exact ⟨hΛ, le_rfl⟩) j i V (me j) (me i) hVn PF hPF' Γ (24 * Γ)⁻¹ (max ε₀ 0) hΓ1
    (by positivity) hM (le_max_right _ _) hbadE
  -- rewrite the expansion in terms of `FI_F` and `FI_T`
  have he1 : ∫ h, resPolyEval PF h * starRingEnd ℂ (h j i) ∂μ =
      ∫ h, h i j * FI_F D N θ Λ z u v p j h ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    have hc : starRingEnd ℂ (h j i) = h i j := by simpa using hh.apply i j
    rw [hevF h hh, hc, mul_comm]
  have he2 : ∀ a q : ℕ,
      ∫ h, wirt a q (fun w => resPolyEval PF (setEntry h j i w)) (h j i) ∂μ =
        ∫ h, wirt a q (fun w => FI_F D N θ Λ z u v p j (setEntry h j i w)) (h j i) ∂μ := by
    intro a q
    refine integral_congr_ae ?_
    filter_upwards [hμ.herm] with h hh
    have : (fun w => resPolyEval PF (setEntry h j i w)) =
        fun w => FI_F D N θ Λ z u v p j (setEntry h j i w) :=
      funext fun w => hevF _ (FI_slice_herm h hh j i w)
    rw [this]
  have hreg := FI_regroup (fun a q => ccum (μ.map fun h => h j i) a (q + 1) /
      ((a.factorial * q.factorial : ℕ) : ℂ) *
      ∫ h, wirt a q (fun w => FI_F D N θ Λ z u v p j (setEntry h j i w)) (h j i) ∂μ)
    (16 * p + 16)
  simp only [he1, he2] at key
  rw [hreg] at key
  refine key.trans ?_
  have hbr0 : 0 ≤ (N : ℝ) ^ (-(((16 * p + 16 : ℕ) : ℝ) + 2) / 2) *
        (6 * Γ) ^ (4 * p - 1 + (16 * p + 16) + 1) +
      (1 + z.im⁻¹) ^ (4 * p - 1 + (16 * p + 16) + 1) *
        Real.sqrt (max ε₀ 0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^
          (-((128 * p + 114 : ℕ) : ℝ))) := by
    have hΓ0 : 0 ≤ 6 * Γ := by linarith
    have : 0 ≤ (1 + z.im⁻¹) := by positivity
    positivity
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwF hbr0) hKe0

/-- `𝒟 · 𝒟^{p-1} conj(𝒟)^p = Σ_{ij} ū_i h_{ij} f_{ij} + (S_θ(G) G)_{uv} 𝒟^{p-1} conj(𝒟)^p` with
`𝒟 = (H̲G)_{uv} = (H G + S_θ(G) G)_{uv}` of (2.30) [eq:HGline]. -/
private lemma FI_split (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ)
    (u v : Idx D N → ℂ) (p : ℕ) (h : Idx D N → Idx D N → ℂ) :
    (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ p =
      (∑ i, ∑ j, starRingEnd ℂ (u i) * (h i j * FI_F D N θ Λ z u v p j h)) +
        (star u ⬝ᵥ ((sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z) *ᵥ v)) *
          (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ (p - 1) *
          starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ p := by
  have e : star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v) =
      (∑ i, ∑ j, starRingEnd ℂ (u i) * (h i j * (res (Matrix.of h + Λ) z *ᵥ v) j)) +
        star u ⬝ᵥ ((sTheta D N θ (res (Matrix.of h + Λ) z) * res (Matrix.of h + Λ) z) *ᵥ v) := by
    unfold hgUnder
    rw [Matrix.add_mulVec, dotProduct_add]
    congr 1
    rw [← Matrix.mulVec_mulVec]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def,
      Matrix.of_apply]
  conv_lhs => arg 1; arg 1; rw [e]
  rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold FI_F
  ring

/-- `a b ≤ (a b²)^{2/3}` for `0 ≤ a ≤ b`. -/
private lemma FI_two_thirds {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a * b ≤ (a * b ^ 2) ^ (((2 : ℕ) : ℝ) / 3) := by
  have hb : 0 ≤ b := ha.trans hab
  have h1 : (a * b) ^ 3 ≤ (a * b ^ 2) ^ 2 := by
    have : 0 ≤ a ^ 2 * b ^ 3 * (b - a) :=
      mul_nonneg (mul_nonneg (sq_nonneg a) (pow_nonneg hb 3)) (sub_nonneg.mpr hab)
    nlinarith
  have e1 : ((a * b) ^ 3) ^ (((3 : ℕ) : ℝ)⁻¹) = a * b :=
    Real.pow_rpow_inv_natCast (mul_nonneg ha hb) (by norm_num)
  have e2 : (a * b ^ 2) ^ (((2 : ℕ) : ℝ) / 3) = ((a * b ^ 2) ^ 2) ^ (((3 : ℕ) : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast (a * b ^ 2) 2, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [e2, ← e1]
  exact Real.rpow_le_rpow (by positivity) h1 (by positivity)

/-- The isotropic moment inequality for one member of the class: with
`ζ̂ = (√D + 3)(1 + |z|) Γ³ (Υ/(Nη))^{1/2} ≤ λ` and the good event `isoGood` off probability `ε₀`,
`E|(H̲G)_{uv}|^{2p} ≤ K Σ_{n=1}^{2p} (ζ̂ λ²)^{n/3} E|(H̲G)_{uv}|^{2p-n}
+ K (N^{-p-1} + N^{21p+18} ε₀^{1/2})`. -/
theorem iso_moment_ineq (D p : ℕ) (hp : 1 ≤ p) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ z : ℂ, ((N : ℝ))⁻¹ ≤ z.im → ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) →
      ∀ u v : Idx D N → ℂ, ∑ k, ‖u k‖ ^ 2 ≤ 1 → ∑ k, ‖v k‖ ^ 2 ≤ 1 →
      ∀ Γ Υ lb ε₀ : ℝ, 1 ≤ Γ → Γ ≤ (N : ℝ) ^ ((1 : ℝ) / 6) → z.im ≤ Υ →
        Υ ≤ (N : ℝ) * z.im →
        (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ≤ lb →
        μ (isoGood D N θ Λ z u v Γ Υ lb)ᶜ ≤ ENNReal.ofReal ε₀ →
        ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p) ∂μ ≤
          K * (∑ n ∈ Finset.Icc 1 (2 * p),
              ((Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) *
                lb ^ 2) ^ ((n : ℝ) / 3) *
              ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - n) ∂μ) +
            K * ((N : ℝ) ^ (-((p : ℝ) + 1)) + (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := iso_order_one D p hp C
  set Kh : ℕ → ℝ := fun k => if hk : 2 ≤ k ∧ k ≤ 16 * p + 16 then
      (iso_order_high' D p k hp hk.1 hk.2 C).choose else 0 with hKhdef
  have hKh0 : ∀ k, 0 ≤ Kh k := by
    intro k
    simp only [hKhdef]
    split_ifs with hk
    · exact (iso_order_high' D p k hp hk.1 hk.2 C).choose_spec.1
    · exact le_rfl
  obtain ⟨Ke, hKe0, hKe⟩ := FI_entry D p hp C
  obtain ⟨cR, hcR0, hcR⟩ := FI_rem_le D p hp
  set Ks : ℝ := ∑ k ∈ Finset.Ico 2 (16 * p + 16 + 1), Kh k with hKs
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun k _ => hKh0 k
  refine ⟨K₁ + Ks + Ke * cR, by positivity, ?_⟩
  intro N θ μ hμ hθ0 hθ1 Λ hΛ hΛn z hzN hzn u v hu hv Γ Υ lb ε₀ hΓ1 hΓN hΥ1 hΥ2 hlb hbad
  have hprob := hμ.prob
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      have : ((0 : ℕ) : ℝ) ^ ((1 : ℝ) / 6) = 0 := by
        rw [Nat.cast_zero]
        exact Real.zero_rpow (by norm_num)
      linarith
    · exact h0
  have hz : 0 < z.im := lt_of_lt_of_le (by positivity) hzN
  -- the integrability of the pieces
  have hFint : ∀ i j : Idx D N, Integrable (fun h => h i j * FI_F D N θ Λ z u v p j h) μ := by
    intro i j
    obtain ⟨hm, B, hB⟩ := FI_bdd μ hμ.herm Λ hΛ z hz
      (fun M => (M *ᵥ v) j * FI_d D N θ Λ z u M v ^ (p - 1) *
        starRingEnd ℂ (FI_d D N θ Λ z u M v) ^ p) (by unfold FI_d FI_hg; fun_prop)
    have hae : (fun h => FI_F D N θ Λ z u v p j h) =ᵐ[μ] fun h =>
        (res (Matrix.of h + Λ) z *ᵥ v) j * FI_d D N θ Λ z u (res (Matrix.of h + Λ) z) v ^ (p - 1) *
          starRingEnd ℂ (FI_d D N θ Λ z u (res (Matrix.of h + Λ) z) v) ^ p := by
      filter_upwards [hμ.herm] with h hh
      simp only [FI_F, FI_d_eq D N θ Λ hΛ z hz h hh]
    have hFm := hm.congr hae.symm
    have hFb : ∀ᵐ h ∂μ, ‖FI_F D N θ Λ z u v p j h‖ ≤ B := by
      filter_upwards [hae, hB] with h e hb
      rw [e]
      exact hb
    have hmeas' : Measurable fun h : Idx D N → Idx D N → ℂ => h i j :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    have hmeas : AEStronglyMeasurable (fun h : Idx D N → Idx D N → ℂ => h i j) μ :=
      hmeas'.aestronglyMeasurable
    have hhij : Integrable (fun h : Idx D N → Idx D N → ℂ => h i j) μ := by
      refine (integrable_norm_iff hmeas).mp ?_
      simpa using hμ.integrable 1 i j
    exact (hhij.bdd_mul hFm hFb).congr (Eventually.of_forall fun h => mul_comm _ _)
  have hQint : Integrable (fun h => (star u ⬝ᵥ ((sTheta D N θ (res (Matrix.of h + Λ) z) *
      res (Matrix.of h + Λ) z) *ᵥ v)) *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ p) μ := by
    refine (FI_int μ hμ.herm Λ hΛ z hz (fun M => (star u ⬝ᵥ ((Matrix.diagonal (fun k =>
        ∑ r, ((varProf D N θ k r : ℝ) : ℂ) * M r r) * M) *ᵥ v)) *
        FI_d D N θ Λ z u M v ^ (p - 1) * starRingEnd ℂ (FI_d D N θ Λ z u M v) ^ p)
      (by unfold FI_d FI_hg; fun_prop)).congr ?_
    filter_upwards [hμ.herm] with h hh
    simp only [FI_d_eq D N θ Λ hΛ z hz h hh, FI_sTheta_diag]
  -- step 1: the moment as the expectation of `𝒟 𝒟^{p-1} conj(𝒟)^p`
  have hE : ((∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p) ∂μ : ℝ) : ℂ) =
      ∫ h, (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ p ∂μ := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only
    set d := star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)
    have e1 : d * d ^ (p - 1) = d ^ p := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e1, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
    push_cast
    ring
  -- step 2: the split into the entries and the self-energy term
  have hsplit : ∫ h, (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) *
        (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ (p - 1) *
        starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ p ∂μ =
      ∑ i, ∑ j, starRingEnd ℂ (u i) * ∫ h, h i j * FI_F D N θ Λ z u v p j h ∂μ +
        ∫ h, (star u ⬝ᵥ ((sTheta D N θ (res (Matrix.of h + Λ) z) *
            res (Matrix.of h + Λ) z) *ᵥ v)) *
          (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ (p - 1) *
          starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ p ∂μ := by
    have hrow : ∀ i, Integrable (fun h => ∑ j, starRingEnd ℂ (u i) *
        (h i j * FI_F D N θ Λ z u v p j h)) μ :=
      fun i => integrable_finsetSum _ fun j _ => (hFint i j).const_mul _
    rw [integral_congr_ae (Eventually.of_forall fun h => FI_split D N θ Λ z u v p h),
      integral_add (integrable_finsetSum _ fun i _ => hrow i) hQint,
      integral_finsetSum _ fun i _ => hrow i]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hFint i j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  -- step 3: the orders
  set l : ℕ := 16 * p + 16 with hl
  have hT : ∑ k ∈ Finset.range (l + 1), isoTerm D N θ μ Λ z u v p k =
      ∑ i, ∑ j, starRingEnd ℂ (u i) *
        ∑ k ∈ Finset.range (l + 1), FI_T D N θ μ Λ z u v p i j k := by
    simp only [FI_isoTerm_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  have hT0 : isoTerm D N θ μ Λ z u v p 0 = 0 := by
    rw [FI_isoTerm_eq]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    simp [FI_T, FI_ccum01 D N C θ μ hμ i j]
  have hTsplit : ∑ k ∈ Finset.range (l + 1), isoTerm D N θ μ Λ z u v p k =
      isoTerm D N θ μ Λ z u v p 1 +
        ∑ k ∈ Finset.Ico 2 (l + 1), isoTerm D N θ μ Λ z u v p k := by
    rw [← Finset.sum_range_add_sum_Ico _ (show 2 ≤ l + 1 by omega), Finset.sum_range_succ,
      Finset.sum_range_one, hT0, zero_add]
  set Q : ℂ := ∫ h, (star u ⬝ᵥ ((sTheta D N θ (res (Matrix.of h + Λ) z) *
            res (Matrix.of h + Λ) z) *ᵥ v)) *
          (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ (p - 1) *
          starRingEnd ℂ (star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)) ^ p ∂μ with hQ
  set Err : ℂ := ∑ i, ∑ j, starRingEnd ℂ (u i) * ((∫ h, h i j * FI_F D N θ Λ z u v p j h ∂μ) -
      ∑ k ∈ Finset.range (l + 1), FI_T D N θ μ Λ z u v p i j k) with hErr
  have hdecomp : ((∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p) ∂μ : ℝ) :
      ℂ) = Err + (isoTerm D N θ μ Λ z u v p 1 + Q) +
        ∑ k ∈ Finset.Ico 2 (l + 1), isoTerm D N θ μ Λ z u v p k := by
    rw [hE, hsplit]
    have : ∑ i, ∑ j, starRingEnd ℂ (u i) * ∫ h, h i j * FI_F D N θ Λ z u v p j h ∂μ =
        Err + ∑ k ∈ Finset.range (l + 1), isoTerm D N θ μ Λ z u v p k := by
      rw [hT, hErr, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, hTsplit]
    ring
  -- step 4: the bounds
  set X : ℝ := (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) with hX
  set S : ℝ := ∑ n ∈ Finset.Icc 1 (2 * p), (X * lb ^ 2) ^ ((n : ℝ) / 3) *
      ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - n) ∂μ with hS
  set B : ℝ := (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ with hB
  set Np : ℝ := (N : ℝ) ^ (-((p : ℝ) + 1)) with hNp
  have hX0 : 0 ≤ X := by
    have : 0 ≤ Γ ^ 3 := pow_nonneg (by linarith) 3
    positivity
  have hlb0 : 0 ≤ lb := hX0.trans hlb
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (integral_nonneg fun h => by positivity)
  have hB0 : 0 ≤ B := by positivity
  have hNp0 : 0 ≤ Np := by positivity
  have hb1 : ‖isoTerm D N θ μ Λ z u v p 1 + Q‖ ≤ K₁ * S + K₁ * B := by
    have h1 := hK₁ N θ μ hμ hθ0 hθ1 Λ hΛ hΛn z hzN hzn u v hu hv Γ Υ lb ε₀ hΓ1 hΓN hΥ1 hΥ2 hlb
      hbad
    have h2 : X * lb * ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) ∂μ ≤
        S := by
      have hI : 0 ≤ ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) ∂μ :=
        integral_nonneg fun h => by positivity
      refine le_trans (mul_le_mul_of_nonneg_right (FI_two_thirds hX0 hlb) hI) ?_
      refine Finset.single_le_sum (f := fun n : ℕ => (X * lb ^ 2) ^ ((n : ℝ) / 3) *
        ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - n) ∂μ)
        (fun n _ => mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (integral_nonneg fun h => by positivity)) (Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩)
    calc ‖isoTerm D N θ μ Λ z u v p 1 + Q‖ ≤ K₁ * X * lb *
          ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) ∂μ +
            K₁ * (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ := h1
      _ = K₁ * X * lb *
          ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - 2) ∂μ + K₁ * B := by
          rw [hB]
          ring
      _ ≤ K₁ * S + K₁ * B := by
          have := mul_le_mul_of_nonneg_left h2 hK₁0
          linarith [show K₁ * X * lb * ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^
            (2 * p - 2) ∂μ = K₁ * (X * lb * ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ
              v)‖ ^ (2 * p - 2) ∂μ) by ring]
  have hbk : ∀ k ∈ Finset.Ico 2 (l + 1), ‖isoTerm D N θ μ Λ z u v p k‖ ≤ Kh k * S + Kh k * B := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    have hk' : 2 ≤ k ∧ k ≤ 16 * p + 16 := ⟨hk1, by omega⟩
    have e : Kh k = (iso_order_high' D p k hp hk'.1 hk'.2 C).choose := by
      simp only [hKhdef, hk', and_self, ↓reduceDIte]
    rw [e, hB, ← mul_assoc]
    exact (iso_order_high' D p k hp hk'.1 hk'.2 C).choose_spec.2 N θ μ hμ hθ0 hθ1 Λ hΛ hΛn z
      hzN hzn u v hu hv Γ Υ lb ε₀ hΓ1 hΓN hΥ1 hΥ2 hlb hbad
  have hbE : ‖Err‖ ≤ Ke * cR * (Np + B) := by
    set R : ℝ := Ke * ((((D : ℝ) + 3) * (1 + ‖z‖)) ^ (2 * p) *
      ((N : ℝ) ^ (-(((16 * p + 16 : ℕ) : ℝ) + 2) / 2) *
          (6 * Γ) ^ (4 * p - 1 + (16 * p + 16) + 1) +
        (1 + z.im⁻¹) ^ (4 * p - 1 + (16 * p + 16) + 1) *
          Real.sqrt (max ε₀ 0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^
            (-((128 * p + 114 : ℕ) : ℝ))))) with hR
    have hui : ∀ i, ‖starRingEnd ℂ (u i)‖ ≤ 1 := by
      intro i
      rw [Complex.norm_conj]
      have : ‖u i‖ ^ 2 ≤ 1 := le_trans (Finset.single_le_sum (f := fun k => ‖u k‖ ^ 2)
        (fun k _ => by positivity) (Finset.mem_univ i)) hu
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
    have hR0 : 0 ≤ R := by
      have hΓ0 : 0 ≤ 6 * Γ := by linarith
      have : 0 ≤ (1 + z.im⁻¹) := by positivity
      have : 0 ≤ ((D : ℝ) + 3) * (1 + ‖z‖) := by positivity
      positivity
    have hEi : ∀ i j, ‖starRingEnd ℂ (u i) * ((∫ h, h i j * FI_F D N θ Λ z u v p j h ∂μ) -
        ∑ k ∈ Finset.range (l + 1), FI_T D N θ μ Λ z u v p i j k)‖ ≤ R := by
      intro i j
      rw [norm_mul]
      have := hKe N θ μ hμ hθ0 hθ1 Λ hΛ hΛn z hz u v hu hv Γ Υ lb ε₀ hΓ1 hbad i j
      calc ‖starRingEnd ℂ (u i)‖ * ‖(∫ h, h i j * FI_F D N θ Λ z u v p j h ∂μ) -
            ∑ k ∈ Finset.range (l + 1), FI_T D N θ μ Λ z u v p i j k‖ ≤ 1 * R :=
            mul_le_mul (hui i) this (norm_nonneg _) zero_le_one
        _ = R := one_mul R
    have hsum : ‖Err‖ ≤ ((D : ℝ) * N) ^ 2 * R := by
      rw [hErr]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ => hEi i j)).trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      ring
    have hc := hcR N Γ z.im ‖z‖ ((((D : ℝ) + 3) * (1 + ‖z‖)) ^ (2 * p)) ε₀ (16 * p + 16)
      (4 * p - 1) (128 * p + 114) rfl rfl rfl hΓ1 hΓN (norm_nonneg z) hzn hzN
      (by positivity) le_rfl
    calc ‖Err‖ ≤ ((D : ℝ) * N) ^ 2 * R := hsum
      _ = Ke * (((D : ℝ) * N) ^ 2 * ((((D : ℝ) + 3) * (1 + ‖z‖)) ^ (2 * p) *
          ((N : ℝ) ^ (-(((16 * p + 16 : ℕ) : ℝ) + 2) / 2) *
              (6 * Γ) ^ (4 * p - 1 + (16 * p + 16) + 1) +
            (1 + z.im⁻¹) ^ (4 * p - 1 + (16 * p + 16) + 1) *
              Real.sqrt (max ε₀ 0 + ((N : ℝ) ^ ((1 : ℝ) / 2) * (24 * Γ)⁻¹) ^
                (-((128 * p + 114 : ℕ) : ℝ)))))) := by rw [hR]; ring
      _ ≤ Ke * (cR * (Np + B)) := mul_le_mul_of_nonneg_left hc hKe0
      _ = Ke * cR * (Np + B) := by ring
  -- step 5: assembly
  have hE0 : 0 ≤ ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p) ∂μ :=
    integral_nonneg fun h => by positivity
  have hsumk : ∑ k ∈ Finset.Ico 2 (l + 1), ‖isoTerm D N θ μ Λ z u v p k‖ ≤ Ks * S + Ks * B := by
    refine (Finset.sum_le_sum hbk).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have hmain : ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p) ∂μ ≤
      Ke * cR * (Np + B) + (K₁ * S + K₁ * B) + (Ks * S + Ks * B) := by
    have hn : ‖((∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p) ∂μ : ℝ) :
        ℂ)‖ = ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p) ∂μ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hE0]
    rw [← hn, hdecomp]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hbE hb1))
      ((norm_sum_le _ _).trans hsumk))
  have hKeR : 0 ≤ Ke * cR := mul_nonneg hKe0 hcR0
  nlinarith [mul_nonneg hKeR hS0, mul_nonneg hK₁0 hNp0, mul_nonneg hKs0 hNp0]

/-! ### One round at a single `N` -/

/-- `y^{m-n} ≤ a^{m-n} + a^{-n} y^m` for `y ≥ 0`, `a > 0`, `n ≤ m`. -/
private lemma FI_split_pow {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) {n m : ℕ} (hnm : n ≤ m) :
    y ^ (m - n) ≤ a ^ (m - n) + (a ^ n)⁻¹ * y ^ m := by
  rcases le_or_gt y a with h | h
  · have h1 : y ^ (m - n) ≤ a ^ (m - n) := pow_le_pow_left₀ hy h _
    have h2 : 0 ≤ (a ^ n)⁻¹ * y ^ m := by positivity
    linarith
  · have han : 0 < a ^ n := pow_pos ha n
    have h1 : a ^ n ≤ y ^ n := pow_le_pow_left₀ ha.le h.le n
    have h2 : y ^ (m - n) * a ^ n ≤ y ^ m := by
      calc y ^ (m - n) * a ^ n ≤ y ^ (m - n) * y ^ n := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = y ^ m := by rw [← pow_add, Nat.sub_add_cancel hnm]
    have h3 : y ^ (m - n) ≤ (a ^ n)⁻¹ * y ^ m := by
      rw [le_inv_mul_iff₀ han, mul_comm]
      exact h2
    have h4 : 0 ≤ a ^ (m - n) := by positivity
    linarith

/-- Young's inequality without Hölder: if `E ≤ K Σ_{n=1}^{2p} X^{n/3} E_n + R` and
`E_n ≤ a^{2p-n} + a^{-n} E` for every `a > 0`, then `E ≤ 4p K c^{2p} X^{2p/3} + 2R` with
`c = 4p max(K, 1)`. -/
private lemma FI_young (p : ℕ) (hp : 1 ≤ p) (K X E R : ℝ) (Ef : ℕ → ℝ) (hK : 0 ≤ K)
    (hX : 0 < X) (hE0 : 0 ≤ E)
    (hE : E ≤ K * (∑ n ∈ Finset.Icc 1 (2 * p), X ^ ((n : ℝ) / 3) * Ef n) + R)
    (hEf : ∀ a : ℝ, 0 < a → ∀ n ∈ Finset.Icc 1 (2 * p), Ef n ≤ a ^ (2 * p - n) + (a ^ n)⁻¹ * E) :
    E ≤ 4 * p * K * (4 * p * max K 1) ^ (2 * p) * X ^ ((2 * (p : ℝ)) / 3) + 2 * R := by
  set c : ℝ := 4 * p * max K 1 with hc
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hc1 : 1 ≤ c := by
    have : 1 ≤ max K 1 := le_max_right _ _
    nlinarith
  have hc0 : 0 < c := by linarith
  set b : ℝ := X ^ ((1 : ℝ) / 3) with hb
  have hb0 : 0 < b := Real.rpow_pos_of_pos hX _
  have hXb : ∀ n : ℕ, X ^ ((n : ℝ) / 3) = b ^ n := by
    intro n
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    congr 1
    ring
  have hterm : ∀ n ∈ Finset.Icc 1 (2 * p), X ^ ((n : ℝ) / 3) * Ef n ≤
      c ^ (2 * p) * b ^ (2 * p) + c⁻¹ * E := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have h1 := hEf (c * b) (by positivity) n hn
    rw [hXb n]
    have e1 : b ^ n * (c * b) ^ (2 * p - n) = c ^ (2 * p - n) * b ^ (2 * p) := by
      rw [mul_pow, ← mul_assoc, mul_comm (b ^ n), mul_assoc, ← pow_add, Nat.add_sub_cancel' hn2]
    have e2 : b ^ n * ((c * b) ^ n)⁻¹ = (c ^ n)⁻¹ := by
      rw [mul_pow]
      field_simp
    have h2 : c ^ (2 * p - n) ≤ c ^ (2 * p) := pow_le_pow_right₀ hc1 (Nat.sub_le _ _)
    have h3 : (c ^ n)⁻¹ ≤ c⁻¹ := by
      apply inv_anti₀ hc0
      calc c = c ^ 1 := (pow_one c).symm
        _ ≤ c ^ n := pow_le_pow_right₀ hc1 hn1
    calc b ^ n * Ef n ≤ b ^ n * ((c * b) ^ (2 * p - n) + ((c * b) ^ n)⁻¹ * E) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = c ^ (2 * p - n) * b ^ (2 * p) + (c ^ n)⁻¹ * E := by rw [mul_add, e1, ← mul_assoc, e2]
      _ ≤ c ^ (2 * p) * b ^ (2 * p) + c⁻¹ * E := by
          gcongr
  have hsum : ∑ n ∈ Finset.Icc 1 (2 * p), X ^ ((n : ℝ) / 3) * Ef n ≤
      (2 * p) * (c ^ (2 * p) * b ^ (2 * p) + c⁻¹ * E) := by
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    push_cast
    ring_nf
  have hKc : K * (2 * p) * c⁻¹ ≤ 1 / 2 := by
    rw [hc, mul_inv, mul_inv]
    have hm : K ≤ max K 1 := le_max_left _ _
    have hm0 : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : K * (max K 1)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hm0]
      exact hm
    have hp0 : (0 : ℝ) < p := by linarith
    calc K * (2 * p) * ((4 : ℝ)⁻¹ * (p : ℝ)⁻¹ * (max K 1)⁻¹) =
        (1 / 2) * (K * (max K 1)⁻¹) := by field_simp; ring
      _ ≤ 1 / 2 * 1 := by gcongr
      _ = 1 / 2 := by ring
  have hb2 : b ^ (2 * p) = X ^ ((2 * (p : ℝ)) / 3) := by
    rw [← hXb (2 * p)]
    push_cast
    ring_nf
  have key : E ≤ K * ((2 * p) * (c ^ (2 * p) * b ^ (2 * p))) + (K * (2 * p) * c⁻¹) * E + R := by
    have := mul_le_mul_of_nonneg_left hsum hK
    nlinarith
  have hKcE : (K * (2 * p) * c⁻¹) * E ≤ 1 / 2 * E := mul_le_mul_of_nonneg_right hKc hE0
  rw [← hb2]
  nlinarith

/-- The moments `‖(H̲G)_{uv}‖^q` are integrable for a law of Hermitian arrays. -/
private lemma FI_pow_int {D N : ℕ} (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    [IsFiniteMeasure μ] (hherm : ∀ᵐ h ∂μ, (Matrix.of h).IsHermitian)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (u v : Idx D N → ℂ) (q : ℕ) :
    Integrable (fun h => ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ q) μ := by
  refine (FI_int μ hherm Λ hΛ z hz (fun M => ‖FI_d D N θ Λ z u M v‖ ^ q)
    (by unfold FI_d FI_hg; fun_prop)).congr ?_
  filter_upwards [hherm] with h hh
  simp only [FI_d_eq D N θ Λ hΛ z hz h hh]

/-- One round of the self-improvement for `(H̲G)_{uv}` at a single `N`, with explicit exponents:
under the hypotheses of `iso_moment_ineq`, Markov's inequality and Young's inequality give, for
every `s > 0`,
`P(|(H̲G)_{uv}| > s) ≤ K s^{-2p} ((ζ̂ λ²)^{2p/3} + N^{-p-1} + N^{21p+18} ε₀^{1/2})`. -/
theorem iso_round (D p : ℕ) (hp : 1 ≤ p) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ)),
      LLClass D N C θ μ → 0 ≤ θ → θ ≤ 1 →
      ∀ Λ : Matrix (Idx D N) (Idx D N) ℂ, Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
      ∀ z : ℂ, ((N : ℝ))⁻¹ ≤ z.im → ‖z‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 9) →
      ∀ u v : Idx D N → ℂ, ∑ k, ‖u k‖ ^ 2 ≤ 1 → ∑ k, ‖v k‖ ^ 2 ≤ 1 →
      ∀ Γ Υ lb ε₀ : ℝ, 1 ≤ Γ → Γ ≤ (N : ℝ) ^ ((1 : ℝ) / 6) → z.im ≤ Υ →
        Υ ≤ (N : ℝ) * z.im →
        (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) ≤ lb →
        μ (isoGood D N θ Λ z u v Γ Υ lb)ᶜ ≤ ENNReal.ofReal ε₀ →
        ∀ s : ℝ, 0 < s →
          μ {h | s < ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖} ≤
            ENNReal.ofReal (K * (s ^ (2 * p))⁻¹ *
              (((Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) *
                  lb ^ 2) ^ ((2 * (p : ℝ)) / 3) +
                (N : ℝ) ^ (-((p : ℝ) + 1)) +
                (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀)) := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := iso_moment_ineq D p hp C
  refine ⟨4 * p * K₀ * (4 * p * max K₀ 1) ^ (2 * p) + 2 * K₀, by positivity, ?_⟩
  intro N θ μ hμ hθ0 hθ1 Λ hΛ hΛn z hzN hzn u v hu hv Γ Υ lb ε₀ hΓ1 hΓN hΥ1 hΥ2 hlb hbad s hs
  have hprob := hμ.prob
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      have : ((0 : ℕ) : ℝ) ^ ((1 : ℝ) / 6) = 0 := by
        rw [Nat.cast_zero]
        exact Real.zero_rpow (by norm_num)
      linarith
    · exact h0
  have hz : 0 < z.im := lt_of_lt_of_le (by positivity) hzN
  have hmom := hK₀ N θ μ hμ hθ0 hθ1 Λ hΛ hΛn z hzN hzn u v hu hv Γ Υ lb ε₀ hΓ1 hΓN hΥ1 hΥ2 hlb hbad
  set X : ℝ := (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / ((N : ℝ) * z.im)) with hX
  set E : ℝ := ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p) ∂μ with hE
  set R : ℝ := (N : ℝ) ^ (-((p : ℝ) + 1)) + (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ with hR
  have hX0 : 0 < X := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : 0 < Υ / ((N : ℝ) * z.im) := div_pos (by linarith) (by positivity)
    have h2 : 0 < Γ ^ 3 := pow_pos (by linarith) 3
    have h3 : 0 < 1 + ‖z‖ := by positivity
    have h4 : 0 < Real.sqrt D + 3 := by positivity
    have h5 := Real.sqrt_pos.mpr h1
    positivity
  have hlb0 : 0 < lb := lt_of_lt_of_le hX0 hlb
  have hXl : 0 < X * lb ^ 2 := by positivity
  have hint := FI_pow_int θ μ hμ.herm Λ hΛ z hz u v (2 * p)
  have hE0 : 0 ≤ E := integral_nonneg fun h => by positivity
  have hEb : E ≤ 4 * p * K₀ * (4 * p * max K₀ 1) ^ (2 * p) * (X * lb ^ 2) ^ ((2 * (p : ℝ)) / 3) +
      2 * (K₀ * R) := by
    refine FI_young p hp K₀ (X * lb ^ 2) E (K₀ * R) (fun n =>
      ∫ h, ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - n) ∂μ) hK₀0 hXl hE0 hmom
      ?_
    intro a ha n hn
    have hn2 : n ≤ 2 * p := (Finset.mem_Icc.mp hn).2
    have hI := integral_mono_of_nonneg (μ := μ)
      (f := fun h => ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p - n))
      (Eventually.of_forall fun h => by positivity)
      ((integrable_const (a ^ (2 * p - n))).add (hint.const_mul (a ^ n)⁻¹))
      (Eventually.of_forall fun h => FI_split_pow (norm_nonneg _) ha hn2)
    simp only [Pi.add_apply] at hI
    rw [integral_add (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul,
      probReal_univ, one_smul] at hI
    exact hI
  -- Markov's inequality
  have hs2 : 0 < s ^ (2 * p) := pow_pos hs _
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun h => by positivity) hint
    (s ^ (2 * p))
  have hsub : {h : Idx D N → Idx D N → ℂ |
      s < ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖} ⊆
      {h | s ^ (2 * p) ≤ ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^ (2 * p)} :=
    fun h hh => pow_le_pow_left₀ hs.le (le_of_lt hh) _
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : μ.real {h | s ^ (2 * p) ≤ ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ v)‖ ^
      (2 * p)} ≤ (s ^ (2 * p))⁻¹ * E := by
    rw [le_inv_mul_iff₀ hs2]
    exact hmk
  refine h1.trans ?_
  have hR0 : 0 ≤ R := by positivity
  have hXp : 0 ≤ (X * lb ^ 2) ^ ((2 * (p : ℝ)) / 3) := Real.rpow_nonneg hXl.le _
  have hc0 : 0 ≤ 4 * p * K₀ * (4 * p * max K₀ 1) ^ (2 * p) := by positivity
  have h2 : E ≤ (4 * p * K₀ * (4 * p * max K₀ 1) ^ (2 * p) + 2 * K₀) *
      ((X * lb ^ 2) ^ ((2 * (p : ℝ)) / 3) + (N : ℝ) ^ (-((p : ℝ) + 1)) +
        (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀) := by
    have e : (X * lb ^ 2) ^ ((2 * (p : ℝ)) / 3) + (N : ℝ) ^ (-((p : ℝ) + 1)) +
        (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀ = (X * lb ^ 2) ^ ((2 * (p : ℝ)) / 3) + R := by
      rw [hR]
      ring
    rw [e]
    nlinarith [mul_nonneg hK₀0 hXp, mul_nonneg hc0 hR0]
  calc (s ^ (2 * p))⁻¹ * E ≤ (s ^ (2 * p))⁻¹ * ((4 * p * K₀ * (4 * p * max K₀ 1) ^ (2 * p) +
        2 * K₀) * ((X * lb ^ 2) ^ ((2 * (p : ℝ)) / 3) + (N : ℝ) ^ (-((p : ℝ) + 1)) +
        (N : ℝ) ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-! ### The exponent count of one self-improving round -/

/-- The three terms of `iso_round` at `s = N^{τ'} w`, `w ≥ N^{-1/2}`, with `x = X^{1/3} ≤
c N^{4ε₁ + τ'/6} w`, `pτ' ≥ D' + 1` and `ε₀ ≤ N^{3 - D₁}`, `D₁ = 44p + 41 + 2D'`, add up to
`≤ N^{-D'}` once `N ≥ K(c^{2p} + 2)` -/
private lemma FI_final (p : ℕ) (hp : 1 ≤ p) (n τ' D' K c ε₁ ε₀ w x : ℝ) (hn : 1 ≤ n)
    (hτ' : 0 < τ') (hD' : 0 < D') (hpτ : D' + 1 ≤ p * τ') (hε₁' : ε₁ ≤ τ' / 16)
    (hK : 0 ≤ K) (hc : 1 ≤ c) (hw : n ^ (-(1 / 2 : ℝ)) ≤ w) (hx0 : 0 ≤ x)
    (hx : x ≤ c * n ^ (4 * ε₁ + τ' / 6) * w)
    (hε : ε₀ ≤ n ^ (3 - (44 * (p : ℝ) + 41 + 2 * D'))) (hnK : K * (c ^ (2 * p) + 2) ≤ n) :
    K * ((n ^ τ' * w) ^ (2 * p))⁻¹ *
        (x ^ (2 * p) + n ^ (-((p : ℝ) + 1)) + n ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀) ≤
      n ^ (-D') := by
  have hn0 : 0 < n := by linarith
  have hw0 : 0 < w := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hw
  have hs0 : 0 < n ^ τ' * w := mul_pos (Real.rpow_pos_of_pos hn0 _) hw0
  have hS0 : 0 < (n ^ τ' * w) ^ (2 * p) := pow_pos hs0 _
  have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hrp : ∀ a : ℝ, ∀ m : ℕ, (n ^ a) ^ m = n ^ (a * m) := by
    intro a m
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
  set L : ℝ := n ^ (-(D' + 1)) with hL
  -- term 1
  have hT1 : ((n ^ τ' * w) ^ (2 * p))⁻¹ * x ^ (2 * p) ≤ c ^ (2 * p) * L := by
    have h1 : x ≤ c * n ^ (-(τ' / 2)) * (n ^ τ' * w) := by
      refine hx.trans ?_
      have : n ^ (4 * ε₁ + τ' / 6) ≤ n ^ (-(τ' / 2)) * n ^ τ' := by
        rw [← Real.rpow_add hn0]
        exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)
      have hc0 : 0 ≤ c := by linarith
      calc c * n ^ (4 * ε₁ + τ' / 6) * w ≤ c * (n ^ (-(τ' / 2)) * n ^ τ') * w := by gcongr
        _ = c * n ^ (-(τ' / 2)) * (n ^ τ' * w) := by ring
    have h2 : x ^ (2 * p) ≤ (c * n ^ (-(τ' / 2))) ^ (2 * p) * (n ^ τ' * w) ^ (2 * p) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hx0 h1 _
    have h3 : (n ^ (-(τ' / 2))) ^ (2 * p) ≤ L := by
      rw [hrp, hL]
      refine Real.rpow_le_rpow_of_exponent_le hn ?_
      push_cast
      nlinarith
    calc ((n ^ τ' * w) ^ (2 * p))⁻¹ * x ^ (2 * p)
        ≤ ((n ^ τ' * w) ^ (2 * p))⁻¹ *
          ((c * n ^ (-(τ' / 2))) ^ (2 * p) * (n ^ τ' * w) ^ (2 * p)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = c ^ (2 * p) * (n ^ (-(τ' / 2))) ^ (2 * p) := by
          rw [mul_pow]
          field_simp
          ring
      _ ≤ c ^ (2 * p) * L := mul_le_mul_of_nonneg_left h3 (by positivity)
  -- the lower bound on `s`
  have hsl : ((n ^ τ' * w) ^ (2 * p))⁻¹ ≤ n ^ ((p : ℝ) - 2 * p * τ') := by
    have h1 : n ^ (τ' - 1 / 2) ≤ n ^ τ' * w := by
      rw [sub_eq_add_neg, Real.rpow_add hn0]
      exact mul_le_mul_of_nonneg_left hw (by positivity)
    have h2 : (n ^ (τ' - 1 / 2)) ^ (2 * p) ≤ (n ^ τ' * w) ^ (2 * p) :=
      pow_le_pow_left₀ (by positivity) h1 _
    rw [hrp] at h2
    calc ((n ^ τ' * w) ^ (2 * p))⁻¹ ≤ (n ^ ((τ' - 1 / 2) * ((2 * p : ℕ) : ℝ)))⁻¹ :=
          inv_anti₀ (by positivity) h2
      _ = n ^ ((p : ℝ) - 2 * p * τ') := by
          rw [← Real.rpow_neg hn0.le]
          congr 1
          push_cast
          ring
  -- term 2
  have hT2 : ((n ^ τ' * w) ^ (2 * p))⁻¹ * n ^ (-((p : ℝ) + 1)) ≤ L := by
    calc ((n ^ τ' * w) ^ (2 * p))⁻¹ * n ^ (-((p : ℝ) + 1))
        ≤ n ^ ((p : ℝ) - 2 * p * τ') * n ^ (-((p : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hsl (by positivity)
      _ = n ^ ((p : ℝ) - 2 * p * τ' + -((p : ℝ) + 1)) := (Real.rpow_add hn0 _ _).symm
      _ ≤ L := Real.rpow_le_rpow_of_exponent_le hn (by nlinarith)
  -- term 3
  have hsq : Real.sqrt ε₀ ≤ n ^ ((3 - (44 * (p : ℝ) + 41 + 2 * D')) / 2) := by
    calc Real.sqrt ε₀ ≤ Real.sqrt (n ^ (3 - (44 * (p : ℝ) + 41 + 2 * D'))) := Real.sqrt_le_sqrt hε
      _ = n ^ ((3 - (44 * (p : ℝ) + 41 + 2 * D')) / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
          ring_nf
  have hT3 : ((n ^ τ' * w) ^ (2 * p))⁻¹ * (n ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀) ≤ L := by
    calc ((n ^ τ' * w) ^ (2 * p))⁻¹ * (n ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀)
        ≤ n ^ ((p : ℝ) - 2 * p * τ') * (n ^ (21 * (p : ℝ) + 18) *
            n ^ ((3 - (44 * (p : ℝ) + 41 + 2 * D')) / 2)) :=
          mul_le_mul hsl (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)
            (by positivity)
      _ = n ^ ((p : ℝ) - 2 * p * τ' + ((21 * (p : ℝ) + 18) +
            (3 - (44 * (p : ℝ) + 41 + 2 * D')) / 2)) := by
          rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      _ ≤ L := Real.rpow_le_rpow_of_exponent_le hn (by nlinarith)
  have hL0 : 0 ≤ L := by positivity
  have hsum : ((n ^ τ' * w) ^ (2 * p))⁻¹ *
      (x ^ (2 * p) + n ^ (-((p : ℝ) + 1)) + n ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀) ≤
      (c ^ (2 * p) + 2) * L := by
    rw [mul_add, mul_add]
    nlinarith
  have hLn : n * L = n ^ (-D') := by
    rw [hL, ← Real.rpow_one_add' hn0.le (by linarith)]
    congr 1
    ring
  calc K * ((n ^ τ' * w) ^ (2 * p))⁻¹ *
        (x ^ (2 * p) + n ^ (-((p : ℝ) + 1)) + n ^ (21 * (p : ℝ) + 18) * Real.sqrt ε₀)
      ≤ K * ((c ^ (2 * p) + 2) * L) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hsum hK
    _ = K * (c ^ (2 * p) + 2) * L := by ring
    _ ≤ n * L := mul_le_mul_of_nonneg_right hnK hL0
    _ = n ^ (-D') := hLn

/-! ### Helpers for the self-improving step -/

section FI_Lam

open scoped Matrix.Norms.L2Operator

/-- The embedding of `ℂ^N` as the block `a` of `Idx D N`. -/
private def FI_J (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Fin N) ℂ :=
  Matrix.of fun p i => if p = (a, i) then 1 else 0

private lemma FI_J_conj_mul (D N : ℕ) (a : Fin D) : (FI_J D N a)ᴴ * FI_J D N a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, FI_J, Matrix.of_apply,
    Matrix.one_apply]
  have : ∀ p : Idx D N, star (if p = (a, i) then (1 : ℂ) else 0) * (if p = (a, j) then 1 else 0) =
      if p = (a, i) then (if i = j then 1 else 0) else 0 := by
    intro p
    by_cases h : p = (a, i)
    · subst h
      by_cases hij : i = j <;> simp [hij]
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma FI_J_norm (D N : ℕ) (hN : 1 ≤ N) (a : Fin D) : ‖FI_J D N a‖ ≤ 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (FI_J D N a)
  rw [FI_J_conj_mul, norm_one] at h1
  have h0 : 0 ≤ ‖FI_J D N a‖ := norm_nonneg _
  nlinarith

private lemma FI_block_norm (D N : ℕ) (hN : 1 ≤ N) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖FI_J D N a * M * (FI_J D N b)ᴴ‖ ≤ ‖M‖ := by
  have ha := FI_J_norm D N hN a
  have hb := FI_J_norm D N hN b
  calc ‖FI_J D N a * M * (FI_J D N b)ᴴ‖
      ≤ ‖FI_J D N a * M‖ * ‖(FI_J D N b)ᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖FI_J D N a‖ * ‖M‖) * ‖(FI_J D N b)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
    _ = ‖M‖ := by ring

private lemma FI_block_apply (D N : ℕ) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ)
    (p q : Idx D N) :
    (FI_J D N a * M * (FI_J D N b)ᴴ) p q = if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = a <;> by_cases h2 : q1 = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, FI_J, Prod.ext_iff, h1, h2]

private lemma FI_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = ∑ a : Fin D, ∑ b : Fin D,
      ((if fwd D a b then FI_J D N a * A * (FI_J D N b)ᴴ else 0) +
        (if fwd D b a then FI_J D N a * Aᴴ * (FI_J D N b)ᴴ else 0)) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.add_apply]
  have e1 : ∀ a b : Fin D,
      (if fwd D a b then FI_J D N a * A * (FI_J D N b)ᴴ else 0) p q =
      if fwd D a b ∧ p.1 = a ∧ q.1 = b then A p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D a b <;> simp [h, FI_block_apply]
  have e2 : ∀ a b : Fin D,
      (if fwd D b a then FI_J D N a * Aᴴ * (FI_J D N b)ᴴ else 0) p q =
      if fwd D b a ∧ p.1 = a ∧ q.1 = b then Aᴴ p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D b a <;> simp [h, FI_block_apply]
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
private lemma FI_opNorm_lam (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := by
  change ‖lam D N A‖ ≤ 2 * (D : ℝ) ^ 2 * ‖A‖
  rw [FI_lam_eq]
  have hb : ∀ a b : Fin D,
      ‖(if fwd D a b then FI_J D N a * A * (FI_J D N b)ᴴ else 0) +
      (if fwd D b a then FI_J D N a * Aᴴ * (FI_J D N b)ᴴ else 0)‖ ≤ 2 * ‖A‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D a b then FI_J D N a * A * (FI_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact FI_block_norm D N hN a b A
      · simp
    have h2 : ‖(if fwd D b a then FI_J D N a * Aᴴ * (FI_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact (FI_block_norm D N hN a b Aᴴ).trans (by rw [Matrix.l2_opNorm_conjTranspose])
      · simp
    linarith
  calc ‖∑ a : Fin D, ∑ b : Fin D, _‖ ≤ ∑ a : Fin D, ‖∑ b : Fin D, _‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin D, ∑ b : Fin D, 2 * ‖A‖ := by
        refine Finset.sum_le_sum fun a _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb a b)
    _ = 2 * (D : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end FI_Lam

/-- Along a sequence of members, `‖Λ_N‖ ≤ 1/10` for `N ≥ 1` large. -/
private lemma FI_lam_small (D : ℕ) (δA : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hseq : LLSeq D δA C θ μ A) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N → opNorm (lam D N (A N)) ≤ 1 / 10 := by
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → 2 * (D : ℝ) ^ 2 * (N : ℝ) ^ (-δA) ≤ 1 / 10 := by
    have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (-δA)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hseq.pos).comp tendsto_natCast_atTop_atTop
    have h2 := ht.const_mul (2 * (D : ℝ) ^ 2)
    rw [mul_zero] at h2
    exact eventually_atTop.mp
      ((h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10))).mono fun N h => h.le)
  exact ⟨N₂, fun N hN hN1 => (FI_opNorm_lam D N hN1 (A N)).trans
    ((mul_le_mul_of_nonneg_left (hseq.small N) (by positivity)).trans (hN₂ N hN))⟩

/-- `N^a ≥ c` for all large `N`, when `a > 0`. -/
private lemma FI_rpow_ge {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c ≤ (N : ℝ) ^ a :=
  eventually_atTop.mp
    (((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c)

/-- `0 < Im m < 1` for `‖Λ‖ ≤ 1/10` and `Im z > 0`. -/
private lemma FI_mExt {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) :
    0 < (mExt Λ z).im ∧ (mExt Λ z).im < 1 := by
  have he : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  rw [he]
  exact ⟨(mSol_spec Λ hΛ z hz).1,
    lt_of_le_of_lt (Complex.im_le_norm _) (mSol_apriori Λ hΛ hℓ z hz).2.1⟩

/-- `|isoVecs| ≤ 3 + D + 3DN`. -/
private lemma FI_card_V (D N : ℕ) (θ : ℝ) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (u v : Idx D N → ℂ) : (isoVecs D N θ Λ u v).card ≤ 3 + D + 3 * (D * N) := by
  unfold isoVecs
  have h1 : ({u, v, Λᴴ *ᵥ u} : Finset (Idx D N → ℂ)).card ≤ 3 := Finset.card_le_three
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin D)))
    (f := fun a => (Ea D N a)ᴴ *ᵥ u)
  have h3 := Finset.card_image_le (s := (Finset.univ : Finset (Idx D N)))
    (f := fun k => (Pi.single k 1 : Idx D N → ℂ))
  have h4 := Finset.card_image_le (s := (Finset.univ : Finset (Idx D N))) (f := tiltV D N θ u)
  have h5 := Finset.card_image_le (s := (Finset.univ : Finset (Idx D N)))
    (f := fun r => star (tiltV D N θ u r))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h2 h3 h4 h5
  refine (Finset.card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Finset.card_union_le _ _) _) _) _).trans ?_
  omega

/-- The set of second arguments of `isoGood` has at most `1 + 2DN` elements. -/
private lemma FI_card_Y (D N : ℕ) (θ : ℝ) (u v : Idx D N → ℂ) :
    (insert v (Finset.univ.image (fun k => (Pi.single k 1 : Idx D N → ℂ)) ∪
        Finset.univ.image (fun r => star (tiltV D N θ u r)))).card ≤ 1 + 2 * (D * N) := by
  have h3 := Finset.card_image_le (s := (Finset.univ : Finset (Idx D N)))
    (f := fun k => (Pi.single k 1 : Idx D N → ℂ))
  have h5 := Finset.card_image_le (s := (Finset.univ : Finset (Idx D N)))
    (f := fun r => star (tiltV D N θ u r))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h3 h5
  refine (Finset.card_insert_le _ _).trans ?_
  have := Finset.card_union_le (Finset.univ.image (fun k => (Pi.single k 1 : Idx D N → ℂ)))
    (Finset.univ.image (fun r => star (tiltV D N θ u r)))
  omega

/-- The bad event of `isoGood` is covered by the bad event of `goodSet` and the events
`|(H̲G)_{uy'}| > t` for the second arguments `y'`, when `t ≤ λ`. -/
private lemma FI_bad_le {D N : ℕ} (θ : ℝ) (μ : Measure (Idx D N → Idx D N → ℂ))
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (u v : Idx D N → ℂ) (Γ Υ lb t a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (htl : t ≤ lb)
    (hG : μ (goodSet Λ z (isoVecs D N θ Λ u v) Γ Υ)ᶜ ≤ ENNReal.ofReal a)
    (hY : ∀ y ∈ insert v (Finset.univ.image (fun k => (Pi.single k 1 : Idx D N → ℂ)) ∪
        Finset.univ.image (fun r => star (tiltV D N θ u r))),
      μ {h | t < ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ y)‖} ≤ ENNReal.ofReal b) :
    μ (isoGood D N θ Λ z u v Γ Υ lb)ᶜ ≤ ENNReal.ofReal (a +
      ((insert v (Finset.univ.image (fun k => (Pi.single k 1 : Idx D N → ℂ)) ∪
        Finset.univ.image (fun r => star (tiltV D N θ u r)))).card : ℝ) * b) := by
  set Y := insert v (Finset.univ.image (fun k => (Pi.single k 1 : Idx D N → ℂ)) ∪
        Finset.univ.image (fun r => star (tiltV D N θ u r))) with hYdef
  have hsub : (isoGood D N θ Λ z u v Γ Υ lb)ᶜ ⊆ (goodSet Λ z (isoVecs D N θ Λ u v) Γ Υ)ᶜ ∪
      ⋃ y ∈ Y, {h | t < ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ y)‖} := by
    intro h hh
    by_contra hc
    apply hh
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_iUnion,
      Set.mem_ofPred_eq, not_exists, not_lt] at hc
    exact ⟨hc.1, fun y hy => (hc.2 y hy).trans htl⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hU : μ (⋃ y ∈ Y, {h | t < ‖star u ⬝ᵥ (hgUnder D N θ (Matrix.of h) Λ z *ᵥ y)‖}) ≤
      ENNReal.ofReal ((Y.card : ℝ) * b) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun y hy => hY y hy).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_add ha (by positivity)]
  exact add_le_add hG hU

/-- `ζ̂ ≤ 4(√D + 3) E⁴ ζ_φ` for `Γ = 5/4 + Eφ`, `Υ = (41/16)η + (25/16) Im m + Eφ`, `E ≥ 1`:
`Γ ≤ (5/4) E (1 + φ)` and `Υ ≤ (41/16) E (Im m + φ + η)`. -/
private lemma FI_zhat_le (D : ℕ) (n η m φ E zn : ℝ) (hn0 : 0 < n) (hη : 0 < η) (hm0 : 0 ≤ m)
    (hφ0 : 0 ≤ φ) (hE1 : 1 ≤ E) (hzn : 0 ≤ zn) :
    (Real.sqrt D + 3) * (1 + zn) * (5 / 4 + E * φ) ^ 3 *
        Real.sqrt ((41 / 16 * η + 25 / 16 * m + E * φ) / (n * η)) ≤
      4 * (Real.sqrt D + 3) * E ^ 4 *
        ((1 + zn) * (1 + φ) ^ 3 * Real.sqrt ((m + φ + η) / (n * η))) := by
  have hNη : 0 < n * η := mul_pos hn0 hη
  have hE0 : 0 ≤ E := by linarith
  have hΓle : 5 / 4 + E * φ ≤ 5 / 4 * E * (1 + φ) := by
    have a1 : 0 ≤ E * φ := mul_nonneg hE0 hφ0
    have e : 5 / 4 * E * (1 + φ) = 5 / 4 * E + 5 / 4 * (E * φ) := by ring
    rw [e]
    linarith
  have hΓ0 : 0 ≤ 5 / 4 + E * φ := by have := mul_nonneg hE0 hφ0; linarith
  have hΥle : (41 / 16 * η + 25 / 16 * m + E * φ) / (n * η) ≤
      41 / 16 * E * ((m + φ + η) / (n * η)) := by
    rw [← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hNη.le
    have a1 : η ≤ E * η := le_mul_of_one_le_left hη.le hE1
    have a2 : m ≤ E * m := le_mul_of_one_le_left hm0 hE1
    have a3 : 0 ≤ E * φ := mul_nonneg hE0 hφ0
    have e : 41 / 16 * E * (m + φ + η) =
        41 / 16 * (E * η) + 41 / 16 * (E * m) + 41 / 16 * (E * φ) := by ring
    rw [e]
    linarith
  set Q := (m + φ + η) / (n * η) with hQ
  have hQ0 : 0 ≤ Q := div_nonneg (by linarith) hNη.le
  have hsq : Real.sqrt ((41 / 16 * η + 25 / 16 * m + E * φ) / (n * η)) ≤ 2 * E * Real.sqrt Q := by
    refine (Real.sqrt_le_sqrt hΥle).trans ?_
    rw [Real.sqrt_mul (mul_nonneg (by norm_num) hE0), Real.sqrt_mul (by norm_num)]
    have h1 : Real.sqrt (41 / 16) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have h2 : Real.sqrt E ≤ E := by
      rw [Real.sqrt_le_left hE0]
      nlinarith
    have h3 := Real.sqrt_nonneg Q
    have h4 := Real.sqrt_nonneg E
    have h5 := Real.sqrt_nonneg (41 / 16 : ℝ)
    gcongr
  have ha : 0 ≤ (Real.sqrt D + 3) * (1 + zn) :=
    mul_nonneg (by positivity) (by linarith)
  have hb : 0 ≤ 1 + φ := by linarith
  have hz1 : 0 ≤ 1 + zn := by linarith
  have hΓ3 : (5 / 4 + E * φ) ^ 3 ≤ (5 / 4 * E * (1 + φ)) ^ 3 := pow_le_pow_left₀ hΓ0 hΓle 3
  have hS0 := Real.sqrt_nonneg ((41 / 16 * η + 25 / 16 * m + E * φ) / (n * η))
  have hP0 : 0 ≤ (Real.sqrt D + 3) * E ^ 4 * ((1 + zn) * (1 + φ) ^ 3 * Real.sqrt Q) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hz1 (pow_nonneg hb 3))
      (Real.sqrt_nonneg _))
  have step1 : (Real.sqrt D + 3) * (1 + zn) * (5 / 4 + E * φ) ^ 3 *
      Real.sqrt ((41 / 16 * η + 25 / 16 * m + E * φ) / (n * η)) ≤
      (Real.sqrt D + 3) * (1 + zn) * (5 / 4 * E * (1 + φ)) ^ 3 * (2 * E * Real.sqrt Q) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hΓ3 ha) hsq hS0
      (mul_nonneg ha (pow_nonneg (by positivity) 3))
  have e2 : (Real.sqrt D + 3) * (1 + zn) * (5 / 4 * E * (1 + φ)) ^ 3 * (2 * E * Real.sqrt Q) =
      125 / 32 * ((Real.sqrt D + 3) * E ^ 4 * ((1 + zn) * (1 + φ) ^ 3 * Real.sqrt Q)) := by ring
  have e3 : 4 * (Real.sqrt D + 3) * E ^ 4 *
      ((1 + zn) * (1 + φ) ^ 3 * Real.sqrt ((m + φ + η) / (n * η))) =
      4 * ((Real.sqrt D + 3) * E ^ 4 * ((1 + zn) * (1 + φ) ^ 3 * Real.sqrt Q)) := by
    rw [hQ]
    ring
  rw [e3]
  linarith

/-- `Γ = 5/4 + N^{ε₁} φ ≤ N^{1/6}` for `ε₁ ≤ 1/144`, `δ₀ ≤ 1/9`, `φ ≤ N^{δ₀}` and
`N^{7/144} ≥ 9/4` -/
private lemma FI_gamma_le (n ε₁ δ₀ φ : ℝ) (hn1 : 1 ≤ n) (hε₁c : ε₁ ≤ 1 / 144)
    (hδ9 : δ₀ ≤ 1 / 9) (hφ2 : φ ≤ n ^ δ₀)
    (h4 : 9 / 4 ≤ n ^ ((7 : ℝ) / 144)) : 5 / 4 + n ^ ε₁ * φ ≤ n ^ ((1 : ℝ) / 6) := by
  have hn0 : 0 < n := by linarith
  have h1 : n ^ ε₁ * φ ≤ n ^ ((17 : ℝ) / 144) := by
    calc n ^ ε₁ * φ ≤ n ^ ε₁ * n ^ δ₀ := mul_le_mul_of_nonneg_left hφ2 (by positivity)
      _ = n ^ (ε₁ + δ₀) := (Real.rpow_add hn0 _ _).symm
      _ ≤ n ^ ((17 : ℝ) / 144) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have ha : 1 ≤ n ^ ((17 : ℝ) / 144) := Real.one_le_rpow hn1 (by norm_num)
  have e : n ^ ((1 : ℝ) / 6) = n ^ ((17 : ℝ) / 144) * n ^ ((7 : ℝ) / 144) := by
    rw [← Real.rpow_add hn0]
    norm_num
  rw [e]
  nlinarith

/-- `Υ = (41/16) η + (25/16) Im m + N^{ε₁} φ ≤ N η` for `Im m < 1`, `η ≥ N^{-1+τ}`, `N ≥ 6`,
`ε₁ ≤ τ/20`, `10 δ₀ ≤ τ` and `N^{17τ/20} ≥ 25/4` -/
private lemma FI_ups_le (n η m ε₁ δ₀ τ φ : ℝ) (hn6 : 6 ≤ n) (hτ : 0 < τ)
    (hη : n ^ (-1 + τ) ≤ η) (hm1 : m < 1) (hφ2 : φ ≤ n ^ δ₀)
    (hε₁b : ε₁ ≤ τ / 20) (hδ : 10 * δ₀ ≤ τ)
    (h5 : 25 / 4 ≤ n ^ (17 / 20 * τ)) :
    41 / 16 * η + 25 / 16 * m + n ^ ε₁ * φ ≤ n * η := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  set b := n ^ (3 / 20 * τ) with hb
  have hb1 : 1 ≤ b := Real.one_le_rpow hn1 (by positivity)
  have h1 : n ^ ε₁ * φ ≤ b := by
    calc n ^ ε₁ * φ ≤ n ^ ε₁ * n ^ δ₀ := mul_le_mul_of_nonneg_left hφ2 (by positivity)
      _ = n ^ (ε₁ + δ₀) := (Real.rpow_add hn0 _ _).symm
      _ ≤ b := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h2 : n ^ τ = b * n ^ (17 / 20 * τ) := by
    rw [hb, ← Real.rpow_add hn0]
    ring_nf
  have h3 : n ^ τ ≤ n * η := by
    calc n ^ τ = n * n ^ (-1 + τ) := by
          rw [← Real.rpow_one_add' hn0.le (by linarith)]
          ring_nf
      _ ≤ n * η := mul_le_mul_of_nonneg_left hη hn0.le
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hη
  have h6 : 41 / 16 * η ≤ n * η / 2 := by nlinarith
  have h7 : 25 / 4 * b ≤ n ^ τ := by rw [h2]; nlinarith
  linarith

/-- `|isoVecs|² + |Y| ≤ N³` for `N ≥ 52 D² + 6` -/
private lemma FI_card_cube (D N a b : ℕ) (hD : 1 ≤ D) (hN : 52 * D ^ 2 + 6 ≤ N)
    (ha : a ≤ 3 + D + 3 * (D * N)) (hb : b ≤ 1 + 2 * (D * N)) :
    (a : ℝ) ^ 2 + b ≤ (N : ℝ) ^ 3 := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hN' : 52 * (D : ℝ) ^ 2 + 6 ≤ N := by exact_mod_cast hN
  have ha' : (a : ℝ) ≤ 3 + D + 3 * (D * N) := by exact_mod_cast ha
  have hb' : (b : ℝ) ≤ 1 + 2 * (D * N) := by exact_mod_cast hb
  have hN1 : (1 : ℝ) ≤ N := by nlinarith
  have hdn : 1 ≤ (D : ℝ) * N := by nlinarith
  have ha7 : (a : ℝ) ≤ 7 * (D * N) := by nlinarith
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have h1 : (a : ℝ) ^ 2 ≤ 49 * ((D : ℝ) * N) ^ 2 := by nlinarith
  have h2 : (b : ℝ) ≤ 3 * ((D : ℝ) * N) ^ 2 := by nlinarith
  have h3 : 52 * ((D : ℝ) * N) ^ 2 ≤ (N : ℝ) ^ 3 := by
    have : 52 * ((D : ℝ) * N) ^ 2 = (52 * (D : ℝ) ^ 2) * (N : ℝ) ^ 2 := by ring
    rw [this, pow_succ (N : ℝ) 2, mul_comm ((N : ℝ) ^ 2)]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- `(ζ̂ λ²)^{1/3} ≤ c N^{4ε₁ + 2ε₂/3} (ζ lb²)^{1/3}` for `ζ̂ ≤ c N^{4ε₁} ζ` and
`λ = c N^{4ε₁} N^{ε₂} lb`. -/
private lemma FI_X_le (zh lr ζ lb c n e₁ e₂ : ℝ) (hn0 : 0 < n) (hc0 : 0 ≤ c) (hζ0 : 0 ≤ ζ)
    (hzh0 : 0 ≤ zh) (hzh : zh ≤ c * n ^ (4 * e₁) * ζ)
    (hlr : lr = c * n ^ (4 * e₁) * (n ^ e₂ * lb)) :
    (zh * lr ^ 2) ^ ((1 : ℝ) / 3) ≤
      c * n ^ (4 * e₁ + 2 * e₂ / 3) * (ζ * lb ^ 2) ^ ((1 : ℝ) / 3) := by
  have hthird : ∀ a : ℝ, 0 ≤ a → (a ^ 3) ^ ((1 : ℝ) / 3) = a := by
    intro a ha
    rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast ha (by norm_num)
  have h1 : zh * lr ^ 2 ≤ c ^ 3 * n ^ (12 * e₁ + 2 * e₂) * (ζ * lb ^ 2) := by
    have e : c ^ 3 * n ^ (12 * e₁ + 2 * e₂) * (ζ * lb ^ 2) =
        c * n ^ (4 * e₁) * ζ * lr ^ 2 := by
      rw [hlr, show 12 * e₁ + 2 * e₂ = 4 * e₁ + (4 * e₁ + e₂ + (4 * e₁ + e₂)) by ring,
        Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_add hn0]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hzh (sq_nonneg _)
  have h2 : (c ^ 3 * n ^ (12 * e₁ + 2 * e₂) * (ζ * lb ^ 2)) ^ ((1 : ℝ) / 3) =
      c * n ^ (4 * e₁ + 2 * e₂ / 3) * (ζ * lb ^ 2) ^ ((1 : ℝ) / 3) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
      (by positivity), hthird c hc0, ← Real.rpow_mul hn0.le]
    congr 2
    ring_nf
  rw [← h2]
  exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)

set_option maxHeartbeats 1000000 in
/-- One self-improving step for `(H̲G)_{uy}`: under `LLSeq`, `10 δ₀ ≤ τ` and
`aprioriLL`, if `(H̲G)_{uy} ≺ λ` in sup form over `z ∈ Z_N`, unit `u` and `|y| ≤ 1` for a
deterministic `λ ≥ ζ_φ = (1 + |z|)(1 + φ)³((Im m + φ + η)/(Nη))^{1/2}`, then
`(H̲G)_{uy} ≺ (ζ_φ λ²)^{1/3}` (Definition 2.8 [stoch_domination]). -/
theorem iso_self_improv :
    ∀ (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
      (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ),
      LLSeq D δA C θ μ A → 0 < τ → 0 ≤ δ₀ → 10 * δ₀ ≤ τ →
    ∀ Z : ℕ → Set ℂ, (∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im) →
    ∀ φ : ℕ → ℂ → ℝ, (∀ N, ∀ z ∈ Z N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀) →
    aprioriLL D μ A Z φ →
    ∀ lb : ℕ → ℂ → ℝ, (∀ N, ∀ z ∈ Z N, (1 + ‖z‖) * (1 + φ N z) ^ 3 *
        Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im)) ≤ lb N z) →
    PrecS μ (U := fun N => {z // z ∈ Z N} × {u : Idx D N → ℂ // ∑ i, ‖u i‖ ^ 2 = 1} ×
        {y : Idx D N → ℂ // ∑ i, ‖y i‖ ^ 2 ≤ 1})
      (fun N w h => ‖star w.2.1.1 ⬝ᵥ
        (hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1 *ᵥ w.2.2.1)‖)
      (fun N w _ => lb N w.1.1) →
    PrecS μ (U := fun N => {z // z ∈ Z N} × {u : Idx D N → ℂ // ∑ i, ‖u i‖ ^ 2 = 1} ×
        {y : Idx D N → ℂ // ∑ i, ‖y i‖ ^ 2 ≤ 1})
      (fun N w h => ‖star w.2.1.1 ⬝ᵥ
        (hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1 *ᵥ w.2.2.1)‖)
      (fun N w _ => ((1 + ‖w.1.1‖) * (1 + φ N w.1.1) ^ 3 *
        Real.sqrt (((mExt (lam D N (A N)) w.1.1).im + φ N w.1.1 + w.1.1.im) /
          ((N : ℝ) * w.1.1.im)) * lb N w.1.1 ^ 2) ^ ((1 : ℝ) / 3)) := by
  intro D δA τ δ₀ C θ μ A hseq hτ hδ₀ hδτ Z hZ φ hφ hLL lb hlb hpre τ' hτ' D' hD'
  have hD1 := hseq.one_le_D
  -- the moment index `p` with `pτ' ≥ D' + 1`
  obtain ⟨p, hp1, hpτ⟩ : ∃ p : ℕ, 1 ≤ p ∧ D' + 1 ≤ (p : ℝ) * τ' := by
    refine ⟨⌈(D' + 1) / τ'⌉₊ + 1, by omega, ?_⟩
    have h1 : (D' + 1) / τ' ≤ ⌈(D' + 1) / τ'⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hτ'] at h1
    push_cast
    nlinarith
  obtain ⟨K, hK0, hK⟩ := iso_round D p hp1 C
  set ε₂ : ℝ := τ' / 4 with hε₂
  set ε₁ : ℝ := min (τ' / 16) (min (τ / 20) (1 / 144)) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hε₁a : ε₁ ≤ τ' / 16 := min_le_left _ _
  have hε₁b : ε₁ ≤ τ / 20 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₁c : ε₁ ≤ 1 / 144 := (min_le_right _ _).trans (min_le_right _ _)
  set D₁ : ℝ := 44 * (p : ℝ) + 41 + 2 * D' with hD₁
  have hD₁0 : 0 < D₁ := by positivity
  set c : ℝ := 4 * (Real.sqrt D + 3) with hc
  have hc1 : 1 ≤ c := by
    have := Real.sqrt_nonneg (D : ℝ)
    linarith
  -- the spectral sets without `N = 0`
  set Z' : ℕ → Set ℂ := fun N => if N = 0 then ∅ else Z N with hZ'def
  have hZ'pos : ∀ N, ∀ z ∈ Z' N, 0 < z.im := by
    intro N z hz
    by_cases hN0 : N = 0
    · simp [hZ'def, hN0] at hz
    · simp only [hZ'def, hN0, ite_false] at hz
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) (hZ N z hz).2
  have hLL' : aprioriLL D μ A Z' φ := by
    intro t ht E hE
    obtain ⟨N₀, hN₀⟩ := hLL t ht E hE
    refine ⟨N₀, fun N hN w => ?_⟩
    obtain ⟨⟨z, hz⟩, s, r⟩ := w
    by_cases hN0 : N = 0
    · simp [hZ'def, hN0] at hz
    · have hz' : z ∈ Z N := by simpa [hZ'def, hN0] using hz
      exact hN₀ N hN ⟨⟨z, hz'⟩, s, r⟩
  obtain ⟨N₁, hN₁⟩ := apriori_good D δA C θ μ A hseq Z' hZ'pos φ hLL' ε₁ D₁ hε₁0 hD₁0
  obtain ⟨N₂, hN₂⟩ := hpre ε₂ (by positivity) D₁ hD₁0
  obtain ⟨N₃, hN₃⟩ := FI_lam_small D δA C θ μ A hseq
  obtain ⟨N₄, hN₄⟩ := FI_rpow_ge (show (0 : ℝ) < 7 / 144 by norm_num) (9 / 4)
  obtain ⟨N₅, hN₅⟩ := FI_rpow_ge (show (0 : ℝ) < 17 / 20 * τ by positivity) (25 / 4)
  obtain ⟨N₆, hN₆⟩ : ∃ N₆ : ℕ, K * (c ^ (2 * p) + 2) ≤ N₆ := exists_nat_ge _
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (52 * D ^ 2 + 6)),
    fun N hN w => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hNN₁, hNN₂⟩, hNN₃, hNN₄⟩, ⟨hNN₅, hNN₆⟩, hNN₇⟩ := hN
  obtain ⟨⟨z, hzZ⟩, ⟨u, hu⟩, ⟨y, hy⟩⟩ := w
  change μ N {h | (N : ℝ) ^ τ' * ((1 + ‖z‖) * (1 + φ N z) ^ 3 *
      Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im)) *
        lb N z ^ 2) ^ ((1 : ℝ) / 3) <
      ‖star u ⬝ᵥ (hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z *ᵥ y)‖} ≤
    ENNReal.ofReal ((N : ℝ) ^ (-D'))
  -- the point
  have hN1 : 1 ≤ N := by omega
  have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
  set n : ℝ := (N : ℝ) with hn
  have hn1 : 1 ≤ n := Nat.one_le_cast.mpr hN1
  have hn0 : 0 < n := by linarith
  have hnD : 52 * (D : ℝ) ^ 2 + 6 ≤ n := by
    have : ((52 * D ^ 2 + 6 : ℕ) : ℝ) ≤ n := Nat.cast_le.mpr hNN₇
    push_cast at this
    exact this
  have hn6 : 6 ≤ n := by nlinarith [sq_nonneg (D : ℝ)]
  set Λ := lam D N (A N) with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N (A N)
  have hΛn : opNorm Λ ≤ 1 / 10 := hN₃ N hNN₃ hN1
  obtain ⟨hzn', hzim⟩ := hZ N z hzZ
  obtain ⟨hφ1, hφ2⟩ := hφ N z hzZ
  have hφ0 : 0 ≤ φ N z := le_trans (by positivity) hφ1
  have hη : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hzim
  have hηN : n⁻¹ ≤ z.im := by
    refine le_trans ?_ hzim
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  -- `δ₀ ≤ 1/9`
  have hδ9 : δ₀ ≤ 1 / 9 := by
    have h1 : n ^ (-1 + τ) ≤ n ^ δ₀ :=
      hzim.trans ((Complex.im_le_norm z).trans hzn')
    have h2 := (Real.rpow_le_rpow_left_iff (by linarith : (1 : ℝ) < n)).mp h1
    linarith
  have hzn : ‖z‖ ≤ n ^ ((1 : ℝ) / 9) :=
    hzn'.trans (Real.rpow_le_rpow_of_exponent_le hn1 hδ9)
  obtain ⟨hIm0, hIm1⟩ := FI_mExt Λ hΛ hΛn z hη
  set m : ℝ := (mExt Λ z).im with hm
  set E : ℝ := n ^ ε₁ with hE
  have hE1 : 1 ≤ E := Real.one_le_rpow hn1 hε₁0.le
  have hEφ : E * φ N z ≤ n ^ (ε₁ + δ₀) := by
    rw [Real.rpow_add hn0]
    exact mul_le_mul_of_nonneg_left hφ2 (by positivity)
  set Γ : ℝ := 5 / 4 + n ^ ε₁ * φ N z with hΓ
  set Υ : ℝ := 41 / 16 * z.im + 25 / 16 * m + n ^ ε₁ * φ N z with hΥ
  set ζ : ℝ := (1 + ‖z‖) * (1 + φ N z) ^ 3 * Real.sqrt ((m + φ N z + z.im) / (n * z.im))
    with hζ
  have hlbN : ζ ≤ lb N z := hlb N z hzZ
  have hNη : 0 < n * z.im := mul_pos hn0 hη
  -- `ζ ≥ N^{-1/2}`
  have hζl : n ^ (-(1 / 2 : ℝ)) ≤ ζ := by
    have h1 : n ^ (-(1 / 2 : ℝ)) = Real.sqrt (z.im / (n * z.im)) := by
      rw [show z.im / (n * z.im) = n⁻¹ by field_simp, Real.sqrt_inv, Real.sqrt_eq_rpow,
        Real.rpow_neg hn0.le]
    have h2 : Real.sqrt (z.im / (n * z.im)) ≤ Real.sqrt ((m + φ N z + z.im) / (n * z.im)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hNη.le)
    have h3 : 1 ≤ (1 + ‖z‖) * (1 + φ N z) ^ 3 := by
      have : 1 ≤ (1 + φ N z) ^ 3 := one_le_pow₀ (by linarith)
      have h4 : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
      nlinarith
    rw [h1, hζ]
    calc Real.sqrt (z.im / (n * z.im)) ≤ 1 * Real.sqrt ((m + φ N z + z.im) / (n * z.im)) := by
          linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
  have hζ0 : 0 < ζ := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hζl
  have hlb0 : 0 < lb N z := lt_of_lt_of_le hζ0 hlbN
  set Y : ℝ := ζ * lb N z ^ 2 with hY
  have hY0 : 0 < Y := by positivity
  set w : ℝ := Y ^ ((1 : ℝ) / 3) with hw
  have hthird : ∀ a : ℝ, 0 ≤ a → (a ^ 3) ^ ((1 : ℝ) / 3) = a := by
    intro a ha
    rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast ha (by norm_num)
  have hwl : n ^ (-(1 / 2 : ℝ)) ≤ w := by
    have h1 : (n ^ (-(1 / 2 : ℝ))) ^ 3 ≤ Y := by
      calc (n ^ (-(1 / 2 : ℝ))) ^ 3 ≤ ζ ^ 3 := pow_le_pow_left₀ (by positivity) hζl 3
        _ = ζ * ζ ^ 2 := by ring
        _ ≤ ζ * lb N z ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hζ0.le hlbN 2) hζ0.le
    calc n ^ (-(1 / 2 : ℝ)) = ((n ^ (-(1 / 2 : ℝ))) ^ 3) ^ ((1 : ℝ) / 3) :=
          (hthird _ (by positivity)).symm
      _ ≤ w := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  -- the round's `λ`
  set lr : ℝ := c * n ^ (4 * ε₁ + ε₂) * lb N z with hlr
  have hn4 : n ^ (4 * ε₁) = E ^ 4 := by
    rw [hE, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
    ring_nf
  have hζhat : (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / (n * z.im)) ≤
      c * n ^ (4 * ε₁) * ζ := by
    rw [hn4, hc]
    exact FI_zhat_le D n z.im m (φ N z) E ‖z‖ hn0 hη hIm0.le hφ0 hE1 (norm_nonneg z)
  have hε₂0 : 0 ≤ ε₂ := div_nonneg hτ'.le (by norm_num)
  have hε₂1 : 1 ≤ n ^ ε₂ := Real.one_le_rpow hn1 hε₂0
  have hc4 : 1 ≤ c * n ^ (4 * ε₁) :=
    one_le_mul_of_one_le_of_one_le hc1 (Real.one_le_rpow hn1 (by positivity))
  have hlr' : lr = c * n ^ (4 * ε₁) * (n ^ ε₂ * lb N z) := by
    rw [hlr, Real.rpow_add hn0]
    ring
  have hnlr : n ^ ε₂ * lb N z ≤ lr := by
    rw [hlr']
    exact le_mul_of_one_le_left (mul_nonneg (by positivity) hlb0.le) hc4
  have hzlr : (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / (n * z.im)) ≤ lr := by
    refine hζhat.trans ?_
    rw [hlr']
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ζ = 1 * ζ := (one_mul ζ).symm
      _ ≤ n ^ ε₂ * lb N z := mul_le_mul hε₂1 hlbN hζ0.le (by positivity)
  -- the remaining hypotheses of `iso_round`
  have hEφ0 : 0 ≤ n ^ ε₁ * φ N z := mul_nonneg (by positivity) hφ0
  have hΓ1 : 1 ≤ Γ := by
    rw [hΓ]
    linarith
  have hΓN : Γ ≤ n ^ ((1 : ℝ) / 6) :=
    FI_gamma_le n ε₁ δ₀ (φ N z) hn1 hε₁c hδ9 hφ2 (hN₄ N hNN₄)
  have hΥ1 : z.im ≤ Υ := by
    rw [hΥ]
    have : 0 ≤ 25 / 16 * m := by linarith
    linarith
  have hΥ2 : Υ ≤ n * z.im :=
    FI_ups_le n z.im m ε₁ δ₀ τ (φ N z) hn6 hτ hzim hIm1 hφ2 hε₁b hδτ (hN₅ N hNN₅)
  set V := isoVecs D N (θ N) Λ u y with hV
  have hVn : ∀ x ∈ V, ∑ k, ‖x k‖ ^ 2 ≤ 1 :=
    FI_V_norm D N (θ N) (hseq.theta N).1 (hseq.theta N).2 Λ hΛ (by linarith) u y hu.le hy
  have hz' : z ∈ Z' N := by
    simp only [hZ'def, show N ≠ 0 by omega, ite_false]
    exact hzZ
  have hG := hN₁ N hNN₁ z hz' V hVn
  set Yset := insert y (Finset.univ.image (fun k => (Pi.single k 1 : Idx D N → ℂ)) ∪
        Finset.univ.image (fun r => star (tiltV D N (θ N) u r))) with hYset
  have hYn : ∀ y' ∈ Yset, ∑ i, ‖y' i‖ ^ 2 ≤ 1 := by
    intro y' hy'
    simp only [hYset, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hy'
    rcases hy' with rfl | ⟨k, rfl⟩ | ⟨r, rfl⟩
    · exact hy
    · exact (FI_single_norm k).le
    · simpa using FI_tilt_norm D N (θ N) (hseq.theta N).1 (hseq.theta N).2 u hu.le r
  have hY : ∀ y' ∈ Yset, μ N {h | n ^ ε₂ * lb N z <
      ‖star u ⬝ᵥ (hgUnder D N (θ N) (Matrix.of h) Λ z *ᵥ y')‖} ≤
        ENNReal.ofReal (n ^ (-D₁)) :=
    fun y' hy' => hN₂ N hNN₂ ⟨⟨z, hzZ⟩, ⟨u, hu⟩, ⟨y', hYn y' hy'⟩⟩
  set ε₀ : ℝ := (V.card : ℝ) ^ 2 * n ^ (-D₁) + (Yset.card : ℝ) * n ^ (-D₁) with hε₀
  have hbad : μ N (isoGood D N (θ N) Λ z u y Γ Υ lr)ᶜ ≤ ENNReal.ofReal ε₀ :=
    FI_bad_le (θ N) (μ N) Λ z u y Γ Υ lr (n ^ ε₂ * lb N z) ((V.card : ℝ) ^ 2 * n ^ (-D₁))
      (n ^ (-D₁)) (by positivity) (by positivity) hnlr hG hY
  have hw0 : 0 < w := Real.rpow_pos_of_pos hY0 _
  have hR := hK N (θ N) (μ N) (hseq.mem N) (hseq.theta N).1 (hseq.theta N).2 Λ hΛ hΛn z hηN hzn
    u y hu.le hy Γ Υ lr ε₀ hΓ1 hΓN hΥ1 hΥ2 hzlr hbad (n ^ τ' * w) (by positivity)
  refine hR.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the exponent count
  set zh : ℝ := (Real.sqrt D + 3) * (1 + ‖z‖) * Γ ^ 3 * Real.sqrt (Υ / (n * z.im)) with hzh
  have hzh0 : 0 ≤ zh :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) 3)) (Real.sqrt_nonneg _)
  have hXr : (zh * lr ^ 2) ^ ((2 * (p : ℝ)) / 3) = ((zh * lr ^ 2) ^ ((1 : ℝ) / 3)) ^ (2 * p) := by
    rw [← Real.rpow_natCast ((zh * lr ^ 2) ^ ((1 : ℝ) / 3)) (2 * p),
      ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  have hx : (zh * lr ^ 2) ^ ((1 : ℝ) / 3) ≤ c * n ^ (4 * ε₁ + τ' / 6) * w := by
    have h := FI_X_le zh lr ζ (lb N z) c n ε₁ ε₂ hn0 (by linarith) hζ0.le hzh0 hζhat hlr'
    rwa [show 4 * ε₁ + 2 * ε₂ / 3 = 4 * ε₁ + τ' / 6 by rw [hε₂]; ring] at h
  have hε : ε₀ ≤ n ^ (3 - D₁) := by
    have hcube := FI_card_cube D N V.card Yset.card hD1 hNN₇ (FI_card_V D N (θ N) Λ u y)
      (FI_card_Y D N (θ N) u y)
    have e1 : ε₀ = ((V.card : ℝ) ^ 2 + Yset.card) * n ^ (-D₁) := by rw [hε₀]; ring
    have e2 : n ^ (3 - D₁) = n ^ 3 * n ^ (-D₁) := by
      rw [sub_eq_add_neg, Real.rpow_add hn0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hcube (by positivity)
  have hnK : K * (c ^ (2 * p) + 2) ≤ n := by
    refine hN₆.trans ?_
    exact Nat.cast_le.mpr hNN₆
  rw [hXr]
  exact FI_final p hp1 n τ' D' K c ε₁ ε₀ w ((zh * lr ^ 2) ^ ((1 : ℝ) / 3)) hn1 hτ' hD' hpτ hε₁a
    hK0 hc1 hwl (Real.rpow_nonneg (mul_nonneg hzh0 (sq_nonneg _)) _) hx hε hnK

/-! ### Helpers for the final bounds -/

/-- `ζ_φ = (1 + |z|)(1 + φ)³((Im m + φ + η)/(Nη))^{1/2} ≥ N^{-1/2}`, with no loss in `|z|`. -/
private lemma FI_zeta_lower (n η m φ zn : ℝ) (hn0 : 0 < n) (hη : 0 < η) (hm : 0 ≤ m)
    (hφ : 0 ≤ φ) (hzn : 0 ≤ zn) :
    n ^ (-(1 / 2 : ℝ)) ≤ (1 + zn) * (1 + φ) ^ 3 * Real.sqrt ((m + φ + η) / (n * η)) := by
  have hNη : 0 < n * η := mul_pos hn0 hη
  have h1 : n ^ (-(1 / 2 : ℝ)) = Real.sqrt (η / (n * η)) := by
    rw [show η / (n * η) = n⁻¹ by field_simp, Real.sqrt_inv, Real.sqrt_eq_rpow,
      Real.rpow_neg hn0.le]
  have h2 : Real.sqrt (η / (n * η)) ≤ Real.sqrt ((m + φ + η) / (n * η)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hNη.le)
  have h3 : 1 ≤ (1 + zn) * (1 + φ) ^ 3 := by
    have : 1 ≤ (1 + φ) ^ 3 := one_le_pow₀ (by linarith)
    have h4 : 1 ≤ 1 + zn := by linarith
    nlinarith
  rw [h1]
  calc Real.sqrt (η / (n * η)) ≤ 1 * Real.sqrt ((m + φ + η) / (n * η)) := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)

/-- `ζ_φ ≤ (12/5)(1 + |z|)^{10}(1 + φ)³ Ψ_φ` (`zeta_le_psi` with `a = 1`) -/
private lemma FI_zeta_psi (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (hΛn : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (φ : ℝ)
    (hφ : 0 ≤ φ) :
    (1 + ‖z‖) * (1 + φ) ^ 3 * Real.sqrt (((mExt Λ z).im + φ + z.im) / ((N : ℝ) * z.im)) ≤
      12 / 5 * ((1 + ‖z‖) ^ (10 : ℝ) * (1 + φ) ^ 3 * psiPhi Λ N z φ) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨hm0, -⟩ := FI_mExt Λ hΛ hΛn z hz
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNη : 0 < (N : ℝ) * z.im := mul_pos hN0 hz
  have h1 := zeta_le_psi D N hD hN Λ hΛ hΛn z hz φ 1 hφ le_rfl
  rw [Real.sqrt_one, mul_one, one_mul] at h1
  have h2 : Real.sqrt (((mExt Λ z).im + φ + z.im) / ((N : ℝ) * z.im)) ≤
      Real.sqrt ((41 / 16 * z.im + 25 / 16 * (mExt Λ z).im + φ) / ((N : ℝ) * z.im)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hNη.le)
  have hz1 : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have h10 : (1 + ‖z‖) ^ (10 : ℝ) = (1 + ‖z‖) ^ (10 : ℕ) := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h3 : (1 + ‖z‖) ^ 2 ≤ (1 + ‖z‖) ^ (10 : ℕ) := pow_le_pow_right₀ hz1 (by norm_num)
  have h4 : Real.sqrt (((mExt Λ z).im + φ) / ((N : ℝ) * z.im)) ≤ psiPhi Λ N z φ := by
    unfold psiPhi
    have : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
    linarith
  have hS0 := Real.sqrt_nonneg (((mExt Λ z).im + φ) / ((N : ℝ) * z.im))
  have hb : 0 ≤ (1 + φ) ^ 3 := pow_nonneg (by linarith) 3
  rw [h10]
  calc (1 + ‖z‖) * (1 + φ) ^ 3 * Real.sqrt (((mExt Λ z).im + φ + z.im) / ((N : ℝ) * z.im))
      ≤ (1 + ‖z‖) * (1 + φ) ^ 3 *
          (12 / 5 * (1 + ‖z‖) * Real.sqrt (((mExt Λ z).im + φ) / ((N : ℝ) * z.im))) :=
        mul_le_mul_of_nonneg_left (h2.trans h1) (mul_nonneg (by linarith) hb)
    _ = 12 / 5 * ((1 + ‖z‖) ^ 2 * (1 + φ) ^ 3 *
          Real.sqrt (((mExt Λ z).im + φ) / ((N : ℝ) * z.im))) := by ring
    _ ≤ 12 / 5 * ((1 + ‖z‖) ^ (10 : ℕ) * (1 + φ) ^ 3 * psiPhi Λ N z φ) := by
        gcongr

/-- `PrecS` is monotone in the control. -/
private lemma FI_precS_mono {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) {U : ℕ → Type*} (ξ ζ₁ ζ₂ : ∀ N, U N → Ω N → ℝ)
    (h : PrecS P ξ ζ₁) (hle : ∀ N u ω, ζ₁ N u ω ≤ ζ₂ N u ω) : PrecS P ξ ζ₂ := by
  intro τ hτ D hD
  obtain ⟨N₀, hN₀⟩ := h τ hτ D hD
  refine ⟨N₀, fun N hN u => le_trans (measure_mono fun ω hω => ?_) (hN₀ N hN u)⟩
  have h0 : 0 ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hle N u ω) h0) hω

/-- The deterministic bound `|(H̲G)_{uy}| ≤ 4N²` along the sequence, almost surely, for large
`N`, `z ∈ Z_N` and `|u|, |y| ≤ 1` (`hgUnder_form_le`). -/
private lemma FI_det (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hseq : LLSeq D δA C θ μ A) (hτ : 0 < τ) (hδτ : 10 * δ₀ ≤ τ) (Z : ℕ → Set ℂ)
    (hZ : ∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z ∈ Z N, ∀ u y : Idx D N → ℂ, ∑ k, ‖u k‖ ^ 2 ≤ 1 →
      ∑ k, ‖y k‖ ^ 2 ≤ 1 → ∀ᵐ h ∂(μ N),
        ‖star u ⬝ᵥ (hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z *ᵥ y)‖ ≤ 4 * (N : ℝ) ^ 2 := by
  obtain ⟨N₃, hN₃⟩ := FI_lam_small D δA C θ μ A hseq
  refine ⟨max N₃ 2, fun N hN z hz u y hu hy => ?_⟩
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hN1 : 1 ≤ N := by omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn2 : (1 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hn0 : (0 : ℝ) < N := by linarith
  have hΛn := hN₃ N ((le_max_left _ _).trans hN) hN1
  obtain ⟨hzn, hzim⟩ := hZ N z hz
  have hη : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hzim
  have hδ9 : δ₀ ≤ 1 / 9 := by
    have h1 : (N : ℝ) ^ (-1 + τ) ≤ (N : ℝ) ^ δ₀ :=
      hzim.trans ((Complex.im_le_norm z).trans hzn)
    have h2 := (Real.rpow_le_rpow_left_iff hn2).mp h1
    linarith
  have hzN : ‖z‖ ≤ N := by
    refine hzn.trans ?_
    calc (N : ℝ) ^ δ₀ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = N := Real.rpow_one _
  have hηi : z.im⁻¹ ≤ N := by
    have h1 : (N : ℝ)⁻¹ ≤ z.im := by
      refine le_trans ?_ hzim
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [inv_le_comm₀ hη hn0]
    exact h1
  filter_upwards [(hseq.mem N).herm] with h hh
  refine (hgUnder_form_le D N (θ N) (hseq.theta N).1 (hseq.theta N).2 _ _ hh
    (lam_isHermitian D N (A N)) z hη u y hu hy).trans ?_
  have hΛ0 : 0 ≤ opNorm (lam D N (A N)) := norm_nonneg _
  have e1 : (opNorm (lam D N (A N)) + ‖z‖) / z.im = (opNorm (lam D N (A N)) + ‖z‖) * z.im⁻¹ :=
    div_eq_mul_inv _ _
  have e2 : 1 / z.im ^ 2 = (z.im⁻¹) ^ 2 := by rw [one_div, inv_pow]
  have hi0 : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  have h1 : (opNorm (lam D N (A N)) + ‖z‖) * z.im⁻¹ ≤ (1 / 10 + N) * N :=
    mul_le_mul (by linarith) hηi hi0 (by linarith)
  have h2 : (z.im⁻¹) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hi0 hηi 2
  rw [e1, e2]
  nlinarith

/-- The control of the rounds, `N^{3 (2/3)^r} ζ_φ`. -/
private def FI_lbr {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (φv : ℝ) (r : ℕ) : ℝ :=
  (N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ r) *
    ((1 + ‖z‖) * (1 + φv) ^ 3 * Real.sqrt (((mExt Λ z).im + φv + z.im) / ((N : ℝ) * z.im)))

/-- One round maps the control `N^{3(2/3)^r} ζ` to `N^{3(2/3)^{r+1}} ζ`:
`(ζ (N^c ζ)²)^{1/3} = N^{2c/3} ζ`. -/
private lemma FI_lbr_succ {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (φv : ℝ)
    (hφ : 0 ≤ φv) (r : ℕ) :
    ((1 + ‖z‖) * (1 + φv) ^ 3 * Real.sqrt (((mExt Λ z).im + φv + z.im) / ((N : ℝ) * z.im)) *
        FI_lbr Λ z φv r ^ 2) ^ ((1 : ℝ) / 3) = FI_lbr Λ z φv (r + 1) := by
  set ζ := (1 + ‖z‖) * (1 + φv) ^ 3 * Real.sqrt (((mExt Λ z).im + φv + z.im) / ((N : ℝ) * z.im))
    with hζ
  have hζ0 : 0 ≤ ζ := mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) 3))
    (Real.sqrt_nonneg _)
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hc : ((N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ (r + 1))) ^ 3 =
      ((N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ r)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast ((N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ r)),
      ← Real.rpow_mul hn0, ← Real.rpow_mul hn0, pow_succ]
    congr 1
    push_cast
    ring
  have e : ζ * FI_lbr Λ z φv r ^ 2 = ((N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ (r + 1)) * ζ) ^ 3 := by
    have e0 : FI_lbr Λ z φv r = (N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ r) * ζ := rfl
    rw [e0, mul_pow (_ : ℝ) ζ 3, hc]
    ring
  rw [e, show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (mul_nonneg (Real.rpow_nonneg hn0 _) hζ0) (by norm_num)]
  rfl

/-- `(H̲G)_{uy} ≺ (1 + |z|)^{10} (1 + φ)³ Ψ_φ` over `z ∈ Z_N`, unit `u` and `|y| ≤ 1`: `r` rounds of
`iso_self_improv` from the deterministic control `N³ ζ_φ`, then `zeta_le_psi` -/
private lemma FI_prec_y (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hseq : LLSeq D δA C θ μ A) (hτ : 0 < τ) (hδ₀ : 0 ≤ δ₀) (hδτ : 10 * δ₀ ≤ τ)
    (Z : ℕ → Set ℂ) (hZ : ∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im)
    (φ : ℕ → ℂ → ℝ) (hφ : ∀ N, ∀ z ∈ Z N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀)
    (hLL : aprioriLL D μ A Z φ) :
    PrecS μ (U := fun N => {z // z ∈ Z N} × {u : Idx D N → ℂ // ∑ i, ‖u i‖ ^ 2 = 1} ×
        {y : Idx D N → ℂ // ∑ i, ‖y i‖ ^ 2 ≤ 1})
      (fun N w h => ‖star w.2.1.1 ⬝ᵥ
        (hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1 *ᵥ w.2.2.1)‖)
      (fun N w _ => (1 + ‖w.1.1‖) ^ (10 : ℝ) * (1 + φ N w.1.1) ^ 3 *
        psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1)) := by
  have hD1 := hseq.one_le_D
  have hφ0 : ∀ N, ∀ z ∈ Z N, 0 ≤ φ N z := fun N z hz => le_trans (by positivity) (hφ N z hz).1
  obtain ⟨Nd, hNd⟩ := FI_det D δA τ δ₀ C θ μ A hseq hτ hδτ Z hZ
  obtain ⟨N₃, hN₃⟩ := FI_lam_small D δA C θ μ A hseq
  -- the rounds
  have hround : ∀ r : ℕ, PrecS μ (U := fun N => {z // z ∈ Z N} ×
      {u : Idx D N → ℂ // ∑ i, ‖u i‖ ^ 2 = 1} × {y : Idx D N → ℂ // ∑ i, ‖y i‖ ^ 2 ≤ 1})
      (fun N w h => ‖star w.2.1.1 ⬝ᵥ
        (hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1 *ᵥ w.2.2.1)‖)
      (fun N w _ => FI_lbr (lam D N (A N)) w.1.1 (φ N w.1.1) r) := by
    intro r
    induction r with
    | zero =>
      intro τ' hτ' D' hD'
      obtain ⟨N₅, hN₅⟩ := FI_rpow_ge (show (0 : ℝ) < 1 / 2 by norm_num) 5
      refine ⟨max (max Nd N₃) (max N₅ 1), fun N hN w => ?_⟩
      simp only [max_le_iff] at hN
      obtain ⟨⟨hNd', hN₃'⟩, hN₅', hN1⟩ := hN
      obtain ⟨⟨z, hz⟩, ⟨u, hu⟩, ⟨y, hy⟩⟩ := w
      have hn1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN1
      have hn0 : (0 : ℝ) < N := by linarith
      have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
      have hΛn := hN₃ N hN₃' hN1
      have hη : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) (hZ N z hz).2
      obtain ⟨hm0, -⟩ := FI_mExt (lam D N (A N)) (lam_isHermitian D N (A N)) hΛn z hη
      have hζ := FI_zeta_lower N z.im (mExt (lam D N (A N)) z).im (φ N z) ‖z‖ hn0 hη hm0.le
        (hφ0 N z hz) (norm_nonneg z)
      have h5 := hN₅ N hN₅'
      have e3 : (N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ 0) * (N : ℝ) ^ (-(1 / 2 : ℝ)) =
          (N : ℝ) ^ 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hn0, ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hn0]
        norm_num
      have hlow : 5 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ τ' * FI_lbr (lam D N (A N)) z (φ N z) 0 := by
        unfold FI_lbr
        have h1 : 1 ≤ (N : ℝ) ^ τ' := Real.one_le_rpow hn1 hτ'.le
        have h2 : 0 ≤ (N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ 0) := Real.rpow_nonneg hn0.le _
        have h3 : 5 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ 0) *
            ((1 + ‖z‖) * (1 + φ N z) ^ 3 *
              Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im))) := by
          calc 5 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by nlinarith
            _ = (N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ 0) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := e3.symm
            _ ≤ _ := mul_le_mul_of_nonneg_left hζ h2
        have h4 : 0 ≤ (N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ 0) *
            ((1 + ‖z‖) * (1 + φ N z) ^ 3 *
              Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im))) :=
          le_trans (by positivity) h3
        nlinarith
      have hS : {h : Idx D N → Idx D N → ℂ | (N : ℝ) ^ τ' * FI_lbr (lam D N (A N)) z (φ N z) 0 <
          ‖star u ⬝ᵥ (hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z *ᵥ y)‖} ≤ᵐ[μ N]
          (∅ : Set (Idx D N → Idx D N → ℂ)) := by
        filter_upwards [hNd N hNd' z hz u y hu.le hy] with h hb hh
        exfalso
        have hh' : (N : ℝ) ^ τ' * FI_lbr (lam D N (A N)) z (φ N z) 0 <
            ‖star u ⬝ᵥ (hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) z *ᵥ y)‖ := hh
        have : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
        linarith
      refine le_trans (measure_mono_ae hS) ?_
      rw [measure_empty]
      exact bot_le
    | succ r ih =>
      have hlb : ∀ N, ∀ z ∈ Z N, (1 + ‖z‖) * (1 + φ N z) ^ 3 *
          Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im)) ≤
            FI_lbr (lam D N (A N)) z (φ N z) r := by
        intro N z hz
        have hζ0 : 0 ≤ (1 + ‖z‖) * (1 + φ N z) ^ 3 *
            Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z + z.im) / ((N : ℝ) * z.im)) :=
          mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith [hφ0 N z hz]) 3))
            (Real.sqrt_nonneg _)
        unfold FI_lbr
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · subst h0
          simp
        · exact le_mul_of_one_le_left hζ0
            (Real.one_le_rpow (Nat.one_le_cast.mpr h0) (by positivity))
      have h := iso_self_improv D δA τ δ₀ C θ μ A hseq hτ hδ₀ hδτ Z hZ φ hφ hLL
        (fun N z => FI_lbr (lam D N (A N)) z (φ N z) r) hlb ih
      exact FI_precS_mono _ _ _ _ h
        (fun N w _ => le_of_eq (FI_lbr_succ _ _ _ (hφ0 N w.1.1 w.1.2) r))
  -- the conversion to `Ψ_φ`
  intro τ' hτ' D' hD'
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (2 / 3 : ℝ) ^ r < τ' / 12 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := hround r (τ' / 2) (by positivity) D' hD'
  obtain ⟨N₄, hN₄⟩ := FI_rpow_ge (show (0 : ℝ) < τ' / 4 by positivity) (12 / 5)
  refine ⟨max (max N₀ N₃) (max N₄ 1), fun N hN w => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨hN₀', hN₃'⟩, hN₄', hN1⟩ := hN
  obtain ⟨⟨z, hz⟩, ⟨u, hu⟩, ⟨y, hy⟩⟩ := w
  suffices key : (N : ℝ) ^ (τ' / 2) * FI_lbr (lam D N (A N)) z (φ N z) r ≤ (N : ℝ) ^ τ' *
      ((1 + ‖z‖) ^ (10 : ℝ) * (1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z)) by
    refine le_trans (measure_mono fun h hh => ?_) (hN₀ N hN₀' ⟨⟨z, hz⟩, ⟨u, hu⟩, ⟨y, hy⟩⟩)
    exact lt_of_le_of_lt key hh
  have hn1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hΛn := hN₃ N hN₃' hN1
  have hη : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) (hZ N z hz).2
  have hψ := FI_zeta_psi D N hD1 hN1 (lam D N (A N)) (lam_isHermitian D N (A N)) hΛn z hη
    (φ N z) (hφ0 N z hz)
  have hX0 : 0 ≤ (1 + ‖z‖) ^ (10 : ℝ) * (1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z) := by
    have h1 : 0 ≤ psiPhi (lam D N (A N)) N z (φ N z) := by
      unfold psiPhi
      have : 0 < (N : ℝ) * z.im := mul_pos hn0 hη
      positivity
    have h2 : 0 ≤ (1 + φ N z) ^ 3 := pow_nonneg (by linarith [hφ0 N z hz]) 3
    have h3 : 0 ≤ (1 + ‖z‖) ^ (10 : ℝ) := Real.rpow_nonneg (by positivity) _
    positivity
  have hc : (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ r) ≤ (N : ℝ) ^ (3 * τ' / 4) := by
    rw [← Real.rpow_add hn0]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h12 := hN₄ N hN₄'
  have e : (N : ℝ) ^ τ' = (N : ℝ) ^ (3 * τ' / 4) * (N : ℝ) ^ (τ' / 4) := by
    rw [← Real.rpow_add hn0]
    ring_nf
  unfold FI_lbr
  rw [e]
  have hζ0 : 0 ≤ (1 + ‖z‖) * (1 + φ N z) ^ 3 * Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z +
      z.im) / ((N : ℝ) * z.im)) :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith [hφ0 N z hz]) 3))
      (Real.sqrt_nonneg _)
  calc (N : ℝ) ^ (τ' / 2) * ((N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ r) *
        ((1 + ‖z‖) * (1 + φ N z) ^ 3 * Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z +
          z.im) / ((N : ℝ) * z.im))))
      = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (3 * (2 / 3 : ℝ) ^ r) *
        ((1 + ‖z‖) * (1 + φ N z) ^ 3 * Real.sqrt (((mExt (lam D N (A N)) z).im + φ N z +
          z.im) / ((N : ℝ) * z.im))) := by ring
    _ ≤ (N : ℝ) ^ (3 * τ' / 4) * (12 / 5 * ((1 + ‖z‖) ^ (10 : ℝ) * (1 + φ N z) ^ 3 *
          psiPhi (lam D N (A N)) N z (φ N z))) :=
        mul_le_mul hc hψ hζ0 (Real.rpow_nonneg hn0.le _)
    _ ≤ (N : ℝ) ^ (3 * τ' / 4) * ((N : ℝ) ^ (τ' / 4) * ((1 + ‖z‖) ^ (10 : ℝ) *
          (1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h12 hX0)
          (Real.rpow_nonneg hn0.le _)
    _ = _ := by ring




/-- `(H̲G)_{uv} ≺ (1 + |z|)^K (1 + φ)³ Ψ_φ` in sup form over `z ∈ Z_N` and deterministic unit
`u, v`, under `LLSeq`, `K δ₀ ≤ τ` and `aprioriLL`. -/
theorem fluct_iso_prec' : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (D : ℕ) (δA τ δ₀ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
      (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ),
      LLSeq D δA C θ μ A → 0 < τ → 0 ≤ δ₀ → K * δ₀ ≤ τ →
    ∀ Z : ℕ → Set ℂ, (∀ N, ∀ z ∈ Z N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im) →
    ∀ φ : ℕ → ℂ → ℝ, (∀ N, ∀ z ∈ Z N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀) →
    aprioriLL D μ A Z φ →
    PrecS μ (U := fun N => {z // z ∈ Z N} × {u : Idx D N → ℂ // ∑ i, ‖u i‖ ^ 2 = 1} ×
        {v : Idx D N → ℂ // ∑ i, ‖v i‖ ^ 2 = 1})
      (fun N w h => ‖star w.2.1.1 ⬝ᵥ
        (hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1 *ᵥ w.2.2.1)‖)
      (fun N w _ => (1 + ‖w.1.1‖) ^ K * (1 + φ N w.1.1) ^ 3 *
        psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1)) := by
  refine ⟨10, by norm_num, ?_⟩
  intro D δA τ δ₀ C θ μ A hseq hτ hδ₀ hδτ Z hZ φ hφ hLL τ' hτ' D' hD'
  obtain ⟨N₀, hN₀⟩ := FI_prec_y D δA τ δ₀ C θ μ A hseq hτ hδ₀ hδτ Z hZ φ hφ hLL τ' hτ' D' hD'
  exact ⟨N₀, fun N hN w => hN₀ N hN ⟨w.1, w.2.1, ⟨w.2.2.1, le_of_eq w.2.2.2⟩⟩⟩


end RBMTransitionEdge

end
