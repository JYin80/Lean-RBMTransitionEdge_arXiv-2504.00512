module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Det.Core
public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.Tools.Resolvent
public import RBMTransitionEdge.Tools.ResolventIdentities
public import RBMTransitionEdge.LocalLaw.Class

@[expose] public section

/-!
# Lemma A.4: products of resolvents, conditional on (2.22)

Lemma A.4 [lemma_necessary_estimates]: (A.53) [entprodG], (A.54) [one_loop_estimate] and (A.55)
[two_loop_estimate], conditional on the anisotropic local law (2.22) [eq:aniso_local] as the paper states them.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The ordered product `∏_{i=1}^p G_i^{s_i} B_i` of (A.53) [entprodG], with `G_i^{s_i} = G_i^*`
when `s_i` holds. -/
def resProd {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} (G : Fin p → Matrix ι ι ℂ)
    (s : Fin p → Bool) (B : Fin p → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (List.ofFn fun i => (if s i then (G i)ᴴ else G i) * B i).prod

/-- A product `Π_l = B₀ G_{w_1}^{s_1} B₁ ⋯ G_{w_l}^{s_l} B_l` of Lemma A.4
[lemma_necessary_estimates] with `l` resolvent factors and deterministic factors `B_j` between
them. -/
def resWord {ι : Type*} [Fintype ι] [DecidableEq ι] {p l : ℕ} (G : Fin p → Matrix ι ι ℂ)
    (w : Fin l → Fin p × Bool) (B : Fin (l + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  B 0 * (List.ofFn fun j : Fin l =>
    (if (w j).2 then (G (w j).1)ᴴ else G (w j).1) * B j.succ).prod

/-- The size `(max_i Im m_i)^{1(l ≥ 2)} / η^{l-1}`, `η = min_i η_i`, of (A.53) [entprodG]. -/
def bndA4 {p : ℕ} (imm eta : Fin p → ℝ) (l : ℕ) : ℝ :=
  (if 2 ≤ l then ⨆ i, imm i else 1) / (⨅ i, eta i) ^ (l - 1)

section Helpers

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Euclidean norm of a vector. -/
private def MultiRes_vn (x : ι → ℂ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖

omit [DecidableEq ι] in
private lemma MultiRes_vn_nonneg (x : ι → ℂ) : 0 ≤ MultiRes_vn x := norm_nonneg _

omit [DecidableEq ι] in
private lemma MultiRes_vn_sq (x : ι → ℂ) : MultiRes_vn x ^ 2 = ∑ p, ‖x p‖ ^ 2 := by
  unfold MultiRes_vn
  rw [EuclideanSpace.norm_sq_eq]

omit [DecidableEq ι] in
private lemma MultiRes_vn_zero : MultiRes_vn (0 : ι → ℂ) = 0 := by
  simp [MultiRes_vn]

omit [DecidableEq ι] in
private lemma MultiRes_vn_smul (c : ℂ) (x : ι → ℂ) : MultiRes_vn (c • x) = ‖c‖ * MultiRes_vn x := by
  unfold MultiRes_vn
  rw [← norm_smul]
  rfl

omit [DecidableEq ι] in
private lemma MultiRes_vn_eq_zero {x : ι → ℂ} (h : MultiRes_vn x = 0) : x = 0 := by
  unfold MultiRes_vn at h
  rw [norm_eq_zero] at h
  simpa using congrArg WithLp.ofLp h

private lemma MultiRes_vn_mulVec_le (A : Matrix ι ι ℂ) (x : ι → ℂ) :
    MultiRes_vn (A *ᵥ x) ≤ opNorm A * MultiRes_vn x := by
  unfold MultiRes_vn opNorm
  have h := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 x)
  rwa [Matrix.toEuclideanCLM_toLp] at h

private lemma MultiRes_opNorm_nonneg (A : Matrix ι ι ℂ) : 0 ≤ opNorm A := norm_nonneg _

omit [DecidableEq ι] in
private lemma MultiRes_norm_dot_le (x y : ι → ℂ) :
    ‖star x ⬝ᵥ y‖ ≤ MultiRes_vn x * MultiRes_vn y := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  unfold MultiRes_vn
  simpa [dotProduct_comm] using h

private lemma MultiRes_opNorm_conjTranspose (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) A)

private lemma MultiRes_opNorm_one_le : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-- `opNorm` bound from the quadratic bound on vectors. -/
private lemma MultiRes_opNorm_le {A : Matrix ι ι ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : ι → ℂ, MultiRes_vn (A *ᵥ x) ≤ c * MultiRes_vn x) : opNorm A ≤ c := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have := h x.ofLp
  unfold MultiRes_vn at this
  have hx : x = WithLp.toLp 2 x.ofLp := rfl
  rw [hx, Matrix.toEuclideanCLM_toLp]
  simpa using this

end Helpers

section HS

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The squared Hilbert–Schmidt norm. -/
private def MultiRes_hs2 (Z : Matrix ι ι ℂ) : ℝ := ∑ p, ∑ q, ‖Z p q‖ ^ 2

omit [DecidableEq ι] in
private lemma MultiRes_hs2_nonneg (Z : Matrix ι ι ℂ) : 0 ≤ MultiRes_hs2 Z := by
  unfold MultiRes_hs2; positivity

omit [DecidableEq ι] in
private lemma MultiRes_hsNorm_sq (Z : Matrix ι ι ℂ) : hsNorm Z ^ 2 = MultiRes_hs2 Z := by
  unfold hsNorm MultiRes_hs2
  exact Real.sq_sqrt (by positivity)

omit [DecidableEq ι] in
private lemma MultiRes_hsNorm_nonneg (Z : Matrix ι ι ℂ) : 0 ≤ hsNorm Z := Real.sqrt_nonneg _

omit [DecidableEq ι] in
private lemma MultiRes_hs2_cols (Z : Matrix ι ι ℂ) :
    MultiRes_hs2 Z = ∑ q, MultiRes_vn (fun p => Z p q) ^ 2 := by
  unfold MultiRes_hs2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => (MultiRes_vn_sq _).symm

omit [DecidableEq ι] in
private lemma MultiRes_trace_mul_conjTranspose (Z : Matrix ι ι ℂ) :
    (Z * Zᴴ).trace = (MultiRes_hs2 Z : ℂ) := by
  unfold MultiRes_hs2
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

private lemma MultiRes_hs2_mul_unitary (Z U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    MultiRes_hs2 (Z * U) = MultiRes_hs2 Z := by
  have h1 := MultiRes_trace_mul_conjTranspose (Z * U)
  have h2 := MultiRes_trace_mul_conjTranspose Z
  have e : Z * U * (Z * U)ᴴ = Z * Zᴴ := by
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Z U, hU, Matrix.mul_one]
  rw [e] at h1
  exact_mod_cast h1.symm.trans h2

omit [DecidableEq ι] in
private lemma MultiRes_hs2_conjTranspose (Z : Matrix ι ι ℂ) :
    MultiRes_hs2 Zᴴ = MultiRes_hs2 Z := by
  unfold MultiRes_hs2
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

private lemma MultiRes_hs2_mul_left_le (B Z : Matrix ι ι ℂ) :
    MultiRes_hs2 (B * Z) ≤ opNorm B ^ 2 * MultiRes_hs2 Z := by
  rw [MultiRes_hs2_cols, MultiRes_hs2_cols, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have e : (fun p => (B * Z) p q) = B *ᵥ (fun p => Z p q) := by
    ext p
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ (MultiRes_vn_nonneg _) (MultiRes_vn_mulVec_le _ _) 2

private lemma MultiRes_hs2_mul_right_le (Z B : Matrix ι ι ℂ) :
    MultiRes_hs2 (Z * B) ≤ MultiRes_hs2 Z * opNorm B ^ 2 := by
  have h := MultiRes_hs2_mul_left_le Bᴴ Zᴴ
  rw [← Matrix.conjTranspose_mul, MultiRes_hs2_conjTranspose, MultiRes_hs2_conjTranspose,
    MultiRes_opNorm_conjTranspose] at h
  linarith

private lemma MultiRes_vn_single (q : ι) : MultiRes_vn (Pi.single q (1 : ℂ) : ι → ℂ) = 1 := by
  have h : MultiRes_vn (Pi.single q (1 : ℂ) : ι → ℂ) ^ 2 = 1 := by
    rw [MultiRes_vn_sq, Finset.sum_eq_single q]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  nlinarith [MultiRes_vn_nonneg (Pi.single q (1 : ℂ) : ι → ℂ)]

private lemma MultiRes_hs2_le_card (Z : Matrix ι ι ℂ) :
    MultiRes_hs2 Z ≤ (Fintype.card ι : ℝ) * opNorm Z ^ 2 := by
  rw [MultiRes_hs2_cols]
  have : ∀ q : ι, MultiRes_vn (fun p => Z p q) ^ 2 ≤ opNorm Z ^ 2 := by
    intro q
    have e : (fun p => Z p q) = Z *ᵥ (Pi.single q (1 : ℂ) : ι → ℂ) := by
      ext p
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have h := MultiRes_vn_mulVec_le Z (Pi.single q (1 : ℂ) : ι → ℂ)
    rw [MultiRes_vn_single, mul_one] at h
    rw [e]
    exact pow_le_pow_left₀ (MultiRes_vn_nonneg _) h 2
  calc ∑ q, MultiRes_vn (fun p => Z p q) ^ 2 ≤ ∑ _q : ι, opNorm Z ^ 2 :=
        Finset.sum_le_sum fun q _ => this q
    _ = (Fintype.card ι : ℝ) * opNorm Z ^ 2 := by simp

omit [DecidableEq ι] in
/-- The trace Cauchy–Schwarz inequality `|tr(PQ)| ≤ ‖P‖_HS ‖Q‖_HS`. -/
private lemma MultiRes_norm_trace_mul_le (P Q : Matrix ι ι ℂ) :
    ‖(P * Q).trace‖ ≤ hsNorm P * hsNorm Q := by
  have h1 : ‖(P * Q).trace‖ ≤ ∑ x : ι × ι, ‖P x.1 x.2‖ * ‖Q x.2 x.1‖ := by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_mul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun x => ‖P x.1 x.2‖) (fun x => ‖Q x.2 x.1‖)
  have e1 : ∑ x : ι × ι, ‖P x.1 x.2‖ ^ 2 = MultiRes_hs2 P := by
    rw [Fintype.sum_prod_type]; rfl
  have e2 : ∑ x : ι × ι, ‖Q x.2 x.1‖ ^ 2 = MultiRes_hs2 Q := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rw [e1, e2] at h2
  have h3 : (∑ x : ι × ι, ‖P x.1 x.2‖ * ‖Q x.2 x.1‖) ^ 2 ≤ (hsNorm P * hsNorm Q) ^ 2 := by
    rw [mul_pow, MultiRes_hsNorm_sq, MultiRes_hsNorm_sq]; exact h2
  have h4 := abs_le_of_sq_le_sq h3 (mul_nonneg (MultiRes_hsNorm_nonneg P) (MultiRes_hsNorm_nonneg Q))
  exact h1.trans ((le_abs_self _).trans h4)

end HS

section Spec

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Spectral decomposition of a Hermitian matrix with a unitary of columns. -/
private lemma MultiRes_spec (Y : Matrix ι ι ℂ) (hY : Y.IsHermitian) :
    ∃ (U : Matrix ι ι ℂ) (a : ι → ℝ), U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      Y = U * Matrix.diagonal (fun k => (a k : ℂ)) * Uᴴ := by
  refine ⟨(hY.eigenvectorUnitary : Matrix ι ι ℂ), hY.eigenvalues, ?_, ?_, ?_⟩
  · exact Unitary.coe_mul_star_self hY.eigenvectorUnitary
  · exact Unitary.coe_star_mul_self hY.eigenvectorUnitary
  · have h := hY.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h

/-- The columns of a unitary are unit vectors. -/
private lemma MultiRes_vn_col (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (k : ι) :
    MultiRes_vn (fun p => U p k) = 1 := by
  have h := congrFun (congrFun hU k) k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : MultiRes_vn (fun p => U p k) ^ 2 = 1 := by
    rw [MultiRes_vn_sq]
    have h3 : ((∑ p, ‖U p k‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h]
      push_cast
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Complex.star_def, Complex.conj_mul', ]
    exact_mod_cast h3
  nlinarith [MultiRes_vn_nonneg (fun p => U p k)]

private lemma MultiRes_trace_mul_diag (X U : Matrix ι ι ℂ) (a : ι → ℝ) :
    (X * (U * Matrix.diagonal (fun k => (a k : ℂ)) * Uᴴ)).trace =
      ∑ k, (a k : ℂ) * (star (fun p => U p k) ⬝ᵥ (X *ᵥ fun p => U p k)) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, mul_comm]
  congr 1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- `‖Z Y‖²_HS = Σ_k a_k² ‖Z u_k‖²` for `Y = U diag(a) U^*`. -/
private lemma MultiRes_hs2_mul_diag (Z U : Matrix ι ι ℂ) (a : ι → ℝ) (hU : U * Uᴴ = 1)
    (hU' : Uᴴ * U = 1) :
    MultiRes_hs2 (Z * (U * Matrix.diagonal (fun k => (a k : ℂ)) * Uᴴ)) =
      ∑ k, a k ^ 2 * MultiRes_vn (Z *ᵥ fun p => U p k) ^ 2 := by
  have hUH : Uᴴ * Uᴴᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hU'
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, MultiRes_hs2_mul_unitary _ _ hUH]
  unfold MultiRes_hs2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MultiRes_vn_sq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    mul_comm]
  rfl

private lemma MultiRes_sum_sq_eq (Y U : Matrix ι ι ℂ) (a : ι → ℝ) (hU : U * Uᴴ = 1)
    (hU' : Uᴴ * U = 1) (hY : Y = U * Matrix.diagonal (fun k => (a k : ℂ)) * Uᴴ) :
    ∑ k, a k ^ 2 = MultiRes_hs2 Y := by
  have h := MultiRes_hs2_mul_diag 1 U a hU hU'
  rw [← hY, Matrix.one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.one_mulVec, MultiRes_vn_col U hU' k]
  ring

end Spec

section Resolv

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma MultiRes_star_dot_conj (A : Matrix ι ι ℂ) (x y : ι → ℂ) :
    star (star y ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (Aᴴ *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, star_sum, star_mul', star_star,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

omit [DecidableEq ι] in
private lemma MultiRes_star_dot_self (y : ι → ℂ) : star y ⬝ᵥ y = ((MultiRes_vn y ^ 2 : ℝ) : ℂ) := by
  rw [MultiRes_vn_sq]
  simp only [dotProduct, Pi.star_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.conj_mul', ]

omit [DecidableEq ι] in
private lemma MultiRes_im_aux (X : Matrix ι ι ℂ) (c : ℝ) (x : ι → ℂ) (r : ℝ)
    (h1 : star x ⬝ᵥ ((X - Xᴴ) *ᵥ x) = (star x ⬝ᵥ (X *ᵥ x)) - star (star x ⬝ᵥ (X *ᵥ x)))
    (h2 : star x ⬝ᵥ ((X - Xᴴ) *ᵥ x) = (2 * Complex.I * c) * (r : ℂ)) :
    (star x ⬝ᵥ (X *ᵥ x)).im = c * r := by
  have h := congrArg Complex.im (h1.symm.trans h2)
  simp [Complex.star_def] at h
  linarith

omit [DecidableEq ι] in
/-- `Im ⟨x, X x⟩ = c ‖Xᴴ x‖²` when `X - Xᴴ = 2ic · X Xᴴ`. -/
private lemma MultiRes_im_form_left (X : Matrix ι ι ℂ) (c : ℝ)
    (h : X - Xᴴ = (2 * Complex.I * c) • (X * Xᴴ)) (x : ι → ℂ) :
    (star x ⬝ᵥ (X *ᵥ x)).im = c * MultiRes_vn (Xᴴ *ᵥ x) ^ 2 := by
  have key : star x ⬝ᵥ (X *ᵥ (Xᴴ *ᵥ x)) = ((MultiRes_vn (Xᴴ *ᵥ x) ^ 2 : ℝ) : ℂ) := by
    have := MultiRes_star_dot_conj Xᴴ x (Xᴴ *ᵥ x)
    rw [Matrix.conjTranspose_conjTranspose, MultiRes_star_dot_self] at this
    rw [← this]
    simp
  refine MultiRes_im_aux X c x _ ?_ ?_
  · rw [Matrix.sub_mulVec, dotProduct_sub, MultiRes_star_dot_conj X x x]
  · rw [h, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, dotProduct_smul, key, smul_eq_mul]

omit [DecidableEq ι] in
/-- `Im ⟨x, X x⟩ = c ‖X x‖²` when `X - Xᴴ = 2ic · Xᴴ X`. -/
private lemma MultiRes_im_form_right (X : Matrix ι ι ℂ) (c : ℝ)
    (h : X - Xᴴ = (2 * Complex.I * c) • (Xᴴ * X)) (x : ι → ℂ) :
    (star x ⬝ᵥ (X *ᵥ x)).im = c * MultiRes_vn (X *ᵥ x) ^ 2 := by
  have key : star x ⬝ᵥ (Xᴴ *ᵥ (X *ᵥ x)) = ((MultiRes_vn (X *ᵥ x) ^ 2 : ℝ) : ℂ) := by
    have := MultiRes_star_dot_conj X x (X *ᵥ x)
    rw [MultiRes_star_dot_self] at this
    rw [← this]
    simp
  refine MultiRes_im_aux X c x _ ?_ ?_
  · rw [Matrix.sub_mulVec, dotProduct_sub, MultiRes_star_dot_conj X x x]
  · rw [h, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, dotProduct_smul, key, smul_eq_mul]

/-- `G - G^* = 2iη G^*G = 2iη G G^*` for Hermitian `X`, `Im z > 0`. -/
private lemma MultiRes_ward_key (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ)
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

/-- The vector form of the Ward identity: `η ‖G x‖² = η ‖G^* x‖² = Im ⟨x, G x⟩`. -/
private lemma MultiRes_ward_vec (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (x : ι → ℂ) :
    z.im * MultiRes_vn (res X z *ᵥ x) ^ 2 = (star x ⬝ᵥ (res X z *ᵥ x)).im ∧
      z.im * MultiRes_vn ((res X z)ᴴ *ᵥ x) ^ 2 = (star x ⬝ᵥ (res X z *ᵥ x)).im := by
  obtain ⟨k1, k2⟩ := MultiRes_ward_key X hX z hz
  exact ⟨(MultiRes_im_form_right _ _ k1 x).symm, (MultiRes_im_form_left _ _ k2 x).symm⟩

end Resolv

section MBounds

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma MultiRes_opNorm_sub_smul_one_le (Λ : Matrix ι ι ℂ) (ζ : ℂ) :
    opNorm (Λ - ζ • (1 : Matrix ι ι ℂ)) ≤ opNorm Λ + ‖ζ‖ := by
  rw [sub_eq_add_neg, ← neg_smul]
  refine (opNorm_add_le _ _).trans ?_
  rw [opNorm_smul, norm_neg]
  have := MultiRes_opNorm_one_le (ι := ι)
  have h0 := norm_nonneg ζ
  nlinarith

/-- A priori facts on `M` used by the word bounds. -/
private lemma MultiRes_Mbounds [Nonempty ι] (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) (τ : ℝ) (z : ℂ) (hz : 0 < z.im) (hzτ : ‖z‖ ≤ τ⁻¹) :
    opNorm (MSol Λ z) ≤ 5 / 4 ∧ 0 < (mSol Λ z).im ∧ (mSol Λ z).im < 1 ∧
      (∀ x : ι → ℂ, (star x ⬝ᵥ (MSol Λ z *ᵥ x)).im ≤
        25 / 16 * (z.im + (mSol Λ z).im) * MultiRes_vn x ^ 2) ∧
      z.im + (mSol Λ z).im ≤ (11 / 10 + τ⁻¹) ^ 2 * (mSol Λ z).im := by
  obtain ⟨hpos, hm, hMM⟩ := mSol_spec Λ hΛ z hz
  obtain ⟨h1, h2, h3⟩ := mSol_apriori Λ hΛ hℓ z hz
  have hℓ0 := MultiRes_opNorm_nonneg Λ
  have hM54 : opNorm (MSol Λ z) ≤ 5 / 4 := by
    refine h3.le.trans ?_
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    norm_num
    linarith
  have him1 : (mSol Λ z).im < 1 :=
    lt_of_le_of_lt (le_trans (le_abs_self _) (Complex.abs_im_le_norm _)) h2
  obtain ⟨hnt, hforms⟩ := equation_z_im_m Λ hΛ z hz
  set m := mSol Λ z with hmdef
  set M := MSol Λ z with hMdef
  have hsum : 0 ≤ z.im + m.im := by linarith
  refine ⟨hM54, hpos, him1, ?_, ?_⟩
  · intro x
    rw [MultiRes_im_form_left M (z.im + m.im) (by simpa using hforms) x]
    have h4 : MultiRes_vn (Mᴴ *ᵥ x) ≤ 5 / 4 * MultiRes_vn x := by
      refine (MultiRes_vn_mulVec_le _ _).trans ?_
      rw [MultiRes_opNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_right hM54 (MultiRes_vn_nonneg _)
    have h5 : MultiRes_vn (Mᴴ *ᵥ x) ^ 2 ≤ (5 / 4 * MultiRes_vn x) ^ 2 :=
      pow_le_pow_left₀ (MultiRes_vn_nonneg _) h4 2
    calc (z.im + m.im) * MultiRes_vn (Mᴴ *ᵥ x) ^ 2 ≤ (z.im + m.im) * (5 / 4 * MultiRes_vn x) ^ 2 :=
          mul_le_mul_of_nonneg_left h5 hsum
      _ = 25 / 16 * (z.im + m.im) * MultiRes_vn x ^ 2 := by ring
  · -- lower bound of `⟨M M^*⟩`
    set s : ℝ := 11 / 10 + τ⁻¹ with hs
    have hτ0 : 0 ≤ τ⁻¹ := (norm_nonneg z).trans hzτ
    have hs0 : 0 < s := by rw [hs]; linarith
    have hζ : ‖z + m‖ ≤ 1 + τ⁻¹ := by
      refine (norm_add_le _ _).trans ?_
      linarith
    have hop : opNorm (Λ - (z + m) • (1 : Matrix ι ι ℂ)) ≤ s := by
      refine (MultiRes_opNorm_sub_smul_one_le _ _).trans ?_
      rw [hs]; linarith
    have hcol : ∀ q : ι, 1 / s ≤ MultiRes_vn (fun p => M p q) := by
      intro q
      have e : (fun p => M p q) = M *ᵥ (Pi.single q (1 : ℂ) : ι → ℂ) := by
        ext p
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      have e2 : (Λ - (z + m) • (1 : Matrix ι ι ℂ)) *ᵥ (M *ᵥ (Pi.single q (1 : ℂ) : ι → ℂ)) =
          (Pi.single q (1 : ℂ) : ι → ℂ) := by
        rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
      have h6 := MultiRes_vn_mulVec_le (Λ - (z + m) • (1 : Matrix ι ι ℂ))
        (M *ᵥ (Pi.single q (1 : ℂ) : ι → ℂ))
      rw [e2, MultiRes_vn_single] at h6
      rw [e, div_le_iff₀ hs0]
      have h7 := MultiRes_vn_nonneg (M *ᵥ (Pi.single q (1 : ℂ) : ι → ℂ))
      nlinarith [mul_le_mul_of_nonneg_right hop h7]
    have hhs : (Fintype.card ι : ℝ) * (1 / s) ^ 2 ≤ MultiRes_hs2 M := by
      rw [MultiRes_hs2_cols]
      calc (Fintype.card ι : ℝ) * (1 / s) ^ 2 = ∑ _q : ι, (1 / s) ^ 2 := by simp
        _ ≤ ∑ q, MultiRes_vn (fun p => M p q) ^ 2 :=
          Finset.sum_le_sum fun q _ =>
            pow_le_pow_left₀ (by positivity) (hcol q) 2
    have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hnt' : MultiRes_hs2 M / (Fintype.card ι : ℝ) = m.im / (m.im + z.im) := by
      apply Complex.ofReal_injective
      have := hnt
      simp only [ntr, MultiRes_trace_mul_conjTranspose] at this
      push_cast at this ⊢
      rw [← this]
      field_simp
    have hlow : (1 / s) ^ 2 ≤ m.im / (m.im + z.im) := by
      rw [← hnt', le_div_iff₀ hcard]
      linarith
    have hden : 0 < m.im + z.im := by linarith
    rw [le_div_iff₀ hden] at hlow
    have : (1 / s) ^ 2 * (m.im + z.im) ≤ m.im := hlow
    rw [one_div, inv_pow] at this
    rw [inv_mul_le_iff₀ (by positivity)] at this
    linarith

/-- `ψ ≤ (1 + 2/c₀) Im m` from `N η Im m ≥ c₀`. -/
private lemma MultiRes_psi_le {N : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : 0 < z.im) (hm : 0 < (mSol Λ z).im)
    (hN : c₀ ≤ (N : ℝ) * z.im * (mSol Λ z).im) :
    psiIso Λ N z ≤ (1 + 2 / c₀) * (mSol Λ z).im := by
  have hN0 : 0 < (N : ℝ) := by
    by_contra hcon
    have : (N : ℝ) = 0 := le_antisymm (not_lt.mp hcon) (Nat.cast_nonneg _)
    rw [this] at hN
    simp at hN
    linarith
  set η := z.im
  set μ := (mSol Λ z).im
  have hNη : 0 < (N : ℝ) * η := mul_pos hN0 hz
  have h1 : 1 / ((N : ℝ) * η) ≤ μ / c₀ := by
    rw [div_le_div_iff₀ hNη hc₀]
    linarith
  have hmext : mExt Λ z = mSol Λ z := by
    unfold mExt
    split_ifs with h
    · rfl
    · exact absurd hz h
  unfold psiIso
  rw [hmext, abs_of_pos hz, abs_of_pos hm]
  have h2 : μ / ((N : ℝ) * η) ≤ (μ * (1 + 1 / c₀)) ^ 2 := by
    have h3 : μ / ((N : ℝ) * η) = μ * (1 / ((N : ℝ) * η)) := by ring
    rw [h3]
    have h4 : μ * (1 / ((N : ℝ) * η)) ≤ μ * (μ / c₀) := mul_le_mul_of_nonneg_left h1 hm.le
    refine h4.trans ?_
    have hu : 0 ≤ 1 / c₀ := by positivity
    have : μ * (μ / c₀) = μ ^ 2 * (1 / c₀) := by ring
    rw [this, mul_pow]
    have : 1 / c₀ ≤ (1 + 1 / c₀) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have h5 : Real.sqrt (μ / ((N : ℝ) * η)) ≤ μ * (1 + 1 / c₀) := by
    rw [Real.sqrt_le_left (by positivity)]
    exact h2
  have h6 : 1 / ((N : ℝ) * η) ≤ μ * (1 / c₀) := by
    refine h1.trans (le_of_eq ?_)
    ring
  calc Real.sqrt (μ / ((N : ℝ) * η)) + 1 / ((N : ℝ) * η)
      ≤ μ * (1 + 1 / c₀) + μ * (1 / c₀) := add_le_add h5 h6
    _ = (1 + 2 / c₀) * μ := by ring

end MBounds

section Word

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

/-- `G` or its conjugate transpose, according to the flag. -/
private def MultiRes_Fs (G : Matrix ι ι ℂ) (s : Bool) : Matrix ι ι ℂ := if s then Gᴴ else G

omit [Fintype ι] [DecidableEq ι] in
private lemma MultiRes_Fs_conj (G : Matrix ι ι ℂ) (s : Bool) :
    (MultiRes_Fs G s)ᴴ = MultiRes_Fs G (!s) := by
  cases s <;> simp [MultiRes_Fs]

omit [DecidableEq ι] in
/-- Dot products move a matrix to the other side. -/
private lemma MultiRes_dot_left (A : Matrix ι ι ℂ) (x v : ι → ℂ) :
    star x ⬝ᵥ (A *ᵥ v) = star (Aᴴ *ᵥ x) ⬝ᵥ v := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

private lemma MultiRes_opNorm_list_prod_le (l : List (Matrix ι ι ℂ)) (r : ℝ)
    (h : ∀ X ∈ l, opNorm X ≤ r) : opNorm l.prod ≤ r ^ l.length := by
  induction l with
  | nil => simpa using MultiRes_opNorm_one_le
  | cons X l ih =>
    rw [List.prod_cons, List.length_cons, pow_succ, mul_comm]
    have h1 := h X (by simp)
    have h2 := ih fun Y hY => h Y (by simp [hY])
    refine (opNorm_mul_le _ _).trans ?_
    exact mul_le_mul h1 h2 (MultiRes_opNorm_nonneg _) ((MultiRes_opNorm_nonneg X).trans h1)

private lemma MultiRes_opNorm_ofFn_prod_le {n : ℕ} (X : Fin n → Matrix ι ι ℂ) (r : ℝ)
    (h : ∀ j, opNorm (X j) ≤ r) : opNorm (List.ofFn X).prod ≤ r ^ n := by
  have := MultiRes_opNorm_list_prod_le (List.ofFn X) r (by
    intro Y hY
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hY
    exact h j)
  simpa using this

/-- Splitting off the last factor of an ordered product. -/
private lemma MultiRes_ofFn_split_last {l : ℕ} (X : Fin (l + 1) → Matrix ι ι ℂ) :
    (List.ofFn X).prod = (List.ofFn fun j : Fin l => X j.castSucc).prod * X (Fin.last l) := by
  rw [List.ofFn_succ', List.prod_concat]

/-- Splitting off the first and last factors of an ordered product. -/
private lemma MultiRes_ofFn_split {l : ℕ} (X : Fin (l + 2) → Matrix ι ι ℂ) :
    (List.ofFn X).prod = X 0 * (List.ofFn fun j : Fin l => X j.succ.castSucc).prod *
      X (Fin.last (l + 1)) := by
  rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ', List.prod_concat, Fin.succ_last]
  simp only [Fin.succ_castSucc, Matrix.mul_assoc]

end Word

section Word2

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

/-- The per-resolvent facts used by the word bounds: for the resolvents `G i` with `Im z_i = η i`
and `Im m_i = μ i`, an abstract predicate `Good` on triples (index, left vector, right vector)
implies the Ward-type bound at the ends and the local bound for `p = 1`. -/
private structure MultiRes_WardData (G : Fin p → Matrix ι ι ℂ) (η μ : Fin p → ℝ) (A CL : ℝ)
    (Good : Fin p → (ι → ℂ) → (ι → ℂ) → Prop) : Prop where
  η_pos : ∀ i, 0 < η i
  μ_nonneg : ∀ i, 0 ≤ μ i
  A_nonneg : 0 ≤ A
  CL_nonneg : 0 ≤ CL
  op : ∀ i, opNorm (G i) ≤ (η i)⁻¹
  ward : ∀ i x, Good i x x → ∀ s, MultiRes_vn (MultiRes_Fs (G i) s *ᵥ x) ^ 2 ≤
    A * (μ i / η i) * MultiRes_vn x ^ 2
  loc : ∀ i x y s, Good i (if s then y else x) (if s then x else y) →
    ‖star x ⬝ᵥ (MultiRes_Fs (G i) s *ᵥ y)‖ ≤ CL * MultiRes_vn x * MultiRes_vn y

private lemma MultiRes_WardData.opFs {G : Fin p → Matrix ι ι ℂ} {η μ : Fin p → ℝ} {A CL : ℝ}
    {Good : Fin p → (ι → ℂ) → (ι → ℂ) → Prop} (hD : MultiRes_WardData G η μ A CL Good)
    (i : Fin p) (s : Bool) : opNorm (MultiRes_Fs (G i) s) ≤ (η i)⁻¹ := by
  cases s
  · simpa [MultiRes_Fs] using hD.op i
  · simp only [MultiRes_Fs, ↓reduceIte]
    rw [MultiRes_opNorm_conjTranspose]
    exact hD.op i

/-- Ward bound at one end of a word. -/
private lemma MultiRes_end_bound {G : Fin p → Matrix ι ι ℂ} {η μ : Fin p → ℝ} {A CL : ℝ}
    {Good : Fin p → (ι → ℂ) → (ι → ℂ) → Prop} (hD : MultiRes_WardData G η μ A CL Good)
    (ε β K : ℝ) (hε : 0 < ε) (hεη : ∀ i, ε ≤ η i) (hβ : ∀ i, μ i ≤ β)
    (i : Fin p) (s : Bool) (B : Matrix ι ι ℂ) (hB : opNorm B ≤ K) (x : ι → ℂ)
    (hg : Good i (B *ᵥ x) (B *ᵥ x)) :
    MultiRes_vn (MultiRes_Fs (G i) s *ᵥ (B *ᵥ x)) ≤ Real.sqrt (A * (β / ε)) * (K * MultiRes_vn x) := by
  have hK : 0 ≤ K := (MultiRes_opNorm_nonneg _).trans hB
  have hβ0 : 0 ≤ β := (hD.μ_nonneg i).trans (hβ i)
  have hQ : 0 ≤ A * (β / ε) := mul_nonneg hD.A_nonneg (div_nonneg hβ0 hε.le)
  have h1 := hD.ward i _ hg s
  have h2 : MultiRes_vn (B *ᵥ x) ≤ K * MultiRes_vn x :=
    (MultiRes_vn_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hB (MultiRes_vn_nonneg _))
  have h3 : μ i / η i ≤ β / ε :=
    div_le_div₀ hβ0 (hβ i) hε (hεη i)
  have h4 : MultiRes_vn (MultiRes_Fs (G i) s *ᵥ (B *ᵥ x)) ^ 2 ≤
      (Real.sqrt (A * (β / ε)) * (K * MultiRes_vn x)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hQ]
    refine h1.trans ?_
    have h5 : MultiRes_vn (B *ᵥ x) ^ 2 ≤ (K * MultiRes_vn x) ^ 2 :=
      pow_le_pow_left₀ (MultiRes_vn_nonneg _) h2 2
    calc A * (μ i / η i) * MultiRes_vn (B *ᵥ x) ^ 2
        ≤ A * (β / ε) * MultiRes_vn (B *ᵥ x) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hD.A_nonneg) (sq_nonneg _)
      _ ≤ A * (β / ε) * (K * MultiRes_vn x) ^ 2 := mul_le_mul_of_nonneg_left h5 hQ
  exact (le_abs_self _).trans (abs_le_of_sq_le_sq h4
    (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hK (MultiRes_vn_nonneg _))))

/-- The first end event of a word with `l + 1` resolvents. -/
private def MultiRes_needL (Good : Fin p → (ι → ℂ) → (ι → ℂ) → Prop) :
    {l : ℕ} → (Fin (l + 1) → Fin p × Bool) → (Fin (l + 1 + 1) → Matrix ι ι ℂ) →
      (ι → ℂ) → (ι → ℂ) → Prop
  | 0, w, B, x, y => if (w 0).2 then Good (w 0).1 (B 1 *ᵥ y) ((B 0)ᴴ *ᵥ x)
      else Good (w 0).1 ((B 0)ᴴ *ᵥ x) (B 1 *ᵥ y)
  | _ + 1, w, B, x, _ => Good (w 0).1 ((B 0)ᴴ *ᵥ x) ((B 0)ᴴ *ᵥ x)

/-- The last end event of a word with `l + 1` resolvents. -/
private def MultiRes_needR (Good : Fin p → (ι → ℂ) → (ι → ℂ) → Prop) :
    {l : ℕ} → (Fin (l + 1) → Fin p × Bool) → (Fin (l + 1 + 1) → Matrix ι ι ℂ) →
      (ι → ℂ) → (ι → ℂ) → Prop
  | 0, _, _, _, _ => True
  | l + 1, w, B, _, y => Good (w (Fin.last (l + 1))).1 (B (Fin.last (l + 1 + 1)) *ᵥ y)
      (B (Fin.last (l + 1 + 1)) *ᵥ y)

/-- The event for the one-ended bound of a word with `l + 1` resolvents. -/
private def MultiRes_needW2 (Good : Fin p → (ι → ℂ) → (ι → ℂ) → Prop) {l : ℕ}
    (w : Fin (l + 1) → Fin p × Bool) (B : Fin (l + 1 + 1) → Matrix ι ι ℂ) (y : ι → ℂ) : Prop :=
  Good (w (Fin.last l)).1 (B (Fin.last (l + 1)) *ᵥ y) (B (Fin.last (l + 1)) *ᵥ y)

end Word2

section Word3

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

private lemma MultiRes_W1_one {G : Fin p → Matrix ι ι ℂ} {η μ : Fin p → ℝ} {A CL : ℝ}
    {Good : Fin p → (ι → ℂ) → (ι → ℂ) → Prop} (hD : MultiRes_WardData G η μ A CL Good)
    (K : ℝ) (w : Fin 1 → Fin p × Bool) (B : Fin 2 → Matrix ι ι ℂ) (hB : ∀ j, opNorm (B j) ≤ K)
    (x y : ι → ℂ) (hL : MultiRes_needL Good w B x y) :
    ‖star x ⬝ᵥ (resWord G w B *ᵥ y)‖ ≤ CL * K ^ 2 * (MultiRes_vn x * MultiRes_vn y) := by
  have hK : 0 ≤ K := (MultiRes_opNorm_nonneg _).trans (hB 0)
  have e : resWord G w B = B 0 * (MultiRes_Fs (G (w 0).1) (w 0).2 * B 1) := by
    simp [resWord, List.ofFn_succ, MultiRes_Fs]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, MultiRes_dot_left]
  set a := (B 0)ᴴ *ᵥ x with ha
  set b := B 1 *ᵥ y with hb
  have hva : MultiRes_vn a ≤ K * MultiRes_vn x := by
    refine (MultiRes_vn_mulVec_le _ _).trans ?_
    rw [MultiRes_opNorm_conjTranspose]
    exact mul_le_mul_of_nonneg_right (hB 0) (MultiRes_vn_nonneg _)
  have hvb : MultiRes_vn b ≤ K * MultiRes_vn y :=
    (MultiRes_vn_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right (hB 1) (MultiRes_vn_nonneg _))
  have hloc := hD.loc (w 0).1 a b (w 0).2 (by
    simp only [MultiRes_needL] at hL
    cases h : (w 0).2 <;> simp only [h] at hL ⊢ <;> exact hL)
  have : ‖star a ⬝ᵥ (MultiRes_Fs (G (w 0).1) (w 0).2 *ᵥ b)‖ ≤ CL * MultiRes_vn a * MultiRes_vn b := hloc
  refine this.trans ?_
  have h1 := hD.CL_nonneg
  calc CL * MultiRes_vn a * MultiRes_vn b ≤ CL * (K * MultiRes_vn x) * (K * MultiRes_vn y) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hva h1) hvb (MultiRes_vn_nonneg _)
          (mul_nonneg h1 (mul_nonneg hK (MultiRes_vn_nonneg _)))
    _ = CL * K ^ 2 * (MultiRes_vn x * MultiRes_vn y) := by ring

private lemma MultiRes_W1_ge2 {G : Fin p → Matrix ι ι ℂ} {η μ : Fin p → ℝ} {A CL : ℝ}
    {Good : Fin p → (ι → ℂ) → (ι → ℂ) → Prop} (hD : MultiRes_WardData G η μ A CL Good)
    (ε β K : ℝ) (hε : 0 < ε) (hεη : ∀ i, ε ≤ η i) (hβ : ∀ i, μ i ≤ β) {l : ℕ}
    (w : Fin (l + 1 + 1) → Fin p × Bool) (B : Fin (l + 1 + 1 + 1) → Matrix ι ι ℂ)
    (hB : ∀ j, opNorm (B j) ≤ K) (x y : ι → ℂ)
    (hL : Good (w 0).1 ((B 0)ᴴ *ᵥ x) ((B 0)ᴴ *ᵥ x))
    (hR : Good (w (Fin.last (l + 1))).1 (B (Fin.last (l + 1 + 1)) *ᵥ y)
      (B (Fin.last (l + 1 + 1)) *ᵥ y)) :
    ‖star x ⬝ᵥ (resWord G w B *ᵥ y)‖ ≤
      A * (β / ε) * K ^ (l + 3) / ε ^ l * (MultiRes_vn x * MultiRes_vn y) := by
  have hK : 0 ≤ K := (MultiRes_opNorm_nonneg _).trans (hB 0)
  set X : Fin (l + 1 + 1) → Matrix ι ι ℂ :=
    fun j => MultiRes_Fs (G (w j).1) (w j).2 * B j.succ with hX
  have e : resWord G w B = B 0 * (X 0 * (List.ofFn fun j : Fin l => X j.succ.castSucc).prod *
      X (Fin.last (l + 1))) := by
    change B 0 * (List.ofFn X).prod = _
    rw [MultiRes_ofFn_split]
  set Pm := (List.ofFn fun j : Fin l => X j.succ.castSucc).prod with hPm
  have hXj : ∀ j, opNorm (X j) ≤ ε⁻¹ * K := by
    intro j
    refine (opNorm_mul_le _ _).trans ?_
    have h1 := hD.opFs (w j).1 (w j).2
    have h2 : (η (w j).1)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (hεη _)
    exact mul_le_mul (h1.trans h2) (hB _) (MultiRes_opNorm_nonneg _) (inv_nonneg.mpr hε.le)
  have hPmn : opNorm Pm ≤ (ε⁻¹ * K) ^ l := by
    exact MultiRes_opNorm_ofFn_prod_le (fun j : Fin l => X j.succ.castSucc) (ε⁻¹ * K)
      (fun j => hXj _)
  set c := (B 0)ᴴ *ᵥ x with hc
  set d := B (Fin.last (l + 1 + 1)) *ᵥ y with hd
  have hXl : X (Fin.last (l + 1)) *ᵥ y =
      MultiRes_Fs (G (w (Fin.last (l + 1))).1) (w (Fin.last (l + 1))).2 *ᵥ d := by
    simp only [hX]
    rw [Fin.succ_last, ← Matrix.mulVec_mulVec]
  have hX0 : X 0 = MultiRes_Fs (G (w 0).1) (w 0).2 * B 1 := by
    simp [hX]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    MultiRes_dot_left, hXl, hX0, ← Matrix.mulVec_mulVec, MultiRes_dot_left]
  set Q := A * (β / ε) with hQdef
  have hβ0 : 0 ≤ β := (hD.μ_nonneg (w 0).1).trans (hβ _)
  have hQ : 0 ≤ Q := mul_nonneg hD.A_nonneg (div_nonneg hβ0 hε.le)
  have hB0 : opNorm (B 0)ᴴ ≤ K := by rw [MultiRes_opNorm_conjTranspose]; exact hB 0
  have hv1 : MultiRes_vn ((MultiRes_Fs (G (w 0).1) (w 0).2)ᴴ *ᵥ c) ≤
      Real.sqrt Q * (K * MultiRes_vn x) := by
    rw [MultiRes_Fs_conj]
    exact MultiRes_end_bound hD ε β K hε hεη hβ (w 0).1 _ _ hB0 x hL
  have hv2 : MultiRes_vn (MultiRes_Fs (G (w (Fin.last (l + 1))).1) (w (Fin.last (l + 1))).2 *ᵥ d) ≤
      Real.sqrt Q * (K * MultiRes_vn y) :=
    MultiRes_end_bound hD ε β K hε hεη hβ _ _ _ (hB _) y hR
  generalize hFl : MultiRes_Fs (G (w (Fin.last (l + 1))).1) (w (Fin.last (l + 1))).2 *ᵥ d = Fl
    at hv2 ⊢
  have hn1 := MultiRes_norm_dot_le
    ((MultiRes_Fs (G (w 0).1) (w 0).2)ᴴ *ᵥ c) (B 1 *ᵥ (Pm *ᵥ Fl))
  have hr1 : MultiRes_vn (Pm *ᵥ Fl) ≤ (ε⁻¹ * K) ^ l * MultiRes_vn Fl :=
    (MultiRes_vn_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hPmn (MultiRes_vn_nonneg _))
  have hr0 : MultiRes_vn (B 1 *ᵥ (Pm *ᵥ Fl)) ≤ K * ((ε⁻¹ * K) ^ l * MultiRes_vn Fl) :=
    (MultiRes_vn_mulVec_le _ _).trans
      (mul_le_mul (hB 1) hr1 (MultiRes_vn_nonneg _) hK)
  have hεK : 0 ≤ ε⁻¹ * K := mul_nonneg (inv_nonneg.mpr hε.le) hK
  have hs := Real.sqrt_nonneg Q
  have hvx := MultiRes_vn_nonneg x
  have hvy := MultiRes_vn_nonneg y
  have hfin : Real.sqrt Q * (K * MultiRes_vn x) *
      (K * ((ε⁻¹ * K) ^ l * (Real.sqrt Q * (K * MultiRes_vn y)))) =
      A * (β / ε) * K ^ (l + 3) / ε ^ l * (MultiRes_vn x * MultiRes_vn y) := by
    have hs2 : Real.sqrt Q * Real.sqrt Q = A * (β / ε) := Real.mul_self_sqrt hQ
    rw [mul_pow, inv_pow, div_eq_mul_inv, ← hs2]
    ring
  refine hn1.trans (le_trans ?_ hfin.le)
  refine mul_le_mul hv1 (hr0.trans ?_) (MultiRes_vn_nonneg _)
    (mul_nonneg hs (mul_nonneg hK hvx))
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv2 (pow_nonneg hεK _)) hK

/-- The bilinear word bound: `|x^* B₀ G^{s_1} B₁ ⋯ G^{s_L} B_L y| ≲ (max Im m)^{1(L ≥ 2)} ε^{-(L-1)}`. -/
private lemma MultiRes_W1 {G : Fin p → Matrix ι ι ℂ} {η μ : Fin p → ℝ} {A CL : ℝ}
    {Good : Fin p → (ι → ℂ) → (ι → ℂ) → Prop} (hD : MultiRes_WardData G η μ A CL Good)
    (ε β K : ℝ) (hε : 0 < ε) (hεη : ∀ i, ε ≤ η i) (hβ : ∀ i, μ i ≤ β) {l : ℕ}
    (w : Fin (l + 1) → Fin p × Bool) (B : Fin (l + 1 + 1) → Matrix ι ι ℂ)
    (hB : ∀ j, opNorm (B j) ≤ K) (x y : ι → ℂ)
    (hL : MultiRes_needL Good w B x y) (hR : MultiRes_needR Good w B x y) :
    ‖star x ⬝ᵥ (resWord G w B *ᵥ y)‖ ≤
      (A + CL) * K ^ (l + 2) * ((if 2 ≤ l + 1 then β else 1) / ε ^ l) *
        (MultiRes_vn x * MultiRes_vn y) := by
  have hK : 0 ≤ K := (MultiRes_opNorm_nonneg _).trans (hB 0)
  have hvv : 0 ≤ MultiRes_vn x * MultiRes_vn y :=
    mul_nonneg (MultiRes_vn_nonneg _) (MultiRes_vn_nonneg _)
  have hA := hD.A_nonneg
  have hCL := hD.CL_nonneg
  cases l with
  | zero =>
    have h := MultiRes_W1_one hD K w B hB x y hL
    simp only [Nat.zero_add, Nat.not_ofNat_le_one, ↓reduceIte, pow_zero, div_one, mul_one]
    refine h.trans ?_
    have : CL * K ^ 2 ≤ (A + CL) * K ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right this hvv
  | succ l' =>
    have h := MultiRes_W1_ge2 hD ε β K hε hεη hβ w B hB x y hL hR
    have hβ0 : 0 ≤ β := (hD.μ_nonneg (w 0).1).trans (hβ _)
    have h2 : 2 ≤ l' + 1 + 1 := by omega
    simp only [h2, ↓reduceIte]
    refine h.trans ?_
    have e : (A + CL) * K ^ (l' + 1 + 2) * (β / ε ^ (l' + 1)) =
        A * (β / ε) * K ^ (l' + 3) / ε ^ l' + CL * K ^ (l' + 3) * (β / ε ^ (l' + 1)) := by
      rw [pow_succ]
      field_simp
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ hvv
    have : 0 ≤ CL * K ^ (l' + 3) * (β / ε ^ (l' + 1)) :=
      mul_nonneg (mul_nonneg hCL (pow_nonneg hK _)) (div_nonneg hβ0 (pow_nonneg hε.le _))
    linarith

/-- The one-ended word bound `‖W y‖² ≲ β ε^{-(2L-1)}`. -/
private lemma MultiRes_W2 {G : Fin p → Matrix ι ι ℂ} {η μ : Fin p → ℝ} {A CL : ℝ}
    {Good : Fin p → (ι → ℂ) → (ι → ℂ) → Prop} (hD : MultiRes_WardData G η μ A CL Good)
    (ε β K : ℝ) (hε : 0 < ε) (hεη : ∀ i, ε ≤ η i) (hβ : ∀ i, μ i ≤ β) {l : ℕ}
    (w : Fin (l + 1) → Fin p × Bool) (B : Fin (l + 1 + 1) → Matrix ι ι ℂ)
    (hB : ∀ j, opNorm (B j) ≤ K) (y : ι → ℂ) (hR : MultiRes_needW2 Good w B y) :
    MultiRes_vn (resWord G w B *ᵥ y) ^ 2 ≤
      A * (β / ε) * K ^ (2 * l + 4) / ε ^ (2 * l) * MultiRes_vn y ^ 2 := by
  have hK : 0 ≤ K := (MultiRes_opNorm_nonneg _).trans (hB 0)
  set X : Fin (l + 1) → Matrix ι ι ℂ :=
    fun j => MultiRes_Fs (G (w j).1) (w j).2 * B j.succ with hX
  have e : resWord G w B = B 0 * ((List.ofFn fun j : Fin l => X j.castSucc).prod *
      X (Fin.last l)) := by
    change B 0 * (List.ofFn X).prod = _
    rw [MultiRes_ofFn_split_last]
  set Pm := (List.ofFn fun j : Fin l => X j.castSucc).prod with hPm
  have hXj : ∀ j, opNorm (X j) ≤ ε⁻¹ * K := by
    intro j
    refine (opNorm_mul_le _ _).trans ?_
    have h1 := hD.opFs (w j).1 (w j).2
    have h2 : (η (w j).1)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (hεη _)
    exact mul_le_mul (h1.trans h2) (hB _) (MultiRes_opNorm_nonneg _) (inv_nonneg.mpr hε.le)
  have hPmn : opNorm Pm ≤ (ε⁻¹ * K) ^ l :=
    MultiRes_opNorm_ofFn_prod_le (fun j : Fin l => X j.castSucc) (ε⁻¹ * K) (fun j => hXj _)
  set d := B (Fin.last (l + 1)) *ᵥ y with hd
  have hXl : X (Fin.last l) *ᵥ y =
      MultiRes_Fs (G (w (Fin.last l)).1) (w (Fin.last l)).2 *ᵥ d := by
    simp only [hX]
    rw [Fin.succ_last, ← Matrix.mulVec_mulVec]
  set Q := A * (β / ε) with hQdef
  have hβ0 : 0 ≤ β := (hD.μ_nonneg (w 0).1).trans (hβ _)
  have hQ : 0 ≤ Q := mul_nonneg hD.A_nonneg (div_nonneg hβ0 hε.le)
  have hv2 : MultiRes_vn (MultiRes_Fs (G (w (Fin.last l)).1) (w (Fin.last l)).2 *ᵥ d) ≤
      Real.sqrt Q * (K * MultiRes_vn y) :=
    MultiRes_end_bound hD ε β K hε hεη hβ _ _ _ (hB _) y hR
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hXl]
  generalize hFl : MultiRes_Fs (G (w (Fin.last l)).1) (w (Fin.last l)).2 *ᵥ d = Fl at hv2 ⊢
  have hr1 : MultiRes_vn (Pm *ᵥ Fl) ≤ (ε⁻¹ * K) ^ l * MultiRes_vn Fl :=
    (MultiRes_vn_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hPmn (MultiRes_vn_nonneg _))
  have hr0 : MultiRes_vn (B 0 *ᵥ (Pm *ᵥ Fl)) ≤ K * ((ε⁻¹ * K) ^ l * MultiRes_vn Fl) :=
    (MultiRes_vn_mulVec_le _ _).trans
      (mul_le_mul (hB 0) hr1 (MultiRes_vn_nonneg _) hK)
  have hεK : 0 ≤ ε⁻¹ * K := mul_nonneg (inv_nonneg.mpr hε.le) hK
  have hvy := MultiRes_vn_nonneg y
  have hs := Real.sqrt_nonneg Q
  have hr2 : MultiRes_vn (B 0 *ᵥ (Pm *ᵥ Fl)) ≤
      K * ((ε⁻¹ * K) ^ l * (Real.sqrt Q * (K * MultiRes_vn y))) :=
    hr0.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv2 (pow_nonneg hεK _)) hK)
  have hsq := pow_le_pow_left₀ (MultiRes_vn_nonneg _) hr2 2
  refine hsq.trans (le_of_eq ?_)
  have hs2 : Real.sqrt Q * Real.sqrt Q = A * (β / ε) := Real.mul_self_sqrt hQ
  have e2 : (K * ((ε⁻¹ * K) ^ l * (Real.sqrt Q * (K * MultiRes_vn y)))) ^ 2 =
      (Real.sqrt Q * Real.sqrt Q) * K ^ (2 * l + 4) * (ε⁻¹) ^ (2 * l) * MultiRes_vn y ^ 2 := by
    ring
  rw [e2, hs2, inv_pow]
  ring

end Word3

section Good

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The event that the anisotropic local law (2.22) holds for `G - M` at the pair `(x, y)`, with the
exponent `t`. -/
private def MultiRes_GoodV (N : ℕ) (t : ℝ) (X Λ : Matrix ι ι ℂ) (z : ℂ) (x y : ι → ℂ) : Prop :=
  ‖star x ⬝ᵥ ((res X z - MSol Λ z) *ᵥ y)‖ ≤
    (N : ℝ) ^ t * psiIso Λ N z * (MultiRes_vn x * MultiRes_vn y)

private lemma MultiRes_nonempty_of_hZ {N : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) (Λ : Matrix ι ι ℂ) (z : ℂ)
    (h : c₀ ≤ (N : ℝ) * z.im * (mSol Λ z).im) : Nonempty ι := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have h0 : mSol Λ z = 0 := by
    unfold mSol
    split_ifs with h
    · exfalso
      obtain ⟨w, hw, hw'⟩ := h
      have : ntr (Λ - (z + w) • (1 : Matrix ι ι ℂ))⁻¹ = 0 := by
        simp [ntr, Fintype.card_eq_zero]
      rw [this] at hw'
      rw [hw'] at hw
      simp at hw
    · rfl
  rw [h0] at h
  simp at h
  linarith

/-- The constants of the word bounds. -/
private def MultiRes_Ct (τ : ℝ) : ℝ := (11 / 10 + τ⁻¹) ^ 2

private def MultiRes_CPsi (c₀ : ℝ) : ℝ := 1 + 2 / c₀

private def MultiRes_CG (τ c₀ : ℝ) : ℝ := 25 / 16 * MultiRes_Ct τ + MultiRes_CPsi c₀

private def MultiRes_CW (τ c₀ : ℝ) : ℝ := MultiRes_CG τ c₀ + MultiRes_CPsi c₀ + 5 / 4

private lemma MultiRes_Ct_nonneg (τ : ℝ) : 0 ≤ MultiRes_Ct τ := sq_nonneg _

private lemma MultiRes_CPsi_pos {c₀ : ℝ} (hc₀ : 0 < c₀) : 0 < MultiRes_CPsi c₀ := by
  unfold MultiRes_CPsi; positivity

private lemma MultiRes_CG_pos {τ c₀ : ℝ} (hc₀ : 0 < c₀) : 0 < MultiRes_CG τ c₀ := by
  have := MultiRes_Ct_nonneg τ
  have := MultiRes_CPsi_pos hc₀
  unfold MultiRes_CG; positivity

/-- The deterministic facts behind the word bounds: Ward's identity and the a priori bounds on `M`
turn the event "(2.22) holds" into the data used by the word bounds. -/
private lemma MultiRes_wardData [Nonempty ι] {p : ℕ} (τ c₀ : ℝ) (hc₀ : 0 < c₀) (N : ℕ)
    (hN : 1 ≤ N) (t : ℝ) (ht : 0 ≤ t) (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (Λ : Fin p → Matrix ι ι ℂ)
    (hΛh : ∀ i, (Λ i).IsHermitian) (hΛn : ∀ i, opNorm (Λ i) ≤ 1 / 10) (z : Fin p → ℂ)
    (hz : ∀ i, 0 < (z i).im ∧ ‖z i‖ ≤ τ⁻¹ ∧ c₀ ≤ (N : ℝ) * (z i).im * (mSol (Λ i) (z i)).im) :
    MultiRes_WardData (fun i => res (H + Λ i) (z i)) (fun i => (z i).im)
      (fun i => (mSol (Λ i) (z i)).im) (MultiRes_CG τ c₀ * (N : ℝ) ^ t)
      (MultiRes_CPsi c₀ * (N : ℝ) ^ t + 5 / 4)
      (fun i x y => MultiRes_GoodV N t (H + Λ i) (Λ i) (z i) x y) := by
  have hT : 1 ≤ (N : ℝ) ^ t := Real.one_le_rpow (by exact_mod_cast hN) ht
  have hCΨ := MultiRes_CPsi_pos hc₀
  have hCG := MultiRes_CG_pos (τ := τ) hc₀
  have hM := fun i => MultiRes_Mbounds (Λ i) (hΛh i) (hΛn i) τ (z i) (hz i).1 (hz i).2.1
  have hψ := fun i => MultiRes_psi_le hc₀ (Λ i) (z i) (hz i).1 (hM i).2.1 (hz i).2.2
  have hHΛ := fun i => hH.add (hΛh i)
  refine ⟨fun i => (hz i).1, fun i => (hM i).2.1.le, mul_nonneg hCG.le (by linarith),
    by positivity, fun i => opNorm_res_le _ (hHΛ i) _ (hz i).1, ?_, ?_⟩
  · intro i x hg s
    obtain ⟨w1, w2⟩ := MultiRes_ward_vec (H + Λ i) (hHΛ i) (z i) (hz i).1 x
    obtain ⟨hM54, hμ0, hμ1, hMim, hCt⟩ := hM i
    have hη := (hz i).1
    set G := res (H + Λ i) (z i) with hG
    set M := MSol (Λ i) (z i) with hMdef
    set μ := (mSol (Λ i) (z i)).im with hμ
    set η := (z i).im with hηdef
    have hqG : star x ⬝ᵥ (G *ᵥ x) =
        star x ⬝ᵥ ((G - M) *ᵥ x) + star x ⬝ᵥ (M *ᵥ x) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, sub_add_cancel]
    have h1 : (star x ⬝ᵥ ((G - M) *ᵥ x)).im ≤ (N : ℝ) ^ t * psiIso (Λ i) N (z i) *
        (MultiRes_vn x * MultiRes_vn x) :=
      ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans hg
    have h2 := hMim x
    have h3 : (N : ℝ) ^ t * psiIso (Λ i) N (z i) ≤ (N : ℝ) ^ t * (MultiRes_CPsi c₀ * μ) :=
      mul_le_mul_of_nonneg_left (hψ i) (by linarith)
    have hvx := MultiRes_vn_nonneg x
    have h4 : (star x ⬝ᵥ (G *ᵥ x)).im ≤ MultiRes_CG τ c₀ * (N : ℝ) ^ t * μ * MultiRes_vn x ^ 2 := by
      rw [hqG, Complex.add_im]
      have h5 : 25 / 16 * (η + μ) ≤ 25 / 16 * (MultiRes_Ct τ * μ) := by
        have : η + μ ≤ MultiRes_Ct τ * μ := hCt
        linarith
      have h6 : 25 / 16 * (η + μ) * MultiRes_vn x ^ 2 ≤
          25 / 16 * (MultiRes_Ct τ * μ) * MultiRes_vn x ^ 2 :=
        mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
      have h7 : (N : ℝ) ^ t * psiIso (Λ i) N (z i) * (MultiRes_vn x * MultiRes_vn x) ≤
          (N : ℝ) ^ t * (MultiRes_CPsi c₀ * μ) * (MultiRes_vn x * MultiRes_vn x) :=
        mul_le_mul_of_nonneg_right h3 (mul_self_nonneg _)
      have hCt0 := MultiRes_Ct_nonneg τ
      have hmv : 0 ≤ μ * MultiRes_vn x ^ 2 := mul_nonneg hμ0.le (sq_nonneg _)
      have h8 : 25 / 16 * (MultiRes_Ct τ * μ) * MultiRes_vn x ^ 2 ≤
          25 / 16 * MultiRes_Ct τ * (N : ℝ) ^ t * μ * MultiRes_vn x ^ 2 := by
        have : 25 / 16 * MultiRes_Ct τ * μ * MultiRes_vn x ^ 2 * 1 ≤
            25 / 16 * MultiRes_Ct τ * μ * MultiRes_vn x ^ 2 * (N : ℝ) ^ t :=
          mul_le_mul_of_nonneg_left hT (by positivity)
        nlinarith
      unfold MultiRes_CG
      nlinarith [h6, h7, h8, h1, h2]
    have hbound : ∀ V : ℝ, η * V = (star x ⬝ᵥ (G *ᵥ x)).im →
        V ≤ MultiRes_CG τ c₀ * (N : ℝ) ^ t * (μ / η) * MultiRes_vn x ^ 2 := by
      intro V hV
      have : η * V ≤ MultiRes_CG τ c₀ * (N : ℝ) ^ t * μ * MultiRes_vn x ^ 2 := by
        rw [hV]; exact h4
      have e : MultiRes_CG τ c₀ * (N : ℝ) ^ t * (μ / η) * MultiRes_vn x ^ 2 =
          MultiRes_CG τ c₀ * (N : ℝ) ^ t * μ * MultiRes_vn x ^ 2 / η := by ring
      rw [e, le_div_iff₀ hη]
      linarith
    cases s
    · exact hbound _ (by simpa [MultiRes_Fs] using w1)
    · exact hbound _ (by simpa [MultiRes_Fs] using w2)
  · intro i x y s hg
    obtain ⟨hM54, hμ0, hμ1, hMim, hCt⟩ := hM i
    set G := res (H + Λ i) (z i) with hG
    set M := MSol (Λ i) (z i) with hMdef
    set μ := (mSol (Λ i) (z i)).im with hμ
    have hloc : ∀ x y : ι → ℂ, MultiRes_GoodV N t (H + Λ i) (Λ i) (z i) x y →
        ‖star x ⬝ᵥ (G *ᵥ y)‖ ≤ (MultiRes_CPsi c₀ * (N : ℝ) ^ t + 5 / 4) * MultiRes_vn x *
          MultiRes_vn y := by
      intro x y hg
      have e : star x ⬝ᵥ (G *ᵥ y) = star x ⬝ᵥ ((G - M) *ᵥ y) + star x ⬝ᵥ (M *ᵥ y) := by
        rw [Matrix.sub_mulVec, dotProduct_sub, sub_add_cancel]
      have h1 : ‖star x ⬝ᵥ (M *ᵥ y)‖ ≤ MultiRes_vn x * (5 / 4 * MultiRes_vn y) :=
        (MultiRes_norm_dot_le _ _).trans (mul_le_mul_of_nonneg_left
          ((MultiRes_vn_mulVec_le M y).trans
            (mul_le_mul_of_nonneg_right hM54 (MultiRes_vn_nonneg _))) (MultiRes_vn_nonneg _))
      have h2 : (N : ℝ) ^ t * psiIso (Λ i) N (z i) ≤ (N : ℝ) ^ t * MultiRes_CPsi c₀ := by
        refine mul_le_mul_of_nonneg_left ((hψ i).trans ?_) (by linarith)
        unfold MultiRes_CPsi
        have : 0 ≤ 1 + 2 / c₀ := by positivity
        nlinarith
      have hvx := MultiRes_vn_nonneg x
      have hvy := MultiRes_vn_nonneg y
      calc ‖star x ⬝ᵥ (G *ᵥ y)‖
          ≤ ‖star x ⬝ᵥ ((G - M) *ᵥ y)‖ + ‖star x ⬝ᵥ (M *ᵥ y)‖ := by
            rw [e]; exact norm_add_le _ _
        _ ≤ (N : ℝ) ^ t * psiIso (Λ i) N (z i) * (MultiRes_vn x * MultiRes_vn y) +
            MultiRes_vn x * (5 / 4 * MultiRes_vn y) := add_le_add hg h1
        _ ≤ (N : ℝ) ^ t * MultiRes_CPsi c₀ * (MultiRes_vn x * MultiRes_vn y) +
            MultiRes_vn x * (5 / 4 * MultiRes_vn y) := by
            gcongr
        _ ≤ (MultiRes_CPsi c₀ * (N : ℝ) ^ t + 5 / 4) * MultiRes_vn x * MultiRes_vn y := by
            nlinarith [mul_nonneg hvx hvy]
    cases s
    · have hg' : MultiRes_GoodV N t (H + Λ i) (Λ i) (z i) x y := by simpa using hg
      simpa [MultiRes_Fs] using hloc x y hg'
    · have hg' : MultiRes_GoodV N t (H + Λ i) (Λ i) (z i) y x := by simpa using hg
      have h := hloc y x hg'
      have e : star x ⬝ᵥ (MultiRes_Fs G true *ᵥ y) = star (star y ⬝ᵥ (G *ᵥ x)) := by
        rw [MultiRes_star_dot_conj]; rfl
      rw [e, norm_star]
      calc ‖star y ⬝ᵥ (G *ᵥ x)‖ ≤ _ := h
        _ = _ := by ring

end Good

section Prob

set_option linter.unusedSectionVars false

private lemma MultiRes_pow_ge (C τ' : ℝ) (hτ' : 0 < τ') :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → C ≤ (N : ℝ) ^ τ' := by
  have h := (tendsto_rpow_atTop hτ').comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (h.eventually_ge_atTop C)
  exact ⟨N₁, hN₁⟩

/-- A finite union of events, off a null set. -/
private lemma MultiRes_union {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {κ : Type*}
    [Fintype κ] (E : κ → Set Ω) (δ : ENNReal) (hE : ∀ k, P (E k) ≤ δ) (Z0 S : Set Ω)
    (hZ0 : P Z0 = 0) (hS : ∀ ω, ω ∉ Z0 → (∀ k, ω ∉ E k) → ω ∉ S) :
    P S ≤ (Fintype.card κ : ENNReal) * δ := by
  have hsub : S ⊆ Z0 ∪ ⋃ k, E k := by
    intro ω hω
    by_contra hcon
    rw [Set.mem_union, not_or, Set.mem_iUnion, not_exists] at hcon
    exact hS ω hcon.1 hcon.2 hω
  calc P S ≤ P (Z0 ∪ ⋃ k, E k) := measure_mono hsub
    _ ≤ P Z0 + P (⋃ k, E k) := measure_union_le _ _
    _ ≤ 0 + ∑ k, P (E k) := by
        rw [hZ0]; exact add_le_add le_rfl (measure_iUnion_fintype_le _ _)
    _ ≤ 0 + ∑ _k : κ, δ := add_le_add le_rfl (Finset.sum_le_sum fun k _ => hE k)
    _ = (Fintype.card κ : ENNReal) * δ := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The union bound costs `m ≤ N²` events of probability `N^{-D'-2}`. -/
private lemma MultiRes_card_mul_le (m N : ℕ) (hN : 1 ≤ N) (hm : m ≤ N * N) (D' : ℝ) :
    (m : ENNReal) * ENNReal.ofReal ((N : ℝ) ^ (-(D' + 2))) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (N : ℝ) ^ (-(D' + 2)) = (N : ℝ) ^ (-D') * ((N : ℝ) ^ 2)⁻¹ := by
    have e2 : (N : ℝ) ^ (-2 : ℝ) = ((N : ℝ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hN0.le, Real.rpow_two]
    rw [show -(D' + 2) = -D' + (-2 : ℝ) by ring, Real.rpow_add hN0, e2]
  rw [e]
  have h1 : (m : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : (m : ℝ) ≤ (N * N : ℕ) := by exact_mod_cast hm
    simpa [sq] using this
  have h2 : 0 ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg hN0.le _
  calc (m : ℝ) * ((N : ℝ) ^ (-D') * ((N : ℝ) ^ 2)⁻¹)
      = (m : ℝ) / (N : ℝ) ^ 2 * (N : ℝ) ^ (-D') := by ring
    _ ≤ 1 * (N : ℝ) ^ (-D') := by
        refine mul_le_mul_of_nonneg_right ?_ h2
        rw [div_le_one (by positivity)]
        exact h1
    _ = (N : ℝ) ^ (-D') := one_mul _

end Prob

section Prob2

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- (2.22) for unit vectors gives the bound for arbitrary vectors with the factor `‖x‖‖y‖`. -/
private lemma MultiRes_bad_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → Matrix ι ι ℂ) (θ : ℝ) (δ : ENNReal)
    (hu : ∀ u v : ι → ℂ, MultiRes_vn u = 1 → MultiRes_vn v = 1 →
      P {ω | θ < ‖star u ⬝ᵥ (f ω *ᵥ v)‖} ≤ δ) (x y : ι → ℂ) :
    P {ω | θ * (MultiRes_vn x * MultiRes_vn y) < ‖star x ⬝ᵥ (f ω *ᵥ y)‖} ≤ δ := by
  by_cases hx : MultiRes_vn x = 0
  · have hx0 : x = 0 := MultiRes_vn_eq_zero hx
    have : {ω | θ * (MultiRes_vn x * MultiRes_vn y) < ‖star x ⬝ᵥ (f ω *ᵥ y)‖} = ∅ := by
      ext ω
      simp [hx0, MultiRes_vn_zero]
    rw [this]; simp
  by_cases hy : MultiRes_vn y = 0
  · have hy0 : y = 0 := MultiRes_vn_eq_zero hy
    have : {ω | θ * (MultiRes_vn x * MultiRes_vn y) < ‖star x ⬝ᵥ (f ω *ᵥ y)‖} = ∅ := by
      ext ω
      simp [hy0, MultiRes_vn_zero]
    rw [this]; simp
  have hxp : 0 < MultiRes_vn x := lt_of_le_of_ne (MultiRes_vn_nonneg _) (Ne.symm hx)
  have hyp : 0 < MultiRes_vn y := lt_of_le_of_ne (MultiRes_vn_nonneg _) (Ne.symm hy)
  set x' : ι → ℂ := (((MultiRes_vn x)⁻¹ : ℝ) : ℂ) • x with hx'
  set y' : ι → ℂ := (((MultiRes_vn y)⁻¹ : ℝ) : ℂ) • y with hy'
  have hvx' : MultiRes_vn x' = 1 := by
    rw [hx', MultiRes_vn_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxp),
      inv_mul_cancel₀ hx]
  have hvy' : MultiRes_vn y' = 1 := by
    rw [hy', MultiRes_vn_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyp),
      inv_mul_cancel₀ hy]
  have hq : ∀ ω, ‖star x' ⬝ᵥ (f ω *ᵥ y')‖ =
      ‖star x ⬝ᵥ (f ω *ᵥ y)‖ / (MultiRes_vn x * MultiRes_vn y) := by
    intro ω
    have : star x' ⬝ᵥ (f ω *ᵥ y') =
        ((((MultiRes_vn x)⁻¹ * (MultiRes_vn y)⁻¹ : ℝ)) : ℂ) * (star x ⬝ᵥ (f ω *ᵥ y)) := by
      simp only [hx', hy', Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, Pi.star_apply,
        star_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (inv_pos.mpr hxp) (inv_pos.mpr hyp))]
    field_simp
  have hset : {ω | θ * (MultiRes_vn x * MultiRes_vn y) < ‖star x ⬝ᵥ (f ω *ᵥ y)‖} =
      {ω | θ < ‖star x' ⬝ᵥ (f ω *ᵥ y')‖} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hq]
    rw [lt_div_iff₀ (mul_pos hxp hyp)]
  rw [hset]
  exact hu x' y' hvx' hvy'

end Prob2

/-- The probabilistic core: from the anisotropic local law (2.22) at all `(i, u, v)`, for `N` large and
`z ∈ Z N`: the events "(2.22) fails at `(x, y)`" have probability at most `N^{-D'-2}`, and off the
non-Hermitian null set the deterministic word bounds hold. -/
private theorem MultiRes_core {D p : ℕ} (hp : 1 ≤ p) (τ c₀ : ℝ) (hc₀ : 0 < c₀)
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    (H : ∀ N, Ω N → Matrix (Idx D N) (Idx D N) ℂ)
    (Λs : ∀ N, Fin p → Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : ∀ N i, (Λs N i).IsHermitian ∧ opNorm (Λs N i) ≤ 1 / 10)
    (Z : ∀ N, Set (Fin p → ℂ))
    (hZ : ∀ N : ℕ, ∀ z ∈ Z N, ∀ i, 0 < (z i).im ∧ ‖z i‖ ≤ τ⁻¹ ∧
      c₀ ≤ (N : ℝ) * (z i).im * (mSol (Λs N i) (z i)).im)
    (hLL : ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ z ∈ Z N, ∀ i, ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
        P N {ω | (N : ℝ) ^ τ' * psiIso (Λs N i) N (z i) <
            ‖star u ⬝ᵥ ((res (H N ω + Λs N i) (z i) - MSol (Λs N i) (z i)) *ᵥ v)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')))
    (τ' : ℝ) (hτ' : 0 < τ') (D' : ℝ) (hD' : 0 < D') :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z ∈ Z N, 1 ≤ N ∧ Nonempty (Idx D N) ∧
      (∀ (i : Fin p) (x y : Idx D N → ℂ),
        P N {ω | ¬ MultiRes_GoodV N (τ' / 2) (H N ω + Λs N i) (Λs N i) (z i) x y} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-(D' + 2)))) ∧
      (∀ ω, (H N ω).IsHermitian →
        MultiRes_WardData (fun i => res (H N ω + Λs N i) (z i)) (fun i => (z i).im)
          (fun i => (mSol (Λs N i) (z i)).im)
          (MultiRes_CG τ c₀ * (N : ℝ) ^ (τ' / 2)) (MultiRes_CPsi c₀ * (N : ℝ) ^ (τ' / 2) + 5 / 4)
          (fun i x y => MultiRes_GoodV N (τ' / 2) (H N ω + Λs N i) (Λs N i) (z i) x y)) := by
  obtain ⟨N₁, hN₁⟩ := hLL (τ' / 2) (by positivity) (D' + 2) (by positivity)
  refine ⟨N₁, fun N hN z hzN => ?_⟩
  have h0 := hZ N z hzN ⟨0, hp⟩
  have hN1 : 1 ≤ N := by
    by_contra hcon
    have hN0 : N = 0 := by omega
    have := h0.2.2
    rw [hN0] at this
    simp at this
    linarith
  have hne : Nonempty (Idx D N) := MultiRes_nonempty_of_hZ hc₀ _ _ h0.2.2
  refine ⟨hN1, hne, ?_, ?_⟩
  · intro i x y
    have h := MultiRes_bad_prob (P N)
      (fun ω => res (H N ω + Λs N i) (z i) - MSol (Λs N i) (z i))
      ((N : ℝ) ^ (τ' / 2) * psiIso (Λs N i) N (z i)) (ENNReal.ofReal ((N : ℝ) ^ (-(D' + 2))))
      (fun u v hu hv => by
        refine hN₁ N hN z hzN i u v ?_ ?_
        · rw [← MultiRes_vn_sq, hu]; norm_num
        · rw [← MultiRes_vn_sq, hv]; norm_num) x y
    simpa [MultiRes_GoodV, not_le] using h
  · intro ω hω
    exact MultiRes_wardData τ c₀ hc₀ N hN1 (τ' / 2) (by positivity) (H N ω) hω (Λs N)
      (fun i => (hΛ N i).1) (fun i => (hΛ N i).2) z (fun i => hZ N z hzN i)

section Lam

set_option linter.unusedSectionVars false

private lemma MultiRes_fwd_functional {D : ℕ} {a b b' : Fin D} (h : fwd D a b) (h' : fwd D a b') :
    b = b' := by
  unfold fwd at h h'
  apply Fin.ext
  omega

private lemma MultiRes_fwd_injective {D : ℕ} {a a' b : Fin D} (h : fwd D a b) (h' : fwd D a' b) :
    a = a' := by
  unfold fwd at h h'
  apply Fin.ext
  omega

private lemma MultiRes_fwd_irrefl {D : ℕ} (a : Fin D) : ¬ fwd D a a := by
  unfold fwd
  have := a.isLt
  omega

/-- The block-upper part of `lam D N A`. -/
private def MultiRes_S1 (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  fun p q => if fwd D p.1 q.1 then A p.2 q.2 else 0

private lemma MultiRes_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = MultiRes_S1 D N A + (MultiRes_S1 D N A)ᴴ := by
  ext p q
  by_cases h : fwd D q.1 p.1 <;> simp [lam, MultiRes_S1, Matrix.conjTranspose_apply, h]

/-- A sum over `b` with at most one nonzero term. -/
private lemma MultiRes_sum_ite_sq {D N : ℕ} (a : Fin D) (f : Fin D → Fin N → ℂ) :
    MultiRes_vn (∑ b, (if fwd D a b then f b else 0)) ^ 2 =
      ∑ b, (if fwd D a b then MultiRes_vn (f b) ^ 2 else 0) := by
  by_cases h : ∃ b₀, fwd D a b₀
  · obtain ⟨b₀, hb₀⟩ := h
    rw [Finset.sum_eq_single b₀, Finset.sum_eq_single b₀]
    · simp [hb₀]
    · intro b _ hb
      have : ¬ fwd D a b := fun h' => hb (MultiRes_fwd_functional h' hb₀)
      simp [this]
    · simp
    · intro b _ hb
      have : ¬ fwd D a b := fun h' => hb (MultiRes_fwd_functional h' hb₀)
      simp [this]
    · simp
  · have h' : ∀ b, ¬ fwd D a b := fun b hb => h ⟨b, hb⟩
    simp [h', MultiRes_vn_zero]

private lemma MultiRes_sum_ite_le {D : ℕ} (b : Fin D) (g : ℝ) (hg : 0 ≤ g) :
    ∑ a, (if fwd D a b then g else 0) ≤ g := by
  by_cases h : ∃ a₀, fwd D a₀ b
  · obtain ⟨a₀, ha₀⟩ := h
    rw [Finset.sum_eq_single a₀]
    · simp [ha₀]
    · intro a _ ha
      have : ¬ fwd D a b := fun h' => ha (MultiRes_fwd_injective h' ha₀)
      simp [this]
    · simp
  · have h' : ∀ a, ¬ fwd D a b := fun a ha => h ⟨a, ha⟩
    simp [h', hg]

private lemma MultiRes_S1_norm (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (MultiRes_S1 D N A) ≤ opNorm A := by
  refine MultiRes_opNorm_le (MultiRes_opNorm_nonneg A) fun x => ?_
  set xb : Fin D → Fin N → ℂ := fun b j => x (b, j) with hxb
  have h1 : ∀ (a : Fin D) (i : Fin N), (MultiRes_S1 D N A *ᵥ x) (a, i) =
      ∑ b, (if fwd D a b then (A *ᵥ xb b) i else 0) := by
    intro a i
    simp only [Matrix.mulVec, dotProduct, MultiRes_S1, Fintype.sum_prod_type, hxb]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · simp
    · simp
  have h2 : ∀ a : Fin D, ∑ i, ‖(MultiRes_S1 D N A *ᵥ x) (a, i)‖ ^ 2 =
      ∑ b, (if fwd D a b then MultiRes_vn (A *ᵥ xb b) ^ 2 else 0) := by
    intro a
    have := MultiRes_sum_ite_sq a (fun b => A *ᵥ xb b)
    rw [← this, MultiRes_vn_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 a i, Finset.sum_apply]
    congr 2
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have h3 : MultiRes_vn (MultiRes_S1 D N A *ᵥ x) ^ 2 ≤ (opNorm A * MultiRes_vn x) ^ 2 := by
    rw [MultiRes_vn_sq, Fintype.sum_prod_type]
    simp only [h2]
    rw [Finset.sum_comm]
    calc ∑ b, ∑ a, (if fwd D a b then MultiRes_vn (A *ᵥ xb b) ^ 2 else 0)
        ≤ ∑ b, MultiRes_vn (A *ᵥ xb b) ^ 2 :=
          Finset.sum_le_sum fun b _ => MultiRes_sum_ite_le b _ (sq_nonneg _)
      _ ≤ ∑ b, (opNorm A * MultiRes_vn (xb b)) ^ 2 :=
          Finset.sum_le_sum fun b _ =>
            pow_le_pow_left₀ (MultiRes_vn_nonneg _) (MultiRes_vn_mulVec_le _ _) 2
      _ = (opNorm A) ^ 2 * ∑ b, MultiRes_vn (xb b) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => mul_pow _ _ _
      _ = (opNorm A * MultiRes_vn x) ^ 2 := by
          rw [mul_pow, MultiRes_vn_sq x, Fintype.sum_prod_type]
          congr 1
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [MultiRes_vn_sq]
  exact (abs_le_of_sq_le_sq h3 (mul_nonneg (MultiRes_opNorm_nonneg A)
    (MultiRes_vn_nonneg _))).trans' (le_abs_self _)

/-- `‖lam D N A‖ ≤ 2 ‖A‖`. -/
private lemma MultiRes_opNorm_lam_le (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * opNorm A := by
  rw [MultiRes_lam_eq]
  refine (opNorm_add_le _ _).trans ?_
  rw [MultiRes_opNorm_conjTranspose]
  have := MultiRes_S1_norm D N A
  linarith

/-- `lam D N A` has zero diagonal. -/
private lemma MultiRes_lam_diag (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (p : Idx D N) :
    lam D N A p p = 0 := by
  simp [lam, MultiRes_fwd_irrefl]

end Lam

section Trace

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Everything used from the spectral decomposition of a Hermitian matrix `Y`. -/
private lemma MultiRes_spec' (Y : Matrix ι ι ℂ) (hY : Y.IsHermitian) :
    ∃ (a : ι → ℝ) (u : ι → ι → ℂ), (∀ k, MultiRes_vn (u k) = 1) ∧
      ∑ k, a k ^ 2 = MultiRes_hs2 Y ∧
      (∀ W : Matrix ι ι ℂ, (W * Y).trace = ∑ k, (a k : ℂ) * (star (u k) ⬝ᵥ (W *ᵥ u k))) ∧
      (∀ Z : Matrix ι ι ℂ, MultiRes_hs2 (Z * Y) = ∑ k, a k ^ 2 * MultiRes_vn (Z *ᵥ u k) ^ 2) ∧
      (∀ Z : Matrix ι ι ℂ, ∑ k, MultiRes_vn (Z *ᵥ u k) ^ 2 = MultiRes_hs2 Z) := by
  obtain ⟨U, a, hU, hU', hY'⟩ := MultiRes_spec Y hY
  refine ⟨a, fun k p => U p k, MultiRes_vn_col U hU', MultiRes_sum_sq_eq Y U a hU hU' hY',
    fun W => ?_, fun Z => ?_, fun Z => ?_⟩
  · rw [hY']
    exact MultiRes_trace_mul_diag W U a
  · rw [hY']
    exact MultiRes_hs2_mul_diag Z U a hU hU'
  · rw [← MultiRes_hs2_mul_unitary Z U hU, MultiRes_hs2_cols]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : (fun p => (Z * U) p k) = Z *ᵥ fun p => U p k := by
      ext p
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e]

omit [DecidableEq ι] in
private lemma MultiRes_sum_abs_sq (a : ι → ℝ) :
    (∑ k, |a k|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ k, a k ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1 : ℝ))
    (fun k => |a k|)
  simpa [sq_abs] using h

omit [DecidableEq ι] in
/-- The normalized trace is at most the largest diagonal entry in norm. -/
private lemma MultiRes_norm_ntr_le [Nonempty ι] (W : Matrix ι ι ℂ) (S : ℝ)
    (hS : ∀ x, ‖W x x‖ ≤ S) : ‖ntr W‖ ≤ S := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ‖W.trace‖ ≤ (Fintype.card ι : ℝ) * S := by
    calc ‖W.trace‖ = ‖∑ x, W x x‖ := rfl
      _ ≤ ∑ x, ‖W x x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : ι, S := Finset.sum_le_sum fun x _ => hS x
      _ = (Fintype.card ι : ℝ) * S := by simp
  rw [inv_mul_le_iff₀ hn]
  exact h1

private lemma MultiRes_diag_eq (W : Matrix ι ι ℂ) (x : ι) :
    star (Pi.single x (1 : ℂ) : ι → ℂ) ⬝ᵥ (W *ᵥ (Pi.single x (1 : ℂ) : ι → ℂ)) = W x x := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

omit [DecidableEq ι] in
/-- `⟨Λ²⟩ = ‖Λ‖²_HS / n` for Hermitian `Λ`. -/
private lemma MultiRes_avgSq_eq (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) :
    avgSq Λ = MultiRes_hs2 Λ / (Fintype.card ι : ℝ) := by
  unfold avgSq ntr
  have e : Λ * Λ = Λ * Λᴴ := by rw [hΛ.eq]
  rw [e, MultiRes_trace_mul_conjTranspose]
  have : ((Fintype.card ι : ℂ))⁻¹ * (MultiRes_hs2 Λ : ℂ) =
      (((Fintype.card ι : ℝ))⁻¹ * MultiRes_hs2 Λ : ℝ) := by push_cast; ring
  rw [this, Complex.ofReal_re, inv_mul_eq_div]

/-- The shifted matrix `Λ - δ` has `‖Λ - δ‖²_HS ≤ (1 + K)² ‖Λ‖²_HS` when `|δ| ≤ K ⟨Λ²⟩`. -/
private lemma MultiRes_hs2_shift [Nonempty ι] (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian)
    (hdiag : ∀ p, Λ p p = 0) (hn : opNorm Λ ≤ 1 / 10) (K δ : ℝ) (hK : 0 ≤ K)
    (hδ : |δ| ≤ K * avgSq Λ) :
    MultiRes_hs2 (Λ - (δ : ℂ) • (1 : Matrix ι ι ℂ)) ≤ (1 + K) ^ 2 * MultiRes_hs2 Λ := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have e : MultiRes_hs2 (Λ - (δ : ℂ) • (1 : Matrix ι ι ℂ)) =
      MultiRes_hs2 Λ + (Fintype.card ι : ℝ) * δ ^ 2 := by
    unfold MultiRes_hs2
    have : ∀ p q : ι, ‖(Λ - (δ : ℂ) • (1 : Matrix ι ι ℂ)) p q‖ ^ 2 =
        ‖Λ p q‖ ^ 2 + (if p = q then δ ^ 2 else 0) := by
      intro p q
      by_cases h : p = q
      · subst h
        simp [hdiag]
      · simp [h]
    simp only [this, Finset.sum_add_distrib]
    simp
  have h1 : MultiRes_hs2 Λ ≤ (Fintype.card ι : ℝ) * opNorm Λ ^ 2 := MultiRes_hs2_le_card Λ
  have h2 : (Fintype.card ι : ℝ) * opNorm Λ ^ 2 ≤ (Fintype.card ι : ℝ) * (1 / 10) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (MultiRes_opNorm_nonneg _) hn 2) hcard.le
  have hav := MultiRes_avgSq_eq Λ hΛ
  have h0 : 0 ≤ avgSq Λ := by
    rw [hav]; exact div_nonneg (MultiRes_hs2_nonneg _) hcard.le
  have h3 : δ ^ 2 ≤ K ^ 2 * (MultiRes_hs2 Λ / (Fintype.card ι : ℝ)) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg δ) hδ 2
    rw [sq_abs, mul_pow, hav] at this
    exact this
  set r := MultiRes_hs2 Λ / (Fintype.card ι : ℝ) with hr
  have hr0 : 0 ≤ r := div_nonneg (MultiRes_hs2_nonneg _) hcard.le
  have hnr : (Fintype.card ι : ℝ) * r = MultiRes_hs2 Λ := by
    rw [hr]; field_simp
  have hr1 : r ≤ 1 / 100 := by
    rw [hr, div_le_iff₀ hcard]
    nlinarith
  have h4 : (Fintype.card ι : ℝ) * δ ^ 2 ≤ K ^ 2 / 100 * MultiRes_hs2 Λ := by
    calc (Fintype.card ι : ℝ) * δ ^ 2 ≤ (Fintype.card ι : ℝ) * (K ^ 2 * r ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hcard.le
      _ = K ^ 2 * r * ((Fintype.card ι : ℝ) * r) := by ring
      _ = K ^ 2 * r * MultiRes_hs2 Λ := by rw [hnr]
      _ ≤ K ^ 2 * (1 / 100) * MultiRes_hs2 Λ := by
          have := MultiRes_hs2_nonneg Λ
          have h5 : K ^ 2 * r ≤ K ^ 2 * (1 / 100) := mul_le_mul_of_nonneg_left hr1 (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right h5 this
      _ = K ^ 2 / 100 * MultiRes_hs2 Λ := by ring
  rw [e]
  have := MultiRes_hs2_nonneg Λ
  nlinarith [mul_nonneg hK this, sq_nonneg K]


/-- `|tr(X Y₁ B Y₂)| ≤ Q₀ ‖B‖ ‖Y₁‖_HS ‖Y₂‖_HS`, from bounds on `x^* X y` for the eigenvectors of
the Hermitian `Y₁`. -/
private lemma MultiRes_loop_one_det (X B Y₁ Y₂ : Matrix ι ι ℂ) (a : ι → ℝ) (u : ι → ι → ℂ)
    (Kb s₁ s₂ Q₀ : ℝ) (hB : opNorm B ≤ Kb) (hKb : 0 ≤ Kb) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (hQ0 : 0 ≤ Q₀) (hY₁s : MultiRes_hs2 Y₁ ≤ s₁ ^ 2) (hY₂s : MultiRes_hs2 Y₂ ≤ s₂ ^ 2)
    (hu1 : ∀ k, MultiRes_vn (u k) = 1) (hsum : ∑ k, a k ^ 2 = MultiRes_hs2 Y₁)
    (htr : ∀ W : Matrix ι ι ℂ, (W * Y₁).trace = ∑ k, (a k : ℂ) * (star (u k) ⬝ᵥ (W *ᵥ u k)))
    (hcol : ∀ Z : Matrix ι ι ℂ, ∑ k, MultiRes_vn (Z *ᵥ u k) ^ 2 = MultiRes_hs2 Z)
    (hQ : ∀ k, ‖star ((B * Y₂)ᴴ *ᵥ u k) ⬝ᵥ (X *ᵥ u k)‖ ≤
      Q₀ * (MultiRes_vn ((B * Y₂)ᴴ *ᵥ u k) * MultiRes_vn (u k))) :
    ‖(X * Y₁ * B * Y₂).trace‖ ≤ Q₀ * (Kb * (s₁ * s₂)) := by
  have e : (X * Y₁ * B * Y₂).trace = ((B * Y₂ * X) * Y₁).trace := by
    calc (X * Y₁ * B * Y₂).trace = ((X * Y₁) * (B * Y₂)).trace := by rw [Matrix.mul_assoc _ B Y₂]
      _ = ((B * Y₂) * (X * Y₁)).trace := Matrix.trace_mul_comm _ _
      _ = ((B * Y₂ * X) * Y₁).trace := by rw [Matrix.mul_assoc (B * Y₂) X Y₁]
  rw [e, htr]
  have h1 : ∀ k, ‖star (u k) ⬝ᵥ ((B * Y₂ * X) *ᵥ u k)‖ ≤ Q₀ * MultiRes_vn ((B * Y₂)ᴴ *ᵥ u k) := by
    intro k
    have : star (u k) ⬝ᵥ ((B * Y₂ * X) *ᵥ u k) = star ((B * Y₂)ᴴ *ᵥ u k) ⬝ᵥ (X *ᵥ u k) := by
      rw [← Matrix.mulVec_mulVec, MultiRes_dot_left]
    rw [this]
    refine (hQ k).trans ?_
    rw [hu1 k, mul_one]
  have h2 : ‖∑ k, (a k : ℂ) * (star (u k) ⬝ᵥ ((B * Y₂ * X) *ᵥ u k))‖ ≤
      Q₀ * ∑ k, |a k| * MultiRes_vn ((B * Y₂)ᴴ *ᵥ u k) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |a k| * ‖star (u k) ⬝ᵥ ((B * Y₂ * X) *ᵥ u k)‖
        ≤ |a k| * (Q₀ * MultiRes_vn ((B * Y₂)ᴴ *ᵥ u k)) :=
          mul_le_mul_of_nonneg_left (h1 k) (abs_nonneg _)
      _ = Q₀ * (|a k| * MultiRes_vn ((B * Y₂)ᴴ *ᵥ u k)) := by ring
  refine h2.trans (mul_le_mul_of_nonneg_left ?_ hQ0)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun k => |a k|)
    (fun k => MultiRes_vn ((B * Y₂)ᴴ *ᵥ u k))
  simp only [sq_abs] at hcs
  rw [hsum, hcol] at hcs
  have h3 : MultiRes_hs2 ((B * Y₂)ᴴ) ≤ (Kb * s₂) ^ 2 := by
    rw [MultiRes_hs2_conjTranspose]
    refine (MultiRes_hs2_mul_left_le _ _).trans ?_
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_left₀ (MultiRes_opNorm_nonneg _) hB 2) hY₂s
      (MultiRes_hs2_nonneg _) (sq_nonneg _)
  have h4 : (∑ k, |a k| * MultiRes_vn ((B * Y₂)ᴴ *ᵥ u k)) ^ 2 ≤ (s₁ * (Kb * s₂)) ^ 2 := by
    refine hcs.trans ?_
    rw [mul_pow]
    exact mul_le_mul hY₁s h3 (MultiRes_hs2_nonneg _) (sq_nonneg _)
  have h5 : 0 ≤ s₁ * (Kb * s₂) := mul_nonneg hs₁ (mul_nonneg hKb hs₂)
  have := (le_abs_self _).trans (abs_le_of_sq_le_sq h4 h5)
  nlinarith

omit [DecidableEq ι] in
/-- `|tr(X₁ Y₁ X₂ Y₂)| ≤ ‖X₁Y₁‖_HS ‖X₂Y₂‖_HS`, with the squared bounds on both factors. -/
private lemma MultiRes_loop_both_det (X₁ X₂ Y₁ Y₂ : Matrix ι ι ℂ) (ρ₁ ρ₂ ρ s₁ s₂ : ℝ)
    (hρ : 0 ≤ ρ) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hρρ : ρ₁ * ρ₂ ≤ ρ ^ 2)
    (h₁ : MultiRes_hs2 (X₁ * Y₁) ≤ ρ₁ * s₁ ^ 2) (h₂ : MultiRes_hs2 (X₂ * Y₂) ≤ ρ₂ * s₂ ^ 2) :
    ‖(X₁ * Y₁ * X₂ * Y₂).trace‖ ≤ ρ * (s₁ * s₂) := by
  rw [Matrix.mul_assoc _ X₂ Y₂]
  refine (MultiRes_norm_trace_mul_le _ _).trans ?_
  have h3 : (hsNorm (X₁ * Y₁) * hsNorm (X₂ * Y₂)) ^ 2 ≤ (ρ * (s₁ * s₂)) ^ 2 := by
    rw [mul_pow, MultiRes_hsNorm_sq, MultiRes_hsNorm_sq]
    calc MultiRes_hs2 (X₁ * Y₁) * MultiRes_hs2 (X₂ * Y₂) ≤ (ρ₁ * s₁ ^ 2) * (ρ₂ * s₂ ^ 2) :=
          mul_le_mul h₁ h₂ (MultiRes_hs2_nonneg _) (by positivity)
      _ = (ρ₁ * ρ₂) * (s₁ ^ 2 * s₂ ^ 2) := by ring
      _ ≤ ρ ^ 2 * (s₁ ^ 2 * s₂ ^ 2) := mul_le_mul_of_nonneg_right hρρ (by positivity)
      _ = (ρ * (s₁ * s₂)) ^ 2 := by ring
  exact (le_abs_self _).trans (abs_le_of_sq_le_sq h3 (by positivity))

end Trace

section Assemble

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma MultiRes_needL_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ}
    (Good : Ω → Fin p → (ι → ℂ) → (ι → ℂ) → Prop) (δ : ENNReal)
    (hG : ∀ i x y, P {ω | ¬ Good ω i x y} ≤ δ) {l : ℕ} (w : Fin (l + 1) → Fin p × Bool)
    (B : Fin (l + 1 + 1) → Matrix ι ι ℂ) (x y : ι → ℂ) :
    P {ω | ¬ MultiRes_needL (Good ω) w B x y} ≤ δ := by
  cases l with
  | zero =>
    by_cases hs : (w 0).2 = true
    · simpa [MultiRes_needL, hs] using hG _ _ _
    · simpa [MultiRes_needL, hs] using hG _ _ _
  | succ l => simpa [MultiRes_needL] using hG _ _ _

omit [DecidableEq ι] in
private lemma MultiRes_needR_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ}
    (Good : Ω → Fin p → (ι → ℂ) → (ι → ℂ) → Prop) (δ : ENNReal)
    (hG : ∀ i x y, P {ω | ¬ Good ω i x y} ≤ δ) {l : ℕ} (w : Fin (l + 1) → Fin p × Bool)
    (B : Fin (l + 1 + 1) → Matrix ι ι ℂ) (x y : ι → ℂ) :
    P {ω | ¬ MultiRes_needR (Good ω) w B x y} ≤ δ := by
  cases l with
  | zero => simp [MultiRes_needR]
  | succ l => simpa [MultiRes_needR] using hG _ _ _

private lemma MultiRes_iInf_iSup {p : ℕ} (hp : 1 ≤ p) (a b : Fin p → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 ≤ b i) :
    0 < (⨅ i, a i) ∧ (∀ i, (⨅ i, a i) ≤ a i) ∧ (∀ i, b i ≤ ⨆ i, b i) ∧ 0 ≤ ⨆ i, b i := by
  have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  refine ⟨?_, fun i => ciInf_le (Finite.bddBelow_range _) i,
    fun i => le_ciSup (Finite.bddAbove_range _) i, ?_⟩
  · obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := a)
    rw [← hj]; exact ha j
  · exact (hb (⟨0, hp⟩ : Fin p)).trans (le_ciSup (Finite.bddAbove_range _) (⟨0, hp⟩ : Fin p))

private lemma MultiRes_AC_le (τ c₀ T Cext : ℝ) (hc₀ : 0 < c₀) (hT1 : 1 ≤ T) (hCe : 0 ≤ Cext)
    (h : MultiRes_CW τ c₀ * Cext ≤ T) :
    (MultiRes_CG τ c₀ * T + (MultiRes_CPsi c₀ * T + 5 / 4)) * Cext ≤ T * T := by
  have h1 : MultiRes_CG τ c₀ * T + (MultiRes_CPsi c₀ * T + 5 / 4) ≤ MultiRes_CW τ c₀ * T := by
    unfold MultiRes_CW; nlinarith
  calc (MultiRes_CG τ c₀ * T + (MultiRes_CPsi c₀ * T + 5 / 4)) * Cext
      ≤ MultiRes_CW τ c₀ * T * Cext := mul_le_mul_of_nonneg_right h1 hCe
    _ = T * (MultiRes_CW τ c₀ * Cext) := by ring
    _ ≤ T * T := mul_le_mul_of_nonneg_left h (by linarith)

private lemma MultiRes_resProd_eq {p : ℕ} (G : Fin p → Matrix ι ι ℂ) (s : Fin p → Bool)
    (B : Fin p → Matrix ι ι ℂ) :
    resProd G s B = resWord G (fun j : Fin p => (j, s j))
      (Fin.cons (1 : Matrix ι ι ℂ) B : Fin (p + 1) → Matrix ι ι ℂ) := by
  unfold resProd resWord
  simp [Fin.cons_zero, Fin.cons_succ]

end Assemble

section Assemble2

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma MultiRes_vn_of_sum (u : ι → ℂ) (h : ∑ x, ‖u x‖ ^ 2 = 1) : MultiRes_vn u = 1 := by
  have h2 : MultiRes_vn u ^ 2 = 1 := by rw [MultiRes_vn_sq, h]
  nlinarith [MultiRes_vn_nonneg u]

/-- The union bound, with `c` events at each of the `κ` indices, off a null set. -/
private lemma MultiRes_union_final {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {κ : Type*}
    [Fintype κ] (E : κ → Set Ω) (c N : ℕ) (hN : 1 ≤ N) (D' : ℝ)
    (hE : ∀ k, P (E k) ≤ (c : ENNReal) * ENNReal.ofReal ((N : ℝ) ^ (-(D' + 2)))) (Z0 S : Set Ω)
    (hZ0 : P Z0 = 0) (hS : ∀ ω, ω ∉ Z0 → (∀ k, ω ∉ E k) → ω ∉ S)
    (hm : Fintype.card κ * c ≤ N * N) : P S ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  refine (MultiRes_union P E _ hE Z0 S hZ0 hS).trans ?_
  rw [← mul_assoc, ← Nat.cast_mul]
  exact MultiRes_card_mul_le _ N hN hm D'

omit [DecidableEq ι] in
/-- Both end events of a word, for one pair of vectors. -/
private lemma MultiRes_ends_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ}
    (Good : Ω → Fin p → (ι → ℂ) → (ι → ℂ) → Prop) (δ : ENNReal)
    (hG : ∀ i x y, P {ω | ¬ Good ω i x y} ≤ δ) {l : ℕ} (w : Fin (l + 1) → Fin p × Bool)
    (B : Fin (l + 1 + 1) → Matrix ι ι ℂ) (x y : ι → ℂ) :
    P {ω | ¬ (MultiRes_needL (Good ω) w B x y ∧ MultiRes_needR (Good ω) w B x y)} ≤
      (2 : ℕ) * δ := by
  have hsub : {ω | ¬ (MultiRes_needL (Good ω) w B x y ∧ MultiRes_needR (Good ω) w B x y)} ⊆
      {ω | ¬ MultiRes_needL (Good ω) w B x y} ∪ {ω | ¬ MultiRes_needR (Good ω) w B x y} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_and_or] at hω
    exact hω
  calc P _ ≤ P ({ω | ¬ MultiRes_needL (Good ω) w B x y} ∪
        {ω | ¬ MultiRes_needR (Good ω) w B x y}) := measure_mono hsub
    _ ≤ P {ω | ¬ MultiRes_needL (Good ω) w B x y} + P {ω | ¬ MultiRes_needR (Good ω) w B x y} :=
        measure_union_le _ _
    _ ≤ δ + δ := add_le_add (MultiRes_needL_prob P Good δ hG w B x y)
        (MultiRes_needR_prob P Good δ hG w B x y)
    _ = (2 : ℕ) * δ := by rw [Nat.cast_ofNat, two_mul]

end Assemble2

section Loops

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private lemma MultiRes_smul_real_herm (c : ℝ) (Λ : Matrix ι ι ℂ) (h : Λ.IsHermitian) :
    ((c : ℂ) • Λ).IsHermitian := by
  unfold Matrix.IsHermitian at h ⊢
  rw [Matrix.conjTranspose_smul, h, Complex.star_def, Complex.conj_ofReal]

omit [Fintype ι] in
private lemma MultiRes_sub_smul_one_herm (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (δ : ℝ) :
    (Λ - (δ : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian at hΛ ⊢
  rw [Matrix.conjTranspose_sub, hΛ, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Complex.star_def, Complex.conj_ofReal]

private lemma MultiRes_rpow_neg_half_sq (N : ℕ) :
    ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num
  exact Real.rpow_neg_one _

/-- The averaged loop bound `n⁻¹ Σ ≤ N^{-1/2} c L` from `Σ² ≤ n (c L)²` and `N ≤ n`. -/
private lemma MultiRes_avg_bound (n : ℝ) (N : ℕ) (hN : 1 ≤ N) (hnN : (N : ℝ) ≤ n) (S c L : ℝ)
    (hS : 0 ≤ S) (hc : 0 ≤ c) (hL : 0 ≤ L) (hsq : S ^ 2 ≤ n * (c * L) ^ 2) :
    n⁻¹ * S ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) * (c * L) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hn : 0 < n := lt_of_lt_of_le hNp hnN
  have hR : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) * (c * L) :=
    mul_nonneg (Real.rpow_nonneg hNp.le _) (mul_nonneg hc hL)
  rw [inv_mul_le_iff₀ hn]
  have h1 : (n * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * (c * L))) ^ 2 = n ^ 2 * (N : ℝ)⁻¹ * (c * L) ^ 2 := by
    rw [mul_pow, mul_pow, MultiRes_rpow_neg_half_sq]; ring
  have h2 : n * (c * L) ^ 2 ≤ n ^ 2 * (N : ℝ)⁻¹ * (c * L) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← div_eq_mul_inv, le_div_iff₀ hNp]
    nlinarith
  have h3 : S ^ 2 ≤ (n * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * (c * L))) ^ 2 := by
    rw [h1]; exact hsq.trans h2
  exact (le_abs_self _).trans (abs_le_of_sq_le_sq h3 (mul_nonneg hn.le hR))

end Loops

section Loops2

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma MultiRes_pow_comb (Kp : ℝ) (hKp : 0 ≤ Kp) (i j m : ℕ) (h : i + j ≤ m) :
    (1 + Kp) ^ i * Kp ^ j ≤ (1 + Kp) ^ m := by
  have h1 : Kp ^ j ≤ (1 + Kp) ^ j := pow_le_pow_left₀ hKp (by linarith) j
  have h2 : (1 + Kp) ^ i * (1 + Kp) ^ j ≤ (1 + Kp) ^ m := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by linarith) h
  exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2

omit [DecidableEq ι] in
private lemma MultiRes_trace_cyc (B Y₁ X Y₂ : Matrix ι ι ℂ) :
    (B * Y₁ * X * Y₂).trace = (X * Y₂ * B * Y₁).trace := by
  calc (B * Y₁ * X * Y₂).trace = ((B * Y₁) * (X * Y₂)).trace := by rw [Matrix.mul_assoc _ X Y₂]
    _ = ((X * Y₂) * (B * Y₁)).trace := Matrix.trace_mul_comm _ _
    _ = (X * Y₂ * B * Y₁).trace := by rw [Matrix.mul_assoc _ B Y₁]

private lemma MultiRes_resWord_zero {p : ℕ} (G : Fin p → Matrix ι ι ℂ) (w : Fin 0 → Fin p × Bool)
    (B : Fin (0 + 1) → Matrix ι ι ℂ) : resWord G w B = B 0 := by
  simp [resWord]

omit [DecidableEq ι] in
/-- From a bound on the trace to the bound on the normalized trace. -/
private lemma MultiRes_ntr_final [Nonempty ι] (M : Matrix ι ι ℂ) (N : ℕ) (hN : 1 ≤ N)
    (hnN : (N : ℝ) ≤ Fintype.card ι) (Bd T2 R : ℝ) (hBd : ‖M.trace‖ ≤ Bd) (hR : Bd ≤ T2 * R) :
    ‖ntr M‖ ≤ T2 * (R / N) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hn : (0 : ℝ) < Fintype.card ι := lt_of_lt_of_le hNp hnN
  have hBd0 : 0 ≤ Bd := (norm_nonneg _).trans hBd
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (Fintype.card ι : ℝ)⁻¹ * ‖M.trace‖ ≤ (Fintype.card ι : ℝ)⁻¹ * Bd :=
        mul_le_mul_of_nonneg_left hBd (inv_nonneg.mpr hn.le)
    _ ≤ (N : ℝ)⁻¹ * Bd := mul_le_mul_of_nonneg_right (inv_anti₀ hNp hnN) hBd0
    _ ≤ (N : ℝ)⁻¹ * (T2 * R) := mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr hNp.le)
    _ = T2 * (R / N) := by rw [div_eq_mul_inv]; ring

/-- Two events fail with probability at most twice the single bound. -/
private lemma MultiRes_and_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → Prop)
    (δ : ENNReal) (hf : P {ω | ¬ f ω} ≤ δ) (hg : P {ω | ¬ g ω} ≤ δ) :
    P {ω | ¬ (f ω ∧ g ω)} ≤ (2 : ℕ) * δ := by
  have hsub : {ω | ¬ (f ω ∧ g ω)} ⊆ {ω | ¬ f ω} ∪ {ω | ¬ g ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_and_or] at hω
    exact hω
  calc P _ ≤ P ({ω | ¬ f ω} ∪ {ω | ¬ g ω}) := measure_mono hsub
    _ ≤ P {ω | ¬ f ω} + P {ω | ¬ g ω} := measure_union_le _ _
    _ ≤ δ + δ := add_le_add hf hg
    _ = (2 : ℕ) * δ := by rw [Nat.cast_ofNat, two_mul]

end Loops2

/-- (A.53) [entprodG] of Lemma A.4 [lemma_necessary_estimates], conditional on (2.22)
[eq:aniso_local] for every `G_i - M_i` as the paper states it: for `G_i = (H + Λ_i - z_i)⁻¹`,
`‖Λ_i‖ ≤ 1/10`, `|z_i| ≤ τ⁻¹`, `N η_i Im m_i ≥ c₀`, deterministic `‖B_i‖ ≤ 1` and unit `u, v`,
`u^* ∏ G_i^{s_i} B_i v` and `⟨∏ G_i^{s_i} B_i⟩` are `≺ (max_i Im m_i)^{1(p ≥ 2)} / η^{p-1}`. -/
theorem entprodG (D p : ℕ) (hp : 1 ≤ p) (τ c₀ : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (H : ∀ N, Ω N → Matrix (Idx D N) (Idx D N) ℂ)
    (hH : ∀ N, ∀ᵐ ω ∂(P N), (H N ω).IsHermitian)
    (Λs : ∀ N, Fin p → Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : ∀ N i, (Λs N i).IsHermitian ∧ opNorm (Λs N i) ≤ 1 / 10)
    (Z : ∀ N, Set (Fin p → ℂ))
    (hZ : ∀ N : ℕ, ∀ z ∈ Z N, ∀ i, 0 < (z i).im ∧ ‖z i‖ ≤ τ⁻¹ ∧
      c₀ ≤ (N : ℝ) * (z i).im * (mSol (Λs N i) (z i)).im)
    (hLL : ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ z ∈ Z N, ∀ i, ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
        P N {ω | (N : ℝ) ^ τ' * psiIso (Λs N i) N (z i) <
            ‖star u ⬝ᵥ ((res (H N ω + Λs N i) (z i) - MSol (Λs N i) (z i)) *ᵥ v)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D'))) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z ∈ Z N,
      ∀ (s : Fin p → Bool) (B : Fin p → Matrix (Idx D N) (Idx D N) ℂ), (∀ i, opNorm (B i) ≤ 1) →
        P N {ω | (N : ℝ) ^ τ' * bndA4 (fun i => (mSol (Λs N i) (z i)).im) (fun i => (z i).im) p <
            ‖ntr (resProd (fun i => res (H N ω + Λs N i) (z i)) s B)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
        ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
          P N {ω | (N : ℝ) ^ τ' * bndA4 (fun i => (mSol (Λs N i) (z i)).im) (fun i => (z i).im) p <
              ‖star u ⬝ᵥ (resProd (fun i => res (H N ω + Λs N i) (z i)) s B *ᵥ v)‖} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨l, rfl⟩ : ∃ l, p = l + 1 := ⟨p - 1, by omega⟩
  intro τ' hτ' D' hD'
  obtain ⟨N₁, hN₁⟩ := MultiRes_core hp τ c₀ hc₀ P H Λs hΛ Z hZ hLL τ' hτ' D' hD'
  obtain ⟨N₂, hN₂⟩ := MultiRes_pow_ge (MultiRes_CW τ c₀) (τ' / 2) (by positivity)
  refine ⟨max (max N₁ N₂) (4 * D + 2), fun N hN z hzN s B hB => ?_⟩
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : 4 * D + 2 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hN1, hne, hbad, hward⟩ := hN₁ N hNa z hzN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  set T : ℝ := (N : ℝ) ^ (τ' / 2) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
  have hCT : MultiRes_CW τ c₀ * 1 ≤ T := by rw [mul_one]; exact hN₂ N hNb
  have hTT : T * T = (N : ℝ) ^ τ' := by
    rw [hT, ← Real.rpow_add hNpos]; congr 1; ring
  have hAC := MultiRes_AC_le τ c₀ T 1 hc₀ hT1 zero_le_one hCT
  have hηpos : ∀ i, 0 < (z i).im := fun i => (hZ N z hzN i).1
  have hμpos : ∀ i, 0 < (mSol (Λs N i) (z i)).im := by
    intro i
    obtain ⟨h1, -, h3⟩ := hZ N z hzN i
    by_contra hcon
    have : (mSol (Λs N i) (z i)).im ≤ 0 := not_lt.mp hcon
    nlinarith [mul_pos hNpos h1]
  obtain ⟨hε0, hεle, hβle, hβ0⟩ := MultiRes_iInf_iSup hp (fun i => (z i).im)
    (fun i => (mSol (Λs N i) (z i)).im) hηpos (fun i => (hμpos i).le)
  set ε : ℝ := ⨅ i, (z i).im with hε
  set β : ℝ := ⨆ i, (mSol (Λs N i) (z i)).im with hβ
  have hbnd : bndA4 (fun i => (mSol (Λs N i) (z i)).im) (fun i => (z i).im) (l + 1) =
      (if 2 ≤ l + 1 then β else 1) / ε ^ l := by
    simp [bndA4, hε, hβ]
  have hSb : 0 ≤ (if 2 ≤ l + 1 then β else 1) / ε ^ l :=
    div_nonneg (by split_ifs; exact hβ0; norm_num) (pow_nonneg hε0.le _)
  have hB' : ∀ j, opNorm ((Fin.cons (1 : Matrix (Idx D N) (Idx D N) ℂ) B :
      Fin (l + 1 + 1) → Matrix (Idx D N) (Idx D N) ℂ) j) ≤ 1 := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using MultiRes_opNorm_one_le
    · simpa using hB i
  let Good : Ω N → Fin (l + 1) → (Idx D N → ℂ) → (Idx D N → ℂ) → Prop :=
    fun ω i x y => MultiRes_GoodV N (τ' / 2) (H N ω + Λs N i) (Λs N i) (z i) x y
  have hnull : P N {ω | ¬ (H N ω).IsHermitian} = 0 := MeasureTheory.ae_iff.mp (hH N)
  have hW : ∀ ω, (H N ω).IsHermitian → ∀ x y : Idx D N → ℂ, MultiRes_vn x = 1 →
      MultiRes_vn y = 1 →
      (MultiRes_needL (Good ω) (fun j : Fin (l + 1) => (j, s j))
        (Fin.cons (1 : Matrix (Idx D N) (Idx D N) ℂ) B) x y ∧
       MultiRes_needR (Good ω) (fun j : Fin (l + 1) => (j, s j))
        (Fin.cons (1 : Matrix (Idx D N) (Idx D N) ℂ) B) x y) →
      ‖star x ⬝ᵥ (resProd (fun i => res (H N ω + Λs N i) (z i)) s B *ᵥ y)‖ ≤
        (N : ℝ) ^ τ' * bndA4 (fun i => (mSol (Λs N i) (z i)).im) (fun i => (z i).im) (l + 1) := by
    intro ω hω x y hx hy ⟨hL, hR⟩
    have h := MultiRes_W1 (hward ω hω) ε β 1 hε0 hεle hβle (fun j : Fin (l + 1) => (j, s j))
      (Fin.cons (1 : Matrix (Idx D N) (Idx D N) ℂ) B) hB' x y hL hR
    rw [MultiRes_resProd_eq, hbnd, ← hTT]
    refine h.trans ?_
    rw [hx, hy, one_pow]
    nlinarith [mul_le_mul_of_nonneg_right hAC hSb]
  refine ⟨?_, ?_⟩
  · refine MultiRes_union_final (P N)
      (fun x : Idx D N => {ω | ¬ (MultiRes_needL (Good ω) (fun j : Fin (l + 1) => (j, s j))
        (Fin.cons (1 : Matrix (Idx D N) (Idx D N) ℂ) B) (Pi.single x 1) (Pi.single x 1) ∧
        MultiRes_needR (Good ω) (fun j : Fin (l + 1) => (j, s j))
        (Fin.cons (1 : Matrix (Idx D N) (Idx D N) ℂ) B) (Pi.single x 1) (Pi.single x 1))})
      2 N hN1 D' (fun x => MultiRes_ends_prob (P N) Good _ hbad _ _ _ _)
      {ω | ¬ (H N ω).IsHermitian} _ hnull ?_ ?_
    · intro ω hω0 hk
      have hω0' : (H N ω).IsHermitian := not_not.mp hω0
      simp only [Set.mem_ofPred_eq, not_lt]
      refine MultiRes_norm_ntr_le _ _ fun x => ?_
      have := hW ω hω0' _ _ (MultiRes_vn_single x) (MultiRes_vn_single x)
        (not_not.mp (hk x))
      rwa [MultiRes_diag_eq] at this
    · simp only [Fintype.card_prod, Fintype.card_fin]
      nlinarith
  · intro u v hu hv
    refine MultiRes_union_final (P N)
      (fun _ : Unit => {ω | ¬ (MultiRes_needL (Good ω) (fun j : Fin (l + 1) => (j, s j))
        (Fin.cons (1 : Matrix (Idx D N) (Idx D N) ℂ) B) u v ∧
        MultiRes_needR (Good ω) (fun j : Fin (l + 1) => (j, s j))
        (Fin.cons (1 : Matrix (Idx D N) (Idx D N) ℂ) B) u v)})
      2 N hN1 D' (fun _ => MultiRes_ends_prob (P N) Good _ hbad _ _ _ _)
      {ω | ¬ (H N ω).IsHermitian} _ hnull ?_ ?_
    · intro ω hω0 hk
      have hω0' : (H N ω).IsHermitian := not_not.mp hω0
      simp only [Set.mem_ofPred_eq, not_lt]
      exact hW ω hω0' u v (MultiRes_vn_of_sum u hu) (MultiRes_vn_of_sum v hv)
        (not_not.mp (hk ()))
    · simp only [Fintype.card_unit]
      nlinarith

/-- (A.54) [one_loop_estimate] of Lemma A.4 [lemma_necessary_estimates], `l ≥ 1`, conditional on
(2.22) [eq:aniso_local] as the paper states it: for `Λ_i = c_i Λ`, `Λ = lam D N A`, `|c_i| ≤ C₀`,
`2C₀‖A‖ ≤ 1/10`, deterministic factors of norm `≤ K` between the resolvents, and `Λ` replaced
by `Λ - δ` with `|δ| ≤ K⟨Λ²⟩` (this covers `Λ̃` of Lemma 5.1 and `Λ̂_t` of Lemma 5.3 through
(5.4) and (5.21)), `⟨Π_l (Λ - δ)⟩ ≺ N^{-1/2} ‖Λ‖_HS (max_i Im m_i)^{1(l ≥ 2)} η^{-(l-1)}`. -/
theorem one_loop_estimate (D p l : ℕ) (hp : 1 ≤ p) (hl : 1 ≤ l) (τ c₀ C₀ K : ℝ) (hτ : 0 < τ)
    (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (H : ∀ N, Ω N → Matrix (Idx D N) (Idx D N) ℂ) (hH : ∀ N, ∀ᵐ ω ∂(P N), (H N ω).IsHermitian)
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (hA : ∀ N, 2 * C₀ * opNorm (A N) ≤ 1 / 10)
    (c : ℕ → Fin p → ℝ) (hc : ∀ N i, |c N i| ≤ C₀)
    (δ : ℕ → ℝ) (hδ : ∀ N, |δ N| ≤ K * avgSq (lam D N (A N)))
    (Z : ∀ N, Set (Fin p → ℂ))
    (hZ : ∀ N : ℕ, ∀ z ∈ Z N, ∀ i, 0 < (z i).im ∧ ‖z i‖ ≤ τ⁻¹ ∧
      c₀ ≤ (N : ℝ) * (z i).im * (mSol ((c N i : ℂ) • lam D N (A N)) (z i)).im)
    (hLL : ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ z ∈ Z N, ∀ i, ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
        P N {ω | (N : ℝ) ^ τ' * psiIso ((c N i : ℂ) • lam D N (A N)) N (z i) <
            ‖star u ⬝ᵥ ((res (H N ω + (c N i : ℂ) • lam D N (A N)) (z i) -
              MSol ((c N i : ℂ) • lam D N (A N)) (z i)) *ᵥ v)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D'))) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z ∈ Z N,
      ∀ (w : Fin l → Fin p × Bool) (B : Fin (l + 1) → Matrix (Idx D N) (Idx D N) ℂ),
      (∀ j, opNorm (B j) ≤ K) →
        P N {ω | (N : ℝ) ^ τ' * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N (A N)) *
              bndA4 (fun i => (mSol ((c N i : ℂ) • lam D N (A N)) (z i)).im)
                (fun i => (z i).im) l) <
            ‖ntr (resWord (fun i => res (H N ω + (c N i : ℂ) • lam D N (A N)) (z i)) w B *
              (lam D N (A N) - (δ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have hC₀0 : 0 ≤ C₀ := by linarith
  have hlam : ∀ N, opNorm (lam D N (A N)) ≤ 1 / 10 := by
    intro N
    have h1 := MultiRes_opNorm_lam_le D N (A N)
    have h2 := MultiRes_opNorm_nonneg (A N)
    have h3 := hA N
    nlinarith
  have hΛ' : ∀ N (i : Fin p), (((c N i : ℝ) : ℂ) • lam D N (A N)).IsHermitian ∧
      opNorm (((c N i : ℝ) : ℂ) • lam D N (A N)) ≤ 1 / 10 := by
    intro N i
    refine ⟨MultiRes_smul_real_herm _ _ (lam_isHermitian D N (A N)), ?_⟩
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := MultiRes_opNorm_lam_le D N (A N)
    have h2 := MultiRes_opNorm_nonneg (A N)
    have h3 := hA N
    have h4 := hc N i
    have h5 := MultiRes_opNorm_nonneg (lam D N (A N))
    nlinarith [mul_le_mul h4 h1 h5 hC₀0]
  intro τ' hτ' D' hD'
  obtain ⟨N₁, hN₁⟩ := MultiRes_core (Λs := fun N i => ((c N i : ℝ) : ℂ) • lam D N (A N)) hp τ c₀
    hc₀ P H hΛ' Z hZ hLL τ' hτ' D' hD'
  set Kp : ℝ := max K 0 with hKp
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  have hKKp : K ≤ Kp := le_max_left _ _
  set Cext : ℝ := Kp ^ (l + 2) * (1 + Kp) with hCext
  have hCext0 : 0 ≤ Cext := by positivity
  obtain ⟨N₂, hN₂⟩ := MultiRes_pow_ge (MultiRes_CW τ c₀ * Cext) (τ' / 2) (by positivity)
  refine ⟨max (max N₁ N₂) (4 * D + 2), fun N hN z hzN w B hB => ?_⟩
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : 4 * D + 2 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hN1, hne, hbad, hward⟩ := hN₁ N hNa z hzN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  set T : ℝ := (N : ℝ) ^ (τ' / 2) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
  have hCT : MultiRes_CW τ c₀ * Cext ≤ T := hN₂ N hNb
  have hTT : T * T = (N : ℝ) ^ τ' := by
    rw [hT, ← Real.rpow_add hNpos]; congr 1; ring
  have hAC := MultiRes_AC_le τ c₀ T Cext hc₀ hT1 hCext0 hCT
  have hηpos : ∀ i, 0 < (z i).im := fun i => (hZ N z hzN i).1
  have hμpos : ∀ i, 0 < (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im := by
    intro i
    obtain ⟨h1, -, h3⟩ := hZ N z hzN i
    by_contra hcon
    have : (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im ≤ 0 := not_lt.mp hcon
    nlinarith [mul_pos hNpos h1]
  obtain ⟨hε0, hεle, hβle, hβ0⟩ := MultiRes_iInf_iSup hp (fun i => (z i).im)
    (fun i => (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im) hηpos (fun i => (hμpos i).le)
  set ε : ℝ := ⨅ i, (z i).im with hε
  set β : ℝ := ⨆ i, (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im with hβ
  have hbnd : bndA4 (fun i => (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im)
      (fun i => (z i).im) (l + 1) = (if 2 ≤ l + 1 then β else 1) / ε ^ l := by
    simp [bndA4, hε, hβ]
  have hSb : 0 ≤ (if 2 ≤ l + 1 then β else 1) / ε ^ l :=
    div_nonneg (by split_ifs; exact hβ0; norm_num) (pow_nonneg hε0.le _)
  have hBp : ∀ j, opNorm (B j) ≤ Kp := fun j => (hB j).trans hKKp
  have hY := MultiRes_sub_smul_one_herm (lam D N (A N)) (lam_isHermitian D N (A N)) (δ N)
  obtain ⟨a, u, hu1, hsum, htr, -, -⟩ := MultiRes_spec' _ hY
  let Good : Ω N → Fin p → (Idx D N → ℂ) → (Idx D N → ℂ) → Prop :=
    fun ω i x y => MultiRes_GoodV N (τ' / 2) (H N ω + ((c N i : ℝ) : ℂ) • lam D N (A N))
      (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i) x y
  have hnull : P N {ω | ¬ (H N ω).IsHermitian} = 0 := MeasureTheory.ae_iff.mp (hH N)
  have hcard : (Fintype.card (Idx D N) : ℝ) = (D : ℝ) * N := by simp
  have hD1 : 1 ≤ D := by
    obtain ⟨⟨a, _⟩⟩ := hne
    exact Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact a.elim0)
  have hnN : (N : ℝ) ≤ Fintype.card (Idx D N) := by
    rw [hcard]
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    nlinarith
  have havg0 : 0 ≤ avgSq (lam D N (A N)) := by
    rw [MultiRes_avgSq_eq _ (lam_isHermitian D N (A N))]
    exact div_nonneg (MultiRes_hs2_nonneg _) (Nat.cast_nonneg _)
  have hhs : MultiRes_hs2 (lam D N (A N) - (δ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤
      (1 + Kp) ^ 2 * hsNorm (lam D N (A N)) ^ 2 := by
    rw [MultiRes_hsNorm_sq]
    exact MultiRes_hs2_shift _ (lam_isHermitian D N (A N)) (MultiRes_lam_diag D N (A N))
      (hlam N) Kp (δ N) hKp0 ((hδ N).trans (mul_le_mul_of_nonneg_right hKKp havg0))
  have hL0 := MultiRes_hsNorm_nonneg (lam D N (A N))
  refine MultiRes_union_final (P N)
    (fun k : Idx D N => {ω | ¬ (MultiRes_needL (Good ω) w B (u k) (u k) ∧
      MultiRes_needR (Good ω) w B (u k) (u k))})
    2 N hN1 D' (fun k => MultiRes_ends_prob (P N) Good _ hbad _ _ _ _)
    {ω | ¬ (H N ω).IsHermitian} _ hnull ?_ ?_
  · intro ω hω0 hk
    have hω0' : (H N ω).IsHermitian := not_not.mp hω0
    simp only [Set.mem_ofPred_eq, not_lt]
    set Q : ℝ := (MultiRes_CG τ c₀ * T + (MultiRes_CPsi c₀ * T + 5 / 4)) * Kp ^ (l + 2) *
      ((if 2 ≤ l + 1 then β else 1) / ε ^ l) with hQ
    have hQ0 : 0 ≤ Q := by
      have := MultiRes_CG_pos (τ := τ) hc₀
      have := MultiRes_CPsi_pos hc₀
      rw [hQ]; positivity
    have hq : ∀ k, ‖star (u k) ⬝ᵥ (resWord (fun i => res (H N ω + ((c N i : ℝ) : ℂ) •
        lam D N (A N)) (z i)) w B *ᵥ u k)‖ ≤ Q := by
      intro k
      have h := MultiRes_W1 (hward ω hω0') ε β Kp hε0 hεle hβle w B hBp (u k) (u k)
        (not_not.mp (hk k)).1 (not_not.mp (hk k)).2
      rw [hu1 k, one_mul, mul_one] at h
      exact h
    have htr' := htr (resWord (fun i => res (H N ω + ((c N i : ℝ) : ℂ) • lam D N (A N)) (z i))
      w B)
    have h1 : ‖ntr (resWord (fun i => res (H N ω + ((c N i : ℝ) : ℂ) • lam D N (A N)) (z i))
        w B * (lam D N (A N) - (δ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))‖ ≤
        (Fintype.card (Idx D N) : ℝ)⁻¹ * ((∑ k, |a k|) * Q) := by
      unfold ntr
      rw [norm_mul, norm_inv, Complex.norm_natCast, htr']
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hq k) (abs_nonneg _)
    have h2 : (Fintype.card (Idx D N) : ℝ)⁻¹ * (∑ k, |a k|) ≤
        (N : ℝ) ^ (-(1 / 2 : ℝ)) * ((1 + Kp) * hsNorm (lam D N (A N))) := by
      refine MultiRes_avg_bound _ N hN1 hnN _ _ _ (Finset.sum_nonneg fun k _ => abs_nonneg _)
        (by linarith) hL0 ?_
      refine (MultiRes_sum_abs_sq a).trans ?_
      have hh2 : MultiRes_hs2 (lam D N (A N) - (δ N : ℂ) •
          (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ ((1 + Kp) * hsNorm (lam D N (A N))) ^ 2 := by
        rw [mul_pow]; exact hhs
      rw [hsum]
      exact mul_le_mul_of_nonneg_left hh2 (Nat.cast_nonneg _)
    rw [hbnd, ← hTT]
    calc _ ≤ (Fintype.card (Idx D N) : ℝ)⁻¹ * ((∑ k, |a k|) * Q) := h1
      _ = ((Fintype.card (Idx D N) : ℝ)⁻¹ * (∑ k, |a k|)) * Q := by ring
      _ ≤ ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ((1 + Kp) * hsNorm (lam D N (A N)))) * Q :=
          mul_le_mul_of_nonneg_right h2 hQ0
      _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N (A N)) *
          ((MultiRes_CG τ c₀ * T + (MultiRes_CPsi c₀ * T + 5 / 4)) * Cext *
            ((if 2 ≤ l + 1 then β else 1) / ε ^ l)) := by
          rw [hQ, hCext]; ring
      _ ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N (A N)) *
          (T * T * ((if 2 ≤ l + 1 then β else 1) / ε ^ l)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAC hSb)
            (mul_nonneg (Real.rpow_nonneg hNpos.le _) hL0)
      _ = T * T * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * hsNorm (lam D N (A N)) *
          ((if 2 ≤ l + 1 then β else 1) / ε ^ l)) := by ring
  · simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith

/-- (A.55) [two_loop_estimate] of Lemma A.4 [lemma_necessary_estimates], `l₁ + l₂ ≥ 1`
(including `l₁ l₂ = 0`), conditional on (2.22) [eq:aniso_local] as the paper states it, in the
setting of `one_loop_estimate`: `⟨Π_{l₁} (Λ - δ₁) Π_{l₂} (Λ - δ₂)⟩ ≺
N^{-1} ‖Λ‖²_HS (max_i Im m_i)^{1(l₁ + l₂ ≥ 2)} η^{-(l₁ + l₂ - 1)}`. -/
theorem two_loop_estimate (D p l₁ l₂ : ℕ) (hp : 1 ≤ p) (hl : 1 ≤ l₁ + l₂) (τ c₀ C₀ K : ℝ)
    (hτ : 0 < τ) (hc₀ : 0 < c₀) (hC₀ : 1 ≤ C₀) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (H : ∀ N, Ω N → Matrix (Idx D N) (Idx D N) ℂ) (hH : ∀ N, ∀ᵐ ω ∂(P N), (H N ω).IsHermitian)
    (A : ∀ N, Matrix (Fin N) (Fin N) ℂ) (hA : ∀ N, 2 * C₀ * opNorm (A N) ≤ 1 / 10)
    (c : ℕ → Fin p → ℝ) (hc : ∀ N i, |c N i| ≤ C₀)
    (δ₁ δ₂ : ℕ → ℝ) (hδ₁ : ∀ N, |δ₁ N| ≤ K * avgSq (lam D N (A N)))
    (hδ₂ : ∀ N, |δ₂ N| ≤ K * avgSq (lam D N (A N)))
    (Z : ∀ N, Set (Fin p → ℂ))
    (hZ : ∀ N : ℕ, ∀ z ∈ Z N, ∀ i, 0 < (z i).im ∧ ‖z i‖ ≤ τ⁻¹ ∧
      c₀ ≤ (N : ℝ) * (z i).im * (mSol ((c N i : ℂ) • lam D N (A N)) (z i)).im)
    (hLL : ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ z ∈ Z N, ∀ i, ∀ u v : Idx D N → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → ∑ x, ‖v x‖ ^ 2 = 1 →
        P N {ω | (N : ℝ) ^ τ' * psiIso ((c N i : ℂ) • lam D N (A N)) N (z i) <
            ‖star u ⬝ᵥ ((res (H N ω + (c N i : ℂ) • lam D N (A N)) (z i) -
              MSol ((c N i : ℂ) • lam D N (A N)) (z i)) *ᵥ v)‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D'))) :
    ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z ∈ Z N,
      ∀ (w₁ : Fin l₁ → Fin p × Bool) (w₂ : Fin l₂ → Fin p × Bool)
        (B₁ : Fin (l₁ + 1) → Matrix (Idx D N) (Idx D N) ℂ)
        (B₂ : Fin (l₂ + 1) → Matrix (Idx D N) (Idx D N) ℂ),
      (∀ j, opNorm (B₁ j) ≤ K) → (∀ j, opNorm (B₂ j) ≤ K) →
        P N {ω | (N : ℝ) ^ τ' * (hsNorm (lam D N (A N)) ^ 2 / N *
              bndA4 (fun i => (mSol ((c N i : ℂ) • lam D N (A N)) (z i)).im)
                (fun i => (z i).im) (l₁ + l₂)) <
            ‖ntr (resWord (fun i => res (H N ω + (c N i : ℂ) • lam D N (A N)) (z i)) w₁ B₁ *
              (lam D N (A N) - (δ₁ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
              resWord (fun i => res (H N ω + (c N i : ℂ) • lam D N (A N)) (z i)) w₂ B₂ *
              (lam D N (A N) - (δ₂ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  have hC₀0 : 0 ≤ C₀ := by linarith
  have hlam : ∀ N, opNorm (lam D N (A N)) ≤ 1 / 10 := by
    intro N
    have h1 := MultiRes_opNorm_lam_le D N (A N)
    have h2 := MultiRes_opNorm_nonneg (A N)
    have h3 := hA N
    nlinarith
  have hΛ' : ∀ N (i : Fin p), (((c N i : ℝ) : ℂ) • lam D N (A N)).IsHermitian ∧
      opNorm (((c N i : ℝ) : ℂ) • lam D N (A N)) ≤ 1 / 10 := by
    intro N i
    refine ⟨MultiRes_smul_real_herm _ _ (lam_isHermitian D N (A N)), ?_⟩
    rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := MultiRes_opNorm_lam_le D N (A N)
    have h2 := MultiRes_opNorm_nonneg (A N)
    have h3 := hA N
    have h4 := hc N i
    have h5 := MultiRes_opNorm_nonneg (lam D N (A N))
    nlinarith [mul_le_mul h4 h1 h5 hC₀0]
  intro τ' hτ' D' hD'
  obtain ⟨N₁, hN₁⟩ := MultiRes_core (Λs := fun N i => ((c N i : ℝ) : ℂ) • lam D N (A N)) hp τ c₀
    hc₀ P H hΛ' Z hZ hLL τ' hτ' D' hD'
  set Kp : ℝ := max K 0 with hKp
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  have hKKp : K ≤ Kp := le_max_left _ _
  obtain ⟨N₂, hN₂⟩ := MultiRes_pow_ge (MultiRes_CW τ c₀ * (1 + Kp) ^ (l₁ + l₂ + 6)) (τ' / 2)
    (by positivity)
  refine ⟨max (max N₁ N₂) (4 * D + 2), fun N hN z hzN w₁ w₂ B₁ B₂ hB₁ hB₂ => ?_⟩
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : 4 * D + 2 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hN1, hne, hbad, hward⟩ := hN₁ N hNa z hzN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  set T : ℝ := (N : ℝ) ^ (τ' / 2) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
  have hTT : T * T = (N : ℝ) ^ τ' := by
    rw [hT, ← Real.rpow_add hNpos]; congr 1; ring
  have hηpos : ∀ i, 0 < (z i).im := fun i => (hZ N z hzN i).1
  have hμpos : ∀ i, 0 < (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im := by
    intro i
    obtain ⟨h1, -, h3⟩ := hZ N z hzN i
    by_contra hcon
    have : (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im ≤ 0 := not_lt.mp hcon
    nlinarith [mul_pos hNpos h1]
  obtain ⟨hε0, hεle, hβle, hβ0⟩ := MultiRes_iInf_iSup hp (fun i => (z i).im)
    (fun i => (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im) hηpos (fun i => (hμpos i).le)
  set ε : ℝ := ⨅ i, (z i).im with hε
  set β : ℝ := ⨆ i, (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im with hβ
  have hBp₁ : ∀ j, opNorm (B₁ j) ≤ Kp := fun j => (hB₁ j).trans hKKp
  have hBp₂ : ∀ j, opNorm (B₂ j) ≤ Kp := fun j => (hB₂ j).trans hKKp
  have hY₁ := MultiRes_sub_smul_one_herm (lam D N (A N)) (lam_isHermitian D N (A N)) (δ₁ N)
  have hY₂ := MultiRes_sub_smul_one_herm (lam D N (A N)) (lam_isHermitian D N (A N)) (δ₂ N)
  obtain ⟨a₁, u₁, hu1₁, hsum₁, htr₁, hhs₁, hcol₁⟩ := MultiRes_spec' _ hY₁
  obtain ⟨a₂, u₂, hu1₂, hsum₂, htr₂, hhs₂, hcol₂⟩ := MultiRes_spec' _ hY₂
  let Good : Ω N → Fin p → (Idx D N → ℂ) → (Idx D N → ℂ) → Prop :=
    fun ω i x y => MultiRes_GoodV N (τ' / 2) (H N ω + ((c N i : ℝ) : ℂ) • lam D N (A N))
      (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i) x y
  have hnull : P N {ω | ¬ (H N ω).IsHermitian} = 0 := MeasureTheory.ae_iff.mp (hH N)
  have hcard : (Fintype.card (Idx D N) : ℝ) = (D : ℝ) * N := by simp
  have hD1 : 1 ≤ D := by
    obtain ⟨⟨a, _⟩⟩ := hne
    exact Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact a.elim0)
  have hnN : (N : ℝ) ≤ Fintype.card (Idx D N) := by
    rw [hcard]
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    nlinarith
  have havg0 : 0 ≤ avgSq (lam D N (A N)) := by
    rw [MultiRes_avgSq_eq _ (lam_isHermitian D N (A N))]
    exact div_nonneg (MultiRes_hs2_nonneg _) (Nat.cast_nonneg _)
  have hL0 := MultiRes_hsNorm_nonneg (lam D N (A N))
  have hs0 : 0 ≤ (1 + Kp) * hsNorm (lam D N (A N)) := mul_nonneg (by linarith) hL0
  have hY₁s : MultiRes_hs2 (lam D N (A N) - (δ₁ N : ℂ) •
      (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ ((1 + Kp) * hsNorm (lam D N (A N))) ^ 2 := by
    rw [mul_pow, MultiRes_hsNorm_sq]
    exact MultiRes_hs2_shift _ (lam_isHermitian D N (A N)) (MultiRes_lam_diag D N (A N))
      (hlam N) Kp (δ₁ N) hKp0 ((hδ₁ N).trans (mul_le_mul_of_nonneg_right hKKp havg0))
  have hY₂s : MultiRes_hs2 (lam D N (A N) - (δ₂ N : ℂ) •
      (1 : Matrix (Idx D N) (Idx D N) ℂ)) ≤ ((1 + Kp) * hsNorm (lam D N (A N))) ^ 2 := by
    rw [mul_pow, MultiRes_hsNorm_sq]
    exact MultiRes_hs2_shift _ (lam_isHermitian D N (A N)) (MultiRes_lam_diag D N (A N))
      (hlam N) Kp (δ₂ N) hKp0 ((hδ₂ N).trans (mul_le_mul_of_nonneg_right hKKp havg0))
  have hcardle : Fintype.card (Idx D N) * 2 ≤ N * N := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith
  have hApos : 0 ≤ MultiRes_CG τ c₀ * T := mul_nonneg (MultiRes_CG_pos hc₀).le (by linarith)
  have hCLpos : 0 ≤ MultiRes_CPsi c₀ * T + 5 / 4 := by
    have := MultiRes_CPsi_pos hc₀
    positivity
  set AA : ℝ := MultiRes_CG τ c₀ * T + (MultiRes_CPsi c₀ * T + 5 / 4) with hAA
  have hAA0 : 0 ≤ AA := add_nonneg hApos hCLpos
  rcases l₁ with _ | l <;> rcases l₂ with _ | l'
  · omega
  · -- `l₁ = 0`, `l₂ = l' + 1`
    have hAC := MultiRes_AC_le τ c₀ T ((1 + Kp) ^ (0 + (l' + 1) + 6)) hc₀ hT1 (by positivity)
      (hN₂ N hNb)
    set Sb : ℝ := (if 2 ≤ l' + 1 then β else 1) / ε ^ l' with hSb_def
    have hSb : 0 ≤ Sb := div_nonneg (by split_ifs; exact hβ0; norm_num) (pow_nonneg hε0.le _)
    have hbnd : bndA4 (fun i => (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im)
        (fun i => (z i).im) (0 + (l' + 1)) = Sb := by
      simp [bndA4, hε, hβ, hSb_def]
    simp only [MultiRes_resWord_zero]
    refine MultiRes_union_final (P N)
      (fun k : Idx D N => {ω | ¬ (MultiRes_needL (Good ω) w₂ B₂
        ((B₁ 0 * (lam D N (A N) - (δ₁ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))ᴴ *ᵥ u₂ k)
        (u₂ k) ∧ MultiRes_needR (Good ω) w₂ B₂
        ((B₁ 0 * (lam D N (A N) - (δ₁ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))ᴴ *ᵥ u₂ k)
        (u₂ k))})
      2 N hN1 D' (fun k => MultiRes_ends_prob (P N) Good _ hbad _ _ _ _)
      {ω | ¬ (H N ω).IsHermitian} _ hnull ?_ hcardle
    intro ω hω0 hk
    have hω0' : (H N ω).IsHermitian := not_not.mp hω0
    simp only [Set.mem_ofPred_eq, not_lt]
    set Q₀ : ℝ := AA * Kp ^ (l' + 2) * Sb with hQ₀
    have hQ0 : 0 ≤ Q₀ := mul_nonneg (mul_nonneg hAA0 (pow_nonneg hKp0 _)) hSb
    have hq : ∀ k, ‖star ((B₁ 0 * (lam D N (A N) - (δ₁ N : ℂ) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ)))ᴴ *ᵥ u₂ k) ⬝ᵥ
        (resWord (fun i => res (H N ω + ((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)) w₂ B₂ *ᵥ
          u₂ k)‖ ≤ Q₀ * (MultiRes_vn ((B₁ 0 * (lam D N (A N) - (δ₁ N : ℂ) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ)))ᴴ *ᵥ u₂ k) * MultiRes_vn (u₂ k)) := fun k =>
      MultiRes_W1 (hward ω hω0') ε β Kp hε0 hεle hβle w₂ B₂ hBp₂ _ _
        (not_not.mp (hk k)).1 (not_not.mp (hk k)).2
    have htr := MultiRes_loop_one_det _ (B₁ 0) _ _ a₂ u₂ Kp _ _ Q₀ (hBp₁ 0) hKp0 hs0 hs0 hQ0
      hY₂s hY₁s hu1₂ hsum₂ htr₂ hcol₂ hq
    have hR : Q₀ * (Kp * ((1 + Kp) * hsNorm (lam D N (A N)) * ((1 + Kp) * hsNorm (lam D N (A N))))) ≤
        T * T * (hsNorm (lam D N (A N)) ^ 2 * Sb) := by
      have h1 : Kp ^ (l' + 2) * Kp * (1 + Kp) ^ 2 ≤ (1 + Kp) ^ (0 + (l' + 1) + 6) := by
        have := MultiRes_pow_comb Kp hKp0 2 (l' + 3) (0 + (l' + 1) + 6) (by omega)
        calc Kp ^ (l' + 2) * Kp * (1 + Kp) ^ 2 = (1 + Kp) ^ 2 * Kp ^ (l' + 3) := by ring
          _ ≤ _ := this
      have h2 : AA * (Kp ^ (l' + 2) * Kp * (1 + Kp) ^ 2) ≤ T * T :=
        (mul_le_mul_of_nonneg_left h1 hAA0).trans hAC
      calc Q₀ * (Kp * ((1 + Kp) * hsNorm (lam D N (A N)) * ((1 + Kp) * hsNorm (lam D N (A N)))))
          = (AA * (Kp ^ (l' + 2) * Kp * (1 + Kp) ^ 2)) * (hsNorm (lam D N (A N)) ^ 2 * Sb) := by
            rw [hQ₀]; ring
        _ ≤ T * T * (hsNorm (lam D N (A N)) ^ 2 * Sb) :=
            mul_le_mul_of_nonneg_right h2 (mul_nonneg (sq_nonneg _) hSb)
    have hfin := MultiRes_ntr_final (B₁ 0 * (lam D N (A N) - (δ₁ N : ℂ) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ)) * resWord (fun i => res (H N ω +
        ((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)) w₂ B₂ * (lam D N (A N) - (δ₂ N : ℂ) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ))) N hN1 hnN _ (T * T) _
      (by rw [MultiRes_trace_cyc]; exact htr) hR
    rw [hbnd, ← hTT]
    refine hfin.trans (le_of_eq ?_)
    ring
  · -- `l₁ = l + 1`, `l₂ = 0`
    have hAC := MultiRes_AC_le τ c₀ T ((1 + Kp) ^ (l + 1 + 0 + 6)) hc₀ hT1 (by positivity)
      (hN₂ N hNb)
    set Sb : ℝ := (if 2 ≤ l + 1 then β else 1) / ε ^ l with hSb_def
    have hSb : 0 ≤ Sb := div_nonneg (by split_ifs; exact hβ0; norm_num) (pow_nonneg hε0.le _)
    have hbnd : bndA4 (fun i => (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im)
        (fun i => (z i).im) (l + 1 + 0) = Sb := by
      simp [bndA4, hε, hβ, hSb_def]
    simp only [MultiRes_resWord_zero]
    refine MultiRes_union_final (P N)
      (fun k : Idx D N => {ω | ¬ (MultiRes_needL (Good ω) w₁ B₁
        ((B₂ 0 * (lam D N (A N) - (δ₂ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))ᴴ *ᵥ u₁ k)
        (u₁ k) ∧ MultiRes_needR (Good ω) w₁ B₁
        ((B₂ 0 * (lam D N (A N) - (δ₂ N : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))ᴴ *ᵥ u₁ k)
        (u₁ k))})
      2 N hN1 D' (fun k => MultiRes_ends_prob (P N) Good _ hbad _ _ _ _)
      {ω | ¬ (H N ω).IsHermitian} _ hnull ?_ hcardle
    intro ω hω0 hk
    have hω0' : (H N ω).IsHermitian := not_not.mp hω0
    simp only [Set.mem_ofPred_eq, not_lt]
    set Q₀ : ℝ := AA * Kp ^ (l + 2) * Sb with hQ₀
    have hQ0 : 0 ≤ Q₀ := mul_nonneg (mul_nonneg hAA0 (pow_nonneg hKp0 _)) hSb
    have hq : ∀ k, ‖star ((B₂ 0 * (lam D N (A N) - (δ₂ N : ℂ) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ)))ᴴ *ᵥ u₁ k) ⬝ᵥ
        (resWord (fun i => res (H N ω + ((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)) w₁ B₁ *ᵥ
          u₁ k)‖ ≤ Q₀ * (MultiRes_vn ((B₂ 0 * (lam D N (A N) - (δ₂ N : ℂ) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ)))ᴴ *ᵥ u₁ k) * MultiRes_vn (u₁ k)) := fun k =>
      MultiRes_W1 (hward ω hω0') ε β Kp hε0 hεle hβle w₁ B₁ hBp₁ _ _
        (not_not.mp (hk k)).1 (not_not.mp (hk k)).2
    have htr := MultiRes_loop_one_det _ (B₂ 0) _ _ a₁ u₁ Kp _ _ Q₀ (hBp₂ 0) hKp0 hs0 hs0 hQ0
      hY₁s hY₂s hu1₁ hsum₁ htr₁ hcol₁ hq
    have hR : Q₀ * (Kp * ((1 + Kp) * hsNorm (lam D N (A N)) * ((1 + Kp) * hsNorm (lam D N (A N))))) ≤
        T * T * (hsNorm (lam D N (A N)) ^ 2 * Sb) := by
      have h1 : Kp ^ (l + 2) * Kp * (1 + Kp) ^ 2 ≤ (1 + Kp) ^ (l + 1 + 0 + 6) := by
        have := MultiRes_pow_comb Kp hKp0 2 (l + 3) (l + 1 + 0 + 6) (by omega)
        calc Kp ^ (l + 2) * Kp * (1 + Kp) ^ 2 = (1 + Kp) ^ 2 * Kp ^ (l + 3) := by ring
          _ ≤ _ := this
      have h2 : AA * (Kp ^ (l + 2) * Kp * (1 + Kp) ^ 2) ≤ T * T :=
        (mul_le_mul_of_nonneg_left h1 hAA0).trans hAC
      calc Q₀ * (Kp * ((1 + Kp) * hsNorm (lam D N (A N)) * ((1 + Kp) * hsNorm (lam D N (A N)))))
          = (AA * (Kp ^ (l + 2) * Kp * (1 + Kp) ^ 2)) * (hsNorm (lam D N (A N)) ^ 2 * Sb) := by
            rw [hQ₀]; ring
        _ ≤ T * T * (hsNorm (lam D N (A N)) ^ 2 * Sb) :=
            mul_le_mul_of_nonneg_right h2 (mul_nonneg (sq_nonneg _) hSb)
    have hfin := MultiRes_ntr_final (resWord (fun i => res (H N ω +
        ((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)) w₁ B₁ * (lam D N (A N) - (δ₁ N : ℂ) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ)) * B₂ 0 * (lam D N (A N) - (δ₂ N : ℂ) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ))) N hN1 hnN _ (T * T) _ htr hR
    rw [hbnd, ← hTT]
    refine hfin.trans (le_of_eq ?_)
    ring
  · -- `l₁ = l + 1`, `l₂ = l' + 1`
    have hAC := MultiRes_AC_le τ c₀ T ((1 + Kp) ^ (l + 1 + (l' + 1) + 6)) hc₀ hT1
      (by positivity) (hN₂ N hNb)
    set Sb : ℝ := β / ε ^ (l + l' + 1) with hSb_def
    have hSb : 0 ≤ Sb := div_nonneg hβ0 (pow_nonneg hε0.le _)
    have hbnd : bndA4 (fun i => (mSol (((c N i : ℝ) : ℂ) • lam D N (A N)) (z i)).im)
        (fun i => (z i).im) (l + 1 + (l' + 1)) = Sb := by
      have h2 : 2 ≤ l + 1 + (l' + 1) := by omega
      have h3 : l + 1 + (l' + 1) - 1 = l + l' + 1 := by omega
      simp [bndA4, hε, hβ, hSb_def, h2, h3]
    refine MultiRes_union_final (P N)
      (fun k : Idx D N => {ω | ¬ (MultiRes_needW2 (Good ω) w₁ B₁ (u₁ k) ∧
        MultiRes_needW2 (Good ω) w₂ B₂ (u₂ k))})
      2 N hN1 D' (fun k => MultiRes_and_prob (P N) _ _ _ (hbad _ _ _) (hbad _ _ _))
      {ω | ¬ (H N ω).IsHermitian} _ hnull ?_ hcardle
    intro ω hω0 hk
    have hω0' : (H N ω).IsHermitian := not_not.mp hω0
    simp only [Set.mem_ofPred_eq, not_lt]
    set ρ₁ : ℝ := MultiRes_CG τ c₀ * T * (β / ε) * Kp ^ (2 * l + 4) / ε ^ (2 * l) with hρ₁
    set ρ₂ : ℝ := MultiRes_CG τ c₀ * T * (β / ε) * Kp ^ (2 * l' + 4) / ε ^ (2 * l') with hρ₂
    set ρ : ℝ := MultiRes_CG τ c₀ * T * (β / ε) * Kp ^ (l + l' + 4) / ε ^ (l + l') with hρ
    have hCGT : 0 ≤ MultiRes_CG τ c₀ * T := hApos
    have hρ₁0 : 0 ≤ ρ₁ := by
      rw [hρ₁]; exact div_nonneg (mul_nonneg (mul_nonneg hCGT (div_nonneg hβ0 hε0.le))
        (pow_nonneg hKp0 _)) (pow_nonneg hε0.le _)
    have hρ₂0 : 0 ≤ ρ₂ := by
      rw [hρ₂]; exact div_nonneg (mul_nonneg (mul_nonneg hCGT (div_nonneg hβ0 hε0.le))
        (pow_nonneg hKp0 _)) (pow_nonneg hε0.le _)
    have hρ0 : 0 ≤ ρ := by
      rw [hρ]; exact div_nonneg (mul_nonneg (mul_nonneg hCGT (div_nonneg hβ0 hε0.le))
        (pow_nonneg hKp0 _)) (pow_nonneg hε0.le _)
    have hρρ : ρ₁ * ρ₂ ≤ ρ ^ 2 := by
      refine le_of_eq ?_
      rw [hρ₁, hρ₂, hρ]
      field_simp
      ring
    have hw₁ : ∀ k, MultiRes_vn (resWord (fun i => res (H N ω + ((c N i : ℝ) : ℂ) •
        lam D N (A N)) (z i)) w₁ B₁ *ᵥ u₁ k) ^ 2 ≤ ρ₁ := by
      intro k
      have h := MultiRes_W2 (hward ω hω0') ε β Kp hε0 hεle hβle w₁ B₁ hBp₁ (u₁ k)
        (not_not.mp (hk k)).1
      rw [hu1₁ k] at h
      simpa using h
    have hw₂ : ∀ k, MultiRes_vn (resWord (fun i => res (H N ω + ((c N i : ℝ) : ℂ) •
        lam D N (A N)) (z i)) w₂ B₂ *ᵥ u₂ k) ^ 2 ≤ ρ₂ := by
      intro k
      have h := MultiRes_W2 (hward ω hω0') ε β Kp hε0 hεle hβle w₂ B₂ hBp₂ (u₂ k)
        (not_not.mp (hk k)).2
      rw [hu1₂ k] at h
      simpa using h
    have h₁ : MultiRes_hs2 (resWord (fun i => res (H N ω + ((c N i : ℝ) : ℂ) •
        lam D N (A N)) (z i)) w₁ B₁ * (lam D N (A N) - (δ₁ N : ℂ) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ))) ≤
        ρ₁ * ((1 + Kp) * hsNorm (lam D N (A N))) ^ 2 := by
      rw [hhs₁]
      calc ∑ k, a₁ k ^ 2 * MultiRes_vn (resWord (fun i => res (H N ω + ((c N i : ℝ) : ℂ) •
            lam D N (A N)) (z i)) w₁ B₁ *ᵥ u₁ k) ^ 2 ≤ ∑ k, a₁ k ^ 2 * ρ₁ :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hw₁ k) (sq_nonneg _)
        _ = ρ₁ * ∑ k, a₁ k ^ 2 := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
        _ ≤ ρ₁ * ((1 + Kp) * hsNorm (lam D N (A N))) ^ 2 := by
            rw [hsum₁]; exact mul_le_mul_of_nonneg_left hY₁s hρ₁0
    have h₂ : MultiRes_hs2 (resWord (fun i => res (H N ω + ((c N i : ℝ) : ℂ) •
        lam D N (A N)) (z i)) w₂ B₂ * (lam D N (A N) - (δ₂ N : ℂ) •
        (1 : Matrix (Idx D N) (Idx D N) ℂ))) ≤
        ρ₂ * ((1 + Kp) * hsNorm (lam D N (A N))) ^ 2 := by
      rw [hhs₂]
      calc ∑ k, a₂ k ^ 2 * MultiRes_vn (resWord (fun i => res (H N ω + ((c N i : ℝ) : ℂ) •
            lam D N (A N)) (z i)) w₂ B₂ *ᵥ u₂ k) ^ 2 ≤ ∑ k, a₂ k ^ 2 * ρ₂ :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hw₂ k) (sq_nonneg _)
        _ = ρ₂ * ∑ k, a₂ k ^ 2 := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
        _ ≤ ρ₂ * ((1 + Kp) * hsNorm (lam D N (A N))) ^ 2 := by
            rw [hsum₂]; exact mul_le_mul_of_nonneg_left hY₂s hρ₂0
    have htr := MultiRes_loop_both_det _ _ _ _ ρ₁ ρ₂ ρ _ _ hρ0 hs0 hs0 hρ₁0 hρ₂0 hρρ h₁ h₂
    have hR : ρ * ((1 + Kp) * hsNorm (lam D N (A N)) * ((1 + Kp) * hsNorm (lam D N (A N)))) ≤
        T * T * (hsNorm (lam D N (A N)) ^ 2 * Sb) := by
      have h1 : (1 + Kp) ^ 2 * Kp ^ (l + l' + 4) ≤ (1 + Kp) ^ (l + 1 + (l' + 1) + 6) :=
        MultiRes_pow_comb Kp hKp0 2 (l + l' + 4) (l + 1 + (l' + 1) + 6) (by omega)
      have h2 : AA * ((1 + Kp) ^ 2 * Kp ^ (l + l' + 4)) ≤ T * T :=
        (mul_le_mul_of_nonneg_left h1 hAA0).trans hAC
      have hCG : MultiRes_CG τ c₀ * T ≤ AA := by
        rw [hAA]; linarith
      calc ρ * ((1 + Kp) * hsNorm (lam D N (A N)) * ((1 + Kp) * hsNorm (lam D N (A N))))
          = (MultiRes_CG τ c₀ * T * ((1 + Kp) ^ 2 * Kp ^ (l + l' + 4))) *
            (hsNorm (lam D N (A N)) ^ 2 * Sb) := by
            rw [hρ, hSb_def]
            field_simp
            ring
        _ ≤ (AA * ((1 + Kp) ^ 2 * Kp ^ (l + l' + 4))) * (hsNorm (lam D N (A N)) ^ 2 * Sb) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCG (by positivity))
              (mul_nonneg (sq_nonneg _) hSb)
        _ ≤ T * T * (hsNorm (lam D N (A N)) ^ 2 * Sb) :=
            mul_le_mul_of_nonneg_right h2 (mul_nonneg (sq_nonneg _) hSb)
    have hfin := MultiRes_ntr_final _ N hN1 hnN _ (T * T) _ htr hR
    rw [hbnd, ← hTT]
    refine hfin.trans (le_of_eq ?_)
    ring

end RBMTransitionEdge

end
