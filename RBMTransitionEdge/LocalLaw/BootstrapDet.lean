module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Det.Core
public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.Tools.Resolvent
public import RBMTransitionEdge.Tools.ResolventIdentities
public import RBMTransitionEdge.LocalLaw.Class
public import RBMTransitionEdge.LocalLaw.Dyson
public import RBMTransitionEdge.LocalLaw.DysonBounds

@[expose] public section

/-!
# Deterministic tools of the continuity argument

The resolvent `R_x` of the self-consistent equation at block traces `x`, its expansion around
`m 1`, the identity `G = R_x̃ - R_x̃ H̲G`, the transfer of resolvent bounds to a lower spectral
parameter, Lipschitz bounds for (2.16) [self_m], (2.17) [def_G0] and the control parameter of
(2.22) [eq:aniso_local], and the continuity step along a vertical line, for the bootstrap that
proves Lemma 2.9 [lem_loc].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- `R_x = (Λ - z - Σ_b x_b E_b)⁻¹` for `x ∈ ℂ^D`, the resolvent of the self-consistent equation
at the block traces `x`. -/
def resX {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) (x : Fin D → ℂ) :
    Matrix (Idx D N) (Idx D N) ℂ :=
  (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - (∑ b, x b • Ea D N b))⁻¹

/-- `s^* M^* s` is the complex conjugate of `s^* M s`; for Hermitian `M` the form `s^* M s` is real. -/
private lemma BootstrapDet_dot_conj {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ)
    (s : ι → ℂ) : star s ⬝ᵥ (Mᴴ *ᵥ s) = star (star s ⬝ᵥ (M *ᵥ s)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply, star_sum,
    star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- If `Im s^* Y s ≤ -c |s|²` for every `s`, then `c ‖v‖ ≤ ‖Y v‖` in the Euclidean norm: `|s^* Y s| ≤ |s| |Y s|`. -/
private lemma BootstrapDet_lower {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) (c : ℝ)
    (h : ∀ s : ι → ℂ, c * ∑ i, ‖s i‖ ^ 2 ≤ -(star s ⬝ᵥ (Y *ᵥ s)).im)
    (v : EuclideanSpace ℂ ι) : c * ‖v‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Y v‖ := by
  obtain ⟨s, rfl⟩ : ∃ s, v = WithLp.toLp 2 s := ⟨v.ofLp, rfl⟩
  have e : star s ⬝ᵥ (Y *ᵥ s) =
      inner ℂ (WithLp.toLp 2 s) (Matrix.toEuclideanCLM (𝕜 := ℂ) Y (WithLp.toLp 2 s)) := by
    change _ = inner ℂ (WithLp.toLp 2 s) (Matrix.toEuclideanLin Y (WithLp.toLp 2 s))
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
  have hs' : ‖(WithLp.toLp 2 s : EuclideanSpace ℂ ι)‖ ^ 2 = ∑ i, ‖s i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  have h1 := h s
  rw [e, ← hs'] at h1
  have h2 : -(inner ℂ (WithLp.toLp 2 s)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) Y (WithLp.toLp 2 s))).im ≤
      ‖(WithLp.toLp 2 s : EuclideanSpace ℂ ι)‖ *
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Y (WithLp.toLp 2 s)‖ :=
    (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _))
  have h3 := h1.trans h2
  rcases (norm_nonneg (WithLp.toLp 2 s : EuclideanSpace ℂ ι)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · refine le_of_mul_le_mul_left ?_ hpos
    nlinarith [h3]

/-- A matrix `Y` bounded below by `c > 0` in the Euclidean norm satisfies `Y Y⁻¹ = 1` and `‖Y⁻¹‖ ≤ c⁻¹`. -/
private lemma BootstrapDet_inv {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) (c : ℝ)
    (hc : 0 < c) (h : ∀ v : EuclideanSpace ℂ ι, c * ‖v‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Y v‖) :
    Y * Y⁻¹ = 1 ∧ opNorm Y⁻¹ ≤ c⁻¹ := by
  have hU : IsUnit Y := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro a b hab
    have h0 : (Y *ᵥ (a - b)) = 0 := by
      rw [Matrix.mulVec_sub, hab, sub_self]
    have key := h (WithLp.toLp 2 (a - b))
    have h00 : Matrix.toEuclideanCLM (𝕜 := ℂ) Y (WithLp.toLp 2 (a - b)) = 0 := by
      rw [Matrix.toEuclideanCLM_toLp, h0]
      rfl
    rw [h00, norm_zero] at key
    have hn : ‖(WithLp.toLp 2 (a - b) : EuclideanSpace ℂ ι)‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      by_contra hcc
      rw [not_le] at hcc
      nlinarith [mul_pos hc hcc]
    rw [norm_eq_zero] at hn
    exact sub_eq_zero.mp (by simpa using congrArg WithLp.ofLp hn)
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have h1 : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  refine ⟨h1, ?_⟩
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le) fun u => ?_
  have h2 : Matrix.toEuclideanCLM (𝕜 := ℂ) Y
      (Matrix.toEuclideanCLM (𝕜 := ℂ) Y⁻¹ u) = u := by
    rw [← mul_apply_eq_comp, ← map_mul, h1, map_one]
    rfl
  have key := h (Matrix.toEuclideanCLM (𝕜 := ℂ) Y⁻¹ u)
  rw [h2] at key
  rw [inv_mul_eq_div, le_div_iff₀ hc]
  linarith

/-- `Σ_b y_b E_b` is the diagonal matrix with entry `y_a` at every index of the block `a`. -/
private lemma BootstrapDet_sum_Ea (D N : ℕ) (y : Fin D → ℂ) :
    ∑ b, y b • Ea D N b = Matrix.diagonal (fun p : Idx D N => y p.1) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Ea, Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : p = q
  · subst h
    simp
  · simp [h]

/-- For Hermitian `Λ`, `Im z > 0` and `Im x_b ≥ 0` for every `b`, `R_x` is a true inverse and
`‖R_x‖ ≤ (Im z)⁻¹`. -/
theorem resX_spec {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (z : ℂ)
    (hz : 0 < z.im) (x : Fin D → ℂ) (hx : ∀ b, 0 ≤ (x b).im) :
    (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - (∑ b, x b • Ea D N b)) * resX Λ z x = 1 ∧
      opNorm (resX Λ z x) ≤ z.im⁻¹ := by
  have hT : Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - (∑ b, x b • Ea D N b) =
      Λ - Matrix.diagonal (fun p : Idx D N => z + x p.1) := by
    rw [BootstrapDet_sum_Ea, Matrix.smul_one_eq_diagonal, sub_sub, Matrix.diagonal_add]
  have hlow : ∀ s : Idx D N → ℂ, z.im * ∑ i, ‖s i‖ ^ 2 ≤
      -(star s ⬝ᵥ ((Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - (∑ b, x b • Ea D N b)) *ᵥ s)).im := by
    intro s
    rw [hT, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im]
    have h1 : (star s ⬝ᵥ (Λ *ᵥ s)).im = 0 := by
      have := BootstrapDet_dot_conj Λ s
      rw [hΛ.eq] at this
      have h2 := congrArg Complex.im this
      simp only [Complex.star_def, Complex.conj_im] at h2
      linarith
    have h3 : (star s ⬝ᵥ (Matrix.diagonal (fun p : Idx D N => z + x p.1) *ᵥ s)).im =
        ∑ p, (z.im + (x p.1).im) * ‖s p‖ ^ 2 := by
      simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.im_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      have : star (s p) * ((z + x p.1) * s p) = (z + x p.1) * ((‖s p‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_left_comm, Complex.star_def, Complex.conj_mul']
        push_cast
        ring
      rw [this, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.add_im]
      ring
    rw [h1, h3, Finset.mul_sum]
    have : ∀ p ∈ (Finset.univ : Finset (Idx D N)), z.im * ‖s p‖ ^ 2 ≤ (z.im + (x p.1).im) * ‖s p‖ ^ 2 := by
      intro p _
      have := hx p.1
      nlinarith [sq_nonneg ‖s p‖]
    have := Finset.sum_le_sum this
    linarith
  have hlow' := BootstrapDet_lower _ z.im hlow
  obtain ⟨h1, h2⟩ := BootstrapDet_inv _ z.im hz hlow'
  exact ⟨h1, h2⟩

/-- The normalized trace is additive. -/
private lemma BootstrapDet_ntr_add {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P + Q) = ntr P + ntr Q := by
  simp [ntr, Matrix.trace_add, mul_add]

/-- The normalized trace is homogeneous. -/
private lemma BootstrapDet_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (P : Matrix ι ι ℂ) :
    ntr (c • P) = c * ntr P := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

/-- The normalized trace of a finite sum is the sum of the normalized traces. -/
private lemma BootstrapDet_ntr_sum {ι κ : Type*} [Fintype ι] (s : Finset κ)
    (P : κ → Matrix ι ι ℂ) : ntr (∑ b ∈ s, P b) = ∑ b ∈ s, ntr (P b) := by
  simp [ntr, Matrix.trace_sum, Finset.mul_sum]

/-- The normalized trace is cyclic: `⟨P Q⟩ = ⟨Q P⟩`. -/
private lemma BootstrapDet_ntr_comm {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P * Q) = ntr (Q * P) := by
  simp [ntr, Matrix.trace_mul_comm P Q]

/-- The normalized trace of `P Y Q` for `Y = Σ_b y_b E_b` is `Σ_b y_b ⟨P E_b Q⟩`. -/
private lemma BootstrapDet_ntr_mid (D N : ℕ) (P Q Y : Matrix (Idx D N) (Idx D N) ℂ)
    (y : Fin D → ℂ) (hY : Y = ∑ b, y b • Ea D N b) :
    ntr (P * Y * Q) = ∑ b, y b * ntr (P * Ea D N b * Q) := by
  rw [hY, Finset.mul_sum, Finset.sum_mul, BootstrapDet_ntr_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, BootstrapDet_ntr_smul]

/-- The normalized trace on an empty index type vanishes. -/
private lemma BootstrapDet_ntr_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (B : Matrix ι ι ℂ) :
    ntr B = 0 := by
  simp [ntr, Matrix.trace]

/-- The operator norm is nonnegative. -/
private lemma BootstrapDet_opNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    0 ≤ opNorm X := norm_nonneg _

/-- The operator norm of a product of matrices with bounded norms. -/
private lemma BootstrapDet_opNorm_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ}
    {x y : ℝ} (hX : opNorm X ≤ x) (hY : opNorm Y ≤ y) : opNorm (X * Y) ≤ x * y :=
  (opNorm_mul_le X Y).trans
    (mul_le_mul hX hY (BootstrapDet_opNorm_nonneg Y) ((BootstrapDet_opNorm_nonneg X).trans hX))

/-- `|D⟨E_a W⟩| ≤ B` when the diagonal entries of `W` are at most `B` in modulus. -/
private lemma BootstrapDet_blk_le (D N : ℕ) (a : Fin D) (W : Matrix (Idx D N) (Idx D N) ℂ)
    (B : ℝ) (hB : 0 ≤ B) (h : ∀ p, ‖W p p‖ ≤ B) : ‖(D : ℂ) * ntr (Ea D N a * W)‖ ≤ B := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : IsEmpty (Idx D 0) := ⟨fun p => p.2.elim0⟩
    simp [BootstrapDet_ntr_of_isEmpty, hB]
  · have hD : 0 < D := a.pos
    have htr : (Ea D N a * W).trace = ∑ p : Idx D N, if p.1 = a then W p p else 0 := by
      simp [Matrix.trace, Ea, Matrix.diagonal_mul]
    have hsum : ‖∑ p : Idx D N, if p.1 = a then W p p else 0‖ ≤ N * B := by
      calc ‖∑ p : Idx D N, if p.1 = a then W p p else 0‖
          ≤ ∑ p : Idx D N, ‖if p.1 = a then W p p else 0‖ := norm_sum_le _ _
        _ ≤ ∑ p : Idx D N, if p.1 = a then B else 0 :=
          Finset.sum_le_sum fun p _ => by split_ifs <;> simp [h p]
        _ = N * B := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          simp
    unfold ntr
    rw [htr]
    have hDN : (0 : ℝ) < D * N := by positivity
    calc ‖(D : ℂ) * (((Fintype.card (Idx D N) : ℕ) : ℂ)⁻¹ *
          ∑ p : Idx D N, if p.1 = a then W p p else 0)‖
        = D * (D * N : ℝ)⁻¹ * ‖∑ p : Idx D N, if p.1 = a then W p p else 0‖ := by
          rw [norm_mul, norm_mul, norm_inv]
          simp [Fintype.card_prod]
          ring
      _ ≤ D * (D * N : ℝ)⁻¹ * (N * B) := by gcongr
      _ = B := by field_simp

/-- `|D⟨E_a W⟩| ≤ ‖W‖`. -/
private lemma BootstrapDet_blk_opNorm (D N : ℕ) (a : Fin D) (W : Matrix (Idx D N) (Idx D N) ℂ) :
    ‖(D : ℂ) * ntr (Ea D N a * W)‖ ≤ opNorm W :=
  BootstrapDet_blk_le D N a W _ (BootstrapDet_opNorm_nonneg W) (fun p => norm_apply_le_opNorm W p p)

/-- The block projections sum to the identity. -/
private lemma BootstrapDet_sum_Ea_one (D N : ℕ) : ∑ a : Fin D, Ea D N a = 1 := by
  ext p q
  simp [Ea, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]

open scoped Matrix.Norms.L2Operator in
/-- The operator norm of a diagonal matrix is the sup norm of its diagonal. -/
private lemma BootstrapDet_opNorm_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    opNorm (Matrix.diagonal v) = ‖v‖ := by
  unfold opNorm
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]

/-- `(σ_θ x)_a = θ x_a + (1 - θ) D⁻¹ Σ_b x_b`. -/
private lemma BootstrapDet_sig_apply (D : ℕ) (θ : ℝ) (x : Fin D → ℂ) (a : Fin D) :
    (sigTheta D θ *ᵥ x) a =
      (θ : ℂ) * x a + ((1 - θ : ℝ) : ℂ) * ((D : ℂ)⁻¹ * ∑ b, x b) := by
  have hJ : (Matrix.of fun (_ _ : Fin D) => (1 : ℂ)) *ᵥ x = fun _ => ∑ b, x b := by
    ext
    simp [Matrix.mulVec, dotProduct]
  simp only [sigTheta, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hJ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- `|(σ_θ x)_a| ≤ |x|_∞` for `θ ∈ [0, 1]`. -/
private lemma BootstrapDet_sig_linf (D : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : Fin D → ℂ)
    (a : Fin D) : ‖(sigTheta D θ *ᵥ x) a‖ ≤ ‖x‖ := by
  have hD : 0 < D := a.pos
  have hx : ∀ b, ‖x b‖ ≤ ‖x‖ := fun b => norm_le_pi_norm x b
  rw [BootstrapDet_sig_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (by linarith), norm_inv,
    Complex.norm_natCast]
  have h2 : (D : ℝ)⁻¹ * ‖∑ b, x b‖ ≤ ‖x‖ := by
    have : ‖∑ b, x b‖ ≤ D * ‖x‖ := by
      calc ‖∑ b, x b‖ ≤ ∑ b, ‖x b‖ := norm_sum_le _ _
        _ ≤ ∑ _b : Fin D, ‖x‖ := Finset.sum_le_sum fun b _ => hx b
        _ = D * ‖x‖ := by simp
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    calc (D : ℝ)⁻¹ * ‖∑ b, x b‖ ≤ (D : ℝ)⁻¹ * (D * ‖x‖) := by gcongr
      _ = ‖x‖ := by field_simp
  nlinarith [hx a, norm_nonneg x]

/-- `σ_θ` fixes constant vectors for `D ≥ 1`. -/
private lemma BootstrapDet_sig_one (D : ℕ) (hD : 1 ≤ D) (θ : ℝ) (m : ℂ) :
    (sigTheta D θ *ᵥ fun _ => m) = fun _ => m := by
  funext a
  rw [BootstrapDet_sig_apply]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  push_cast
  field_simp
  ring

/-- `D⟨M E_a⟩ = m` for every block, for `D ≥ 1`, `N ≥ 1` and `z ∉ ℝ`: the diagonal blocks of (2.17) [def_G0] have the normalized trace (2.16) [self_m]. -/
private lemma BootstrapDet_blk_M (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : z.im ≠ 0) (a : Fin D) :
    (D : ℂ) * ntr (MExt (lam D N A) z * Ea D N a) = mExt (lam D N A) z := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  obtain ⟨hm, -, -⟩ := MExt_spec (lam D N A) (lam_isHermitian D N A) z hz
  by_cases h2 : 2 ≤ D
  · exact (def_M_scalar D h2 N hN A z hz).1 a
  · obtain rfl : D = 1 := by omega
    have hE : Ea 1 N a = 1 := by
      ext p q
      have : p.1 = a := Subsingleton.elim _ _
      simp [Ea, Matrix.diagonal_apply, Matrix.one_apply, this]
    rw [hE, Matrix.mul_one, ← hm]
    simp

/-- The second and third order terms of `R = M + R Δ M` with `Δ = Σ_b d_b E_b`: `D⟨E_a M Δ M⟩ = Σ_b M̂_{ab} d_b` and `D⟨E_a M Δ M Δ M⟩ = Σ_{b,c} q_{abc} d_b d_c`, with `M̂` of (3.1) [def_ML]. -/
private lemma BootstrapDet_terms (D N : ℕ) (M Δ : Matrix (Idx D N) (Idx D N) ℂ) (d : Fin D → ℂ)
    (hΔ : Δ = ∑ b, d b • Ea D N b) (a : Fin D) :
    (D : ℂ) * ntr (Ea D N a * (M * Δ * M)) =
      ∑ b, ((D : ℂ) * ntr (M * Ea D N a * M * Ea D N b)) * d b ∧
    (D : ℂ) * ntr (Ea D N a * (M * Δ * (M * Δ * M))) =
      ∑ b, ∑ c, ((D : ℂ) * ntr (Ea D N a * M * Ea D N b * M * Ea D N c * M)) * d b * d c := by
  have hcyc : ∀ b, ntr (M * Ea D N a * M * Ea D N b) = ntr (Ea D N a * M * Ea D N b * M) := by
    intro b
    have : M * Ea D N a * M * Ea D N b = M * (Ea D N a * M * Ea D N b) := by
      simp only [Matrix.mul_assoc]
    rw [this, BootstrapDet_ntr_comm]
  constructor
  · have := BootstrapDet_ntr_mid D N (Ea D N a * M) M Δ d hΔ
    simp only [Matrix.mul_assoc] at this ⊢
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h2 := hcyc b
    simp only [Matrix.mul_assoc] at h2
    rw [h2]
    ring
  · have e1 := BootstrapDet_ntr_mid D N (Ea D N a * M) (M * Δ * M) Δ d hΔ
    have e2 : ∀ b, ntr (Ea D N a * M * Ea D N b * (M * Δ * M)) =
        ∑ c, d c * ntr (Ea D N a * M * Ea D N b * M * Ea D N c * M) := fun b => by
      have := BootstrapDet_ntr_mid D N (Ea D N a * M * Ea D N b * M) M Δ d hΔ
      simp only [Matrix.mul_assoc] at this ⊢
      exact this
    simp only [e2] at e1
    simp only [Matrix.mul_assoc] at e1 ⊢
    rw [e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring

/-- The expansion of the self-consistent map at the block traces `m + x`, `|x|_∞ ≤ 2/5`, for
`‖M‖ ≤ 5/4`, `Im z > 0`, `θ ∈ [0, 1]`: with `y = σ_θ(m 1 + x)` and `R_y = (Λ - z - Σ_b y_b E_b)⁻¹`,
`R_y` is a true inverse, `‖R_y - M‖ ≤ (25/8) |x|_∞`, and
`|D⟨E_a R_y⟩ - m - (M̂ σ_θ x)_a - Q(σ_θ x)_a| ≤ 5 |x|_∞³` for every block `a`, with `M̂ = M̂(z, z)` of
(3.1) [def_ML] and `Q(y)_a = Σ_{b,c} q_{abc} y_b y_c`. -/
theorem resX_taylor (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : 0 < z.im)
    (hM : opNorm (MExt (lam D N A) z) ≤ 5 / 4) (x : Fin D → ℂ) (hx : ‖x‖ ≤ 2 / 5) :
    (lam D N A - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) -
        ∑ b, (sigTheta D θ *ᵥ fun a => mExt (lam D N A) z + x a) b • Ea D N b) *
        resX (lam D N A) z (sigTheta D θ *ᵥ fun a => mExt (lam D N A) z + x a) = 1 ∧
      opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ fun a => mExt (lam D N A) z + x a) -
        MExt (lam D N A) z) ≤ 25 / 8 * ‖x‖ ∧
      ‖blockTr D N (resX (lam D N A) z (sigTheta D θ *ᵥ fun a => mExt (lam D N A) z + x a)) -
          (fun _ => mExt (lam D N A) z) - Mhat (lam D N A) z z *ᵥ (sigTheta D θ *ᵥ x) -
          quadForm (qTensor (lam D N A) z) (sigTheta D θ *ᵥ x)‖ ≤ 5 * ‖x‖ ^ 3 := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hΛh := lam_isHermitian D N A
  obtain ⟨hm_tr, hKM, -⟩ := MExt_spec (lam D N A) hΛh z hz.ne'
  have hblk := BootstrapDet_blk_M D N hD hN A z hz.ne'
  have hy : (sigTheta D θ *ᵥ fun a => mExt (lam D N A) z + x a) =
      fun a => mExt (lam D N A) z + (sigTheta D θ *ᵥ x) a := by
    have h1 : (fun a => mExt (lam D N A) z + x a) = (fun _ => mExt (lam D N A) z) + x := rfl
    rw [h1, Matrix.mulVec_add, BootstrapDet_sig_one D hD]
    rfl
  rw [hy]
  have hd0 : ∀ a, ‖(sigTheta D θ *ᵥ x) a‖ ≤ ‖x‖ := BootstrapDet_sig_linf D θ hθ0 hθ1 x
  have hQ : quadForm (qTensor (lam D N A) z) (sigTheta D θ *ᵥ x) = fun a => ∑ b, ∑ c,
      ((D : ℂ) * ntr (Ea D N a * MExt (lam D N A) z * Ea D N b * MExt (lam D N A) z * Ea D N c *
        MExt (lam D N A) z)) * (sigTheta D θ *ᵥ x) b * (sigTheta D θ *ᵥ x) c := by
    funext a
    rfl
  have hMv : Mhat (lam D N A) z z *ᵥ (sigTheta D θ *ᵥ x) = fun a => ∑ b,
      ((D : ℂ) * ntr (MExt (lam D N A) z * Ea D N a * MExt (lam D N A) z * Ea D N b)) *
        (sigTheta D θ *ᵥ x) b := by
    funext a
    rfl
  rw [hQ, hMv]
  generalize sigTheta D θ *ᵥ x = d at hd0 ⊢
  generalize hMM : MExt (lam D N A) z = M at hM hKM hblk ⊢
  generalize hmm : mExt (lam D N A) z = m at hKM hblk ⊢
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  set K : Matrix (Idx D N) (Idx D N) ℂ := lam D N A - (z + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)
    with hKdef
  set Δ : Matrix (Idx D N) (Idx D N) ℂ := ∑ b, d b • Ea D N b with hΔdef
  have hMK : M * K = 1 := mul_eq_one_comm.mp hKM
  have hT : lam D N A - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - ∑ b, (m + d b) • Ea D N b =
      K - Δ := by
    simp only [add_smul, Finset.sum_add_distrib, ← Finset.smul_sum, BootstrapDet_sum_Ea_one, hKdef, hΔdef]
    abel
  have hRx : resX (lam D N A) z (fun a => m + d a) = (K - Δ)⁻¹ := by
    unfold resX
    congr 1
  have hΔn : opNorm Δ ≤ ‖x‖ := by
    rw [hΔdef, BootstrapDet_sum_Ea, BootstrapDet_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hx0).mpr fun p => hd0 p.1
  have hlow : ∀ v : EuclideanSpace ℂ (Idx D N), (2 / 5 : ℝ) * ‖v‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (K - Δ) v‖ := by
    intro v
    have hv : v = Matrix.toEuclideanCLM (𝕜 := ℂ) M (Matrix.toEuclideanCLM (𝕜 := ℂ) K v) := by
      rw [← mul_apply_eq_comp, ← map_mul, hMK, map_one]
      rfl
    have h1 : ‖v‖ ≤ opNorm M * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) K v‖ := by
      calc ‖v‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M (Matrix.toEuclideanCLM (𝕜 := ℂ) K v)‖ := by
            rw [← hv]
        _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) K v‖ :=
            ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Δ v‖ ≤ opNorm Δ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h3 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) K v‖ -
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Δ v‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (K - Δ) v‖ := by
      have e : Matrix.toEuclideanCLM (𝕜 := ℂ) (K - Δ) v =
          Matrix.toEuclideanCLM (𝕜 := ℂ) K v - Matrix.toEuclideanCLM (𝕜 := ℂ) Δ v := by
        simp
      rw [e]
      exact norm_sub_norm_le _ _
    have h4 : opNorm M * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) K v‖ ≤
        5 / 4 * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) K v‖ :=
      mul_le_mul_of_nonneg_right hM (norm_nonneg _)
    have h5 : opNorm Δ * ‖v‖ ≤ 2 / 5 * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hΔn.trans hx) (norm_nonneg _)
    linarith
  obtain ⟨hinv, hRn'⟩ := BootstrapDet_inv _ (2 / 5) (by norm_num) hlow
  have hRn : opNorm (K - Δ)⁻¹ ≤ 5 / 2 := by
    refine hRn'.trans ?_
    norm_num
  have hRT : (K - Δ)⁻¹ * (K - Δ) = 1 := mul_eq_one_comm.mp hinv
  set R : Matrix (Idx D N) (Idx D N) ℂ := (K - Δ)⁻¹ with hRdef
  have hKΔM : (K - Δ) * M = 1 - Δ * M := by rw [Matrix.sub_mul, hKM]
  have e1 : R = M + R * Δ * M := by
    have e2 : R * (1 - Δ * M) = M := by
      rw [← hKΔM, ← Matrix.mul_assoc, hRT, Matrix.one_mul]
    have e3 : R - R * Δ * M = M := by
      have : R - R * Δ * M = R * (1 - Δ * M) := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      rw [this, e2]
    exact sub_eq_iff_eq_add.mp e3
  have e4 : R = M + M * Δ * M + M * Δ * (M * Δ * M) + R * Δ * M * Δ * M * Δ * M := by
    have e5 : R = M + M * Δ * M + R * Δ * M * Δ * M := by
      calc R = M + R * Δ * M := e1
        _ = M + (M + R * Δ * M) * Δ * M := congrArg (fun W => M + W * Δ * M) e1
        _ = _ := by simp only [Matrix.add_mul, Matrix.mul_assoc]; abel
    calc R = M + M * Δ * M + R * Δ * M * Δ * M := e5
      _ = M + M * Δ * M + (M + R * Δ * M) * Δ * M * Δ * M :=
          congrArg (fun W => M + M * Δ * M + W * Δ * M * Δ * M) e1
      _ = _ := by simp only [Matrix.add_mul, Matrix.mul_assoc]; abel
  refine ⟨?_, ?_, ?_⟩
  · change (lam D N A - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - ∑ b, (m + d b) • Ea D N b) *
      resX (lam D N A) z (fun a => m + d a) = 1
    rw [hT, hRx]
    exact hinv
  · rw [hRx]
    have : R - M = R * Δ * M := by
      conv_lhs => rw [e1]
      rw [add_sub_cancel_left]
    rw [this]
    have h2 := BootstrapDet_opNorm_mul_le (BootstrapDet_opNorm_mul_le hRn hΔn) hM
    refine h2.trans (le_of_eq ?_)
    ring
  · rw [hRx]
    have hW : opNorm (R * Δ * M * Δ * M * Δ * M) ≤ 5 * ‖x‖ ^ 3 := by
      have h2 := BootstrapDet_opNorm_mul_le (BootstrapDet_opNorm_mul_le (BootstrapDet_opNorm_mul_le (BootstrapDet_opNorm_mul_le
        (BootstrapDet_opNorm_mul_le (BootstrapDet_opNorm_mul_le hRn hΔn) hM) hΔn) hM) hΔn) hM
      refine h2.trans ?_
      have : 5 / 2 * ‖x‖ * (5 / 4) * ‖x‖ * (5 / 4) * ‖x‖ * (5 / 4) = 625 / 128 * ‖x‖ ^ 3 := by
        ring
      rw [this]
      nlinarith [pow_nonneg hx0 3]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
    have hcomp : blockTr D N R a - m - (∑ b,
        ((D : ℂ) * ntr (M * Ea D N a * M * Ea D N b)) * d b) - (∑ b, ∑ c,
        ((D : ℂ) * ntr (Ea D N a * M * Ea D N b * M * Ea D N c * M)) * d b * d c) =
        (D : ℂ) * ntr (Ea D N a * (R * Δ * M * Δ * M * Δ * M)) := by
      obtain ⟨t2, t4⟩ := BootstrapDet_terms D N M Δ d hΔdef a
      have t0 : (D : ℂ) * ntr (Ea D N a * M) = m := by
        rw [BootstrapDet_ntr_comm]
        exact hblk a
      simp only [blockTr]
      conv_lhs => rw [e4]
      rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, BootstrapDet_ntr_add, BootstrapDet_ntr_add, BootstrapDet_ntr_add,
        mul_add, mul_add, mul_add, t0, t2, t4]
      simp only [Matrix.mul_assoc]
      ring
    simp only [Pi.sub_apply]
    rw [hcomp]
    exact (BootstrapDet_blk_opNorm D N a _).trans hW

/-- The exact identity behind the self-improving steps: for Hermitian `H`, `Im z > 0` and
`x̃ = σ_θ g`, `g_a = D⟨E_a G⟩`, if `Λ - z - Σ_b x̃_b E_b` is inverted by `R_x̃`, then
`G = R_x̃ - R_x̃ H̲G`. -/
theorem res_eq_resX_sub (D N : ℕ) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (hR : (lam D N A - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) -
        ∑ b, (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) b • Ea D N b) *
        resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) = 1) :
    res (H + lam D N A) z =
      resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) -
        resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) *
          hgUnder D N θ H (lam D N A) z := by
  have hH' : (H + lam D N A).IsHermitian := hH.add (lam_isHermitian D N A)
  obtain ⟨h1, -⟩ := res_mul_sub (H + lam D N A) hH' z hz
  have hS := sTheta_blockTr D N θ (res (H + lam D N A) z)
  have hRT := mul_eq_one_comm.mp hR
  set Λ := lam D N A with hΛ
  set G := res (H + Λ) z with hG
  set S := ∑ b, (sigTheta D θ *ᵥ blockTr D N G) b • Ea D N b with hSdef
  set R := resX Λ z (sigTheta D θ *ᵥ blockTr D N G) with hRdef
  have e : (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - S) * G =
      (H + Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * G - (H * G + S * G) := by
    simp only [Matrix.sub_mul, Matrix.add_mul]
    abel
  have hU : hgUnder D N θ H Λ z = 1 - (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - S) * G := by
    rw [e, h1]
    unfold hgUnder
    rw [hS]
    abel
  rw [hU, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hRT, Matrix.one_mul]
  abel

/-- The shell inequality: for `|a| ≤ y` and `ρ ≥ y / 2`, `1 / ρ ≤ 4 y / (a² + y²)`. -/
private lemma BootstrapDet_L (y a ρ : ℝ) (hy : 0 < y) (ha : |a| ≤ y) (hρ : y / 2 ≤ ρ) :
    1 / ρ ≤ 4 * (y / (a ^ 2 + y ^ 2)) := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : a ^ 2 ≤ y ^ 2 := by
    have := sq_le_sq' (by linarith [abs_le.mp ha |>.1]) (abs_le.mp ha |>.2)
    exact this
  have h2 : 1 / ρ ≤ 2 / y := by
    have := one_div_le_one_div_of_le (by linarith : 0 < y / 2) hρ
    calc 1 / ρ ≤ 1 / (y / 2) := this
      _ = 2 / y := by field_simp
  refine h2.trans ?_
  have hpos : 0 < a ^ 2 + y ^ 2 := by positivity
  rw [div_le_iff₀ hy]
  have : 4 * (y / (a ^ 2 + y ^ 2)) * y = 4 * y ^ 2 / (a ^ 2 + y ^ 2) := by
    field_simp
  rw [this, le_div_iff₀ hpos]
  nlinarith

/-- The dyadic bound `1 / √(a² + η²) ≤ 1 + 4 Σ_{j=0}^{J} 2^j η / (a² + 4^j η²)` for `2^J η ≥ 1`: the core `|a| ≤ η` and the shells `2^{j-1} η < |a| ≤ 2^j η` are covered by one term each, and `|a| > 2^J η` by the constant `1`. -/
private lemma BootstrapDet_weight (η : ℝ) (hη : 0 < η) (J : ℕ) (hJ : 1 ≤ 2 ^ J * η) (a : ℝ) :
    1 / Real.sqrt (a ^ 2 + η ^ 2) ≤
      1 + 4 * ∑ j ∈ Finset.range (J + 1), ((2 ^ j * η) / (a ^ 2 + (2 ^ j * η) ^ 2)) := by
  have hρa : |a| ≤ Real.sqrt (a ^ 2 + η ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hρη : η ≤ Real.sqrt (a ^ 2 + η ^ 2) := by
    calc η = Real.sqrt (η ^ 2) := (Real.sqrt_sq hη.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  have hterm : ∀ j : ℕ, 0 ≤ (2 ^ j * η) / (a ^ 2 + (2 ^ j * η) ^ 2) := fun j => by positivity
  have hS : ∀ J : ℕ, |a| ≤ 2 ^ J * η → 1 / Real.sqrt (a ^ 2 + η ^ 2) ≤
      4 * ∑ j ∈ Finset.range (J + 1), ((2 ^ j * η) / (a ^ 2 + (2 ^ j * η) ^ 2)) := by
    intro J
    induction J with
    | zero =>
      intro h
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul] at h ⊢
      exact BootstrapDet_L η a _ hη h (by linarith)
    | succ J ih =>
      intro h
      rw [Finset.sum_range_succ]
      have hsum : 0 ≤ ∑ j ∈ Finset.range (J + 1), ((2 ^ j * η) / (a ^ 2 + (2 ^ j * η) ^ 2)) :=
        Finset.sum_nonneg fun j _ => hterm j
      by_cases hc : |a| ≤ 2 ^ J * η
      · have := ih hc
        linarith [hterm (J + 1)]
      · rw [not_le] at hc
        have hy : (0 : ℝ) < 2 ^ (J + 1) * η := by positivity
        have e : (2 : ℝ) ^ (J + 1) * η / 2 = 2 ^ J * η := by ring
        have h2 := BootstrapDet_L (2 ^ (J + 1) * η) a (Real.sqrt (a ^ 2 + η ^ 2)) hy h (by
          rw [e]
          linarith)
        linarith
  by_cases hc : |a| ≤ 2 ^ J * η
  · have := hS J hc
    have hsum : 0 ≤ ∑ j ∈ Finset.range (J + 1), ((2 ^ j * η) / (a ^ 2 + (2 ^ j * η) ^ 2)) :=
      Finset.sum_nonneg fun j _ => hterm j
    linarith
  · rw [not_le] at hc
    have hsum : 0 ≤ ∑ j ∈ Finset.range (J + 1), ((2 ^ j * η) / (a ^ 2 + (2 ^ j * η) ^ 2)) :=
      Finset.sum_nonneg fun j _ => hterm j
    have h1 : 1 / Real.sqrt (a ^ 2 + η ^ 2) ≤ 1 := by
      rw [div_le_one (lt_of_lt_of_le hη hρη)]
      linarith
    linarith

/-- The spectral form `G(z) = U diag((λ_k - z)⁻¹) U^*` of the resolvent (2.12) [def_resolv]. -/
private lemma BootstrapDet_res_decomp {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    res X z = (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun k => ((hX.eigenvalues k : ℂ) - z)⁻¹) *
        (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  ext i j
  rw [res_eq_sum_eig X hX z hz, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def]
  rw [div_eq_mul_inv]
  ring

/-- `s^* G(z) t = Σ_k conj((U^* s)_k) (λ_k - z)⁻¹ (U^* t)_k`. -/
private lemma BootstrapDet_form {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s t : ι → ℂ) :
    star s ⬝ᵥ (res X z *ᵥ t) = ∑ k, star (((hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ s) k) *
      (((hX.eigenvalues k : ℂ) - z)⁻¹ * ((hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ t) k) := by
  rw [BootstrapDet_res_decomp X hX z hz, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  have : star s ᵥ* (hX.eigenvectorUnitary : Matrix ι ι ℂ) =
      star ((hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ s) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [this]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_diagonal]
  rfl

/-- The eigenvector unitary preserves the Euclidean norm: `Σ_k |(U^* s)_k|² = Σ_i |s_i|²`. -/
private lemma BootstrapDet_unit_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (s : ι → ℂ) :
    ∑ k, ‖((hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ s) k‖ ^ 2 = ∑ i, ‖s i‖ ^ 2 := by
  set U : Matrix ι ι ℂ := (hX.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : U * Uᴴ = 1 := by
    have := Unitary.coe_mul_star_self hX.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  have key : ∀ v : ι → ℂ, star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  have h1 : star (Uᴴ *ᵥ s) ⬝ᵥ (Uᴴ *ᵥ s) = star s ⬝ᵥ s := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  rw [key, key] at h1
  exact_mod_cast h1

/-- `Im s^* G(E + iy) s = Σ_k |(U^* s)_k|² y / ((λ_k - E)² + y²)`. -/
private lemma BootstrapDet_im_form {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (E y : ℝ) (hy : 0 < y) (s : ι → ℂ) :
    (star s ⬝ᵥ (res X ((E : ℂ) + (y : ℂ) * Complex.I) *ᵥ s)).im =
      ∑ k, ‖((hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ s) k‖ ^ 2 *
        (y / ((hX.eigenvalues k - E) ^ 2 + y ^ 2)) := by
  have hz : 0 < ((E : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [BootstrapDet_form X hX _ hz, Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set a := ((hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ s) k with ha
  have e : star a * ((((hX.eigenvalues k : ℂ) - ((E : ℂ) + (y : ℂ) * Complex.I)))⁻¹ * a) =
      (((hX.eigenvalues k : ℂ) - ((E : ℂ) + (y : ℂ) * Complex.I)))⁻¹ * ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_left_comm, Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  rw [e, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.inv_im]
  have h2 : (((hX.eigenvalues k : ℂ) - ((E : ℂ) + (y : ℂ) * Complex.I))).im = -y := by simp
  have h3 : Complex.normSq (((hX.eigenvalues k : ℂ) - ((E : ℂ) + (y : ℂ) * Complex.I))) =
      (hX.eigenvalues k - E) ^ 2 + y ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  rw [h2, h3]
  ring

/-- `|l - (E + iy)| = √((l - E)² + y²)` for real `l`, `E`, `y`. -/
private lemma BootstrapDet_norm_sub (l E y : ℝ) :
    ‖(l : ℂ) - ((E : ℂ) + (y : ℂ) * Complex.I)‖ = Real.sqrt ((l - E) ^ 2 + y ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

/-- The transfer of resolvent bounds to a lower spectral parameter (deterministic): for Hermitian
`X`, unit `s, t`, `0 < η' ≤ η` and `2^J η ≥ 1`,
`|s^* G(E + iη') t| ≤ (η/η') (A_s A_t)^{1/2}` with
`A_s = 1 + 4 Σ_{j=0}^{J} Im s^* G(E + i 2^j η) s`. -/
theorem res_transfer {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (s t : ι → ℂ) (hs : ∑ i, ‖s i‖ ^ 2 = 1) (ht : ∑ i, ‖t i‖ ^ 2 = 1)
    (E η η' : ℝ) (hη' : 0 < η') (hηη : η' ≤ η) (J : ℕ) (hJ : 1 ≤ 2 ^ J * η) :
    ‖star s ⬝ᵥ (res X ((E : ℂ) + (η' : ℂ) * Complex.I) *ᵥ t)‖ ≤
      η / η' * Real.sqrt
        ((1 + 4 * ∑ j ∈ Finset.range (J + 1),
            (star s ⬝ᵥ (res X ((E : ℂ) + ((2 ^ j * η : ℝ) : ℂ) * Complex.I) *ᵥ s)).im) *
          (1 + 4 * ∑ j ∈ Finset.range (J + 1),
            (star t ⬝ᵥ (res X ((E : ℂ) + ((2 ^ j * η : ℝ) : ℂ) * Complex.I) *ᵥ t)).im)) := by
  have hη0 : 0 < η := lt_of_lt_of_le hη' hηη
  set U : Matrix ι ι ℂ := (hX.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set ev : ι → ℝ := hX.eigenvalues with hev
  have hρpos : ∀ k, 0 < Real.sqrt ((ev k - E) ^ 2 + η ^ 2) := fun k =>
    Real.sqrt_pos.mpr (by positivity)
  set w : ι → ℝ := fun k => 1 / Real.sqrt ((ev k - E) ^ 2 + η ^ 2) with hw
  have hw0 : ∀ k, 0 < w k := fun k => one_div_pos.mpr (hρpos k)
  have hy : ∀ j : ℕ, 0 < 2 ^ j * η := fun j => by positivity
  -- the bound `Σ_k |u_k|² w_k ≤ A_u`
  have hA : ∀ u : ι → ℂ, ∑ i, ‖u i‖ ^ 2 = 1 →
      ∑ k, ‖(Uᴴ *ᵥ u) k‖ ^ 2 * w k ≤ 1 + 4 * ∑ j ∈ Finset.range (J + 1),
        (star u ⬝ᵥ (res X ((E : ℂ) + ((2 ^ j * η : ℝ) : ℂ) * Complex.I) *ᵥ u)).im := by
    intro u hu
    have hun := (BootstrapDet_unit_norm X hX u).trans hu
    have him : ∀ j ∈ Finset.range (J + 1),
        (star u ⬝ᵥ (res X ((E : ℂ) + ((2 ^ j * η : ℝ) : ℂ) * Complex.I) *ᵥ u)).im =
        ∑ k, ‖(Uᴴ *ᵥ u) k‖ ^ 2 * ((2 ^ j * η) / ((ev k - E) ^ 2 + (2 ^ j * η) ^ 2)) :=
      fun j _ => BootstrapDet_im_form X hX E (2 ^ j * η) (hy j) u
    rw [Finset.sum_congr rfl him]
    calc ∑ k, ‖(Uᴴ *ᵥ u) k‖ ^ 2 * w k
        ≤ ∑ k, ‖(Uᴴ *ᵥ u) k‖ ^ 2 * (1 + 4 * ∑ j ∈ Finset.range (J + 1),
            ((2 ^ j * η) / ((ev k - E) ^ 2 + (2 ^ j * η) ^ 2))) :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (BootstrapDet_weight η hη0 J hJ (ev k - E)) (sq_nonneg _)
      _ = (∑ k, ‖(Uᴴ *ᵥ u) k‖ ^ 2) + 4 * (∑ j ∈ Finset.range (J + 1),
            ∑ k, ‖(Uᴴ *ᵥ u) k‖ ^ 2 * ((2 ^ j * η) / ((ev k - E) ^ 2 + (2 ^ j * η) ^ 2))) := by
          have : ∀ k, ‖(Uᴴ *ᵥ u) k‖ ^ 2 * (1 + 4 * ∑ j ∈ Finset.range (J + 1),
              ((2 ^ j * η) / ((ev k - E) ^ 2 + (2 ^ j * η) ^ 2))) =
              ‖(Uᴴ *ᵥ u) k‖ ^ 2 + 4 * ∑ j ∈ Finset.range (J + 1),
              ‖(Uᴴ *ᵥ u) k‖ ^ 2 * ((2 ^ j * η) / ((ev k - E) ^ 2 + (2 ^ j * η) ^ 2)) := by
            intro k
            rw [mul_add, mul_one, mul_left_comm, Finset.mul_sum]
          simp only [this, Finset.sum_add_distrib]
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ = 1 + 4 * ∑ j ∈ Finset.range (J + 1),
            ∑ k, ‖(Uᴴ *ᵥ u) k‖ ^ 2 * ((2 ^ j * η) / ((ev k - E) ^ 2 + (2 ^ j * η) ^ 2)) := by
          rw [hun]
  have hAs := hA s hs
  have hAt := hA t ht
  set As := 1 + 4 * ∑ j ∈ Finset.range (J + 1),
        (star s ⬝ᵥ (res X ((E : ℂ) + ((2 ^ j * η : ℝ) : ℂ) * Complex.I) *ᵥ s)).im with hAsdef
  set At := 1 + 4 * ∑ j ∈ Finset.range (J + 1),
        (star t ⬝ᵥ (res X ((E : ℂ) + ((2 ^ j * η : ℝ) : ℂ) * Complex.I) *ᵥ t)).im with hAtdef
  -- Cauchy–Schwarz
  have hCS : ∑ k, ‖(Uᴴ *ᵥ s) k‖ * ‖(Uᴴ *ᵥ t) k‖ * w k ≤ Real.sqrt (As * At) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k => ‖(Uᴴ *ᵥ s) k‖ * Real.sqrt (w k)) (fun k => ‖(Uᴴ *ᵥ t) k‖ * Real.sqrt (w k))
    have e1 : ∀ k, (‖(Uᴴ *ᵥ s) k‖ * Real.sqrt (w k)) * (‖(Uᴴ *ᵥ t) k‖ * Real.sqrt (w k)) =
        ‖(Uᴴ *ᵥ s) k‖ * ‖(Uᴴ *ᵥ t) k‖ * w k := fun k => by
      calc _ = ‖(Uᴴ *ᵥ s) k‖ * ‖(Uᴴ *ᵥ t) k‖ * (Real.sqrt (w k) * Real.sqrt (w k)) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (hw0 k).le]
    have e2 : ∀ (u : ι → ℂ) k, (‖(Uᴴ *ᵥ u) k‖ * Real.sqrt (w k)) ^ 2 =
        ‖(Uᴴ *ᵥ u) k‖ ^ 2 * w k := fun u k => by
      rw [mul_pow, Real.sq_sqrt (hw0 k).le]
    simp only [e1, e2] at hcs
    have hsum0 : 0 ≤ ∑ k, ‖(Uᴴ *ᵥ s) k‖ * ‖(Uᴴ *ᵥ t) k‖ * w k :=
      Finset.sum_nonneg fun k _ => by have := hw0 k; positivity
    refine Real.le_sqrt_of_sq_le ?_
    refine hcs.trans ?_
    have h1 : 0 ≤ ∑ k, ‖(Uᴴ *ᵥ s) k‖ ^ 2 * w k :=
      Finset.sum_nonneg fun k _ => by have := hw0 k; positivity
    have h2 : 0 ≤ ∑ k, ‖(Uᴴ *ᵥ t) k‖ ^ 2 * w k :=
      Finset.sum_nonneg fun k _ => by have := hw0 k; positivity
    exact mul_le_mul hAs hAt h2 (h1.trans hAs)
  -- the transfer step
  set r : ℝ := η / η' with hr
  have hr0 : r * η' = η := div_mul_cancel₀ _ hη'.ne'
  have hr1 : 1 ≤ r := (one_le_div hη').mpr hηη
  have hstep1 : ∀ a : ℝ, Real.sqrt (a ^ 2 + η ^ 2) ≤ r * Real.sqrt (a ^ 2 + η' ^ 2) := by
    intro a
    have h2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith
    have h1 : a ^ 2 + η ^ 2 ≤ r ^ 2 * (a ^ 2 + η' ^ 2) := by
      have : r ^ 2 * η' ^ 2 = η ^ 2 := by rw [← mul_pow, hr0]
      nlinarith [sq_nonneg a]
    calc Real.sqrt (a ^ 2 + η ^ 2) ≤ Real.sqrt (r ^ 2 * (a ^ 2 + η' ^ 2)) := Real.sqrt_le_sqrt h1
      _ = r * Real.sqrt (a ^ 2 + η' ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  have hz' : 0 < ((E : ℂ) + (η' : ℂ) * Complex.I).im := by simpa using hη'
  rw [BootstrapDet_form X hX _ hz' s t]
  calc ‖∑ k, star ((Uᴴ *ᵥ s) k) *
        ((((ev k : ℂ) - ((E : ℂ) + (η' : ℂ) * Complex.I)))⁻¹ * (Uᴴ *ᵥ t) k)‖
      ≤ ∑ k, ‖star ((Uᴴ *ᵥ s) k) *
        ((((ev k : ℂ) - ((E : ℂ) + (η' : ℂ) * Complex.I)))⁻¹ * (Uᴴ *ᵥ t) k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, r * (‖(Uᴴ *ᵥ s) k‖ * ‖(Uᴴ *ᵥ t) k‖ * w k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul, norm_star, norm_inv, BootstrapDet_norm_sub]
        have hρ' : 0 < Real.sqrt ((ev k - E) ^ 2 + η' ^ 2) :=
          Real.sqrt_pos.mpr (by positivity)
        have h1 : (Real.sqrt ((ev k - E) ^ 2 + η' ^ 2))⁻¹ ≤ r * w k := by
          rw [hw, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hρ' (hρpos k), one_mul]
          exact hstep1 _
        calc ‖(Uᴴ *ᵥ s) k‖ * ((Real.sqrt ((ev k - E) ^ 2 + η' ^ 2))⁻¹ * ‖(Uᴴ *ᵥ t) k‖)
            = ‖(Uᴴ *ᵥ s) k‖ * ‖(Uᴴ *ᵥ t) k‖ * (Real.sqrt ((ev k - E) ^ 2 + η' ^ 2))⁻¹ := by
              ring
          _ ≤ ‖(Uᴴ *ᵥ s) k‖ * ‖(Uᴴ *ᵥ t) k‖ * (r * w k) := by gcongr
          _ = r * (‖(Uᴴ *ᵥ s) k‖ * ‖(Uᴴ *ᵥ t) k‖ * w k) := by ring
    _ = r * ∑ k, ‖(Uᴴ *ᵥ s) k‖ * ‖(Uᴴ *ᵥ t) k‖ * w k := by rw [Finset.mul_sum]
    _ ≤ r * Real.sqrt (As * At) := by gcongr

/-- `|⟨X⟩| ≤ ‖X‖` on a nonempty index type. -/
private lemma BootstrapDet_norm_ntr_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Matrix ι ι ℂ) : ‖ntr X‖ ≤ opNorm X := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr Matrix.trace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, X.diag i‖
      ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, opNorm X := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_apply_le_opNorm X i i)
    _ = opNorm X := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-- `⟨M M^*⟩ = n⁻¹ ‖M‖_HS²`. -/
private lemma BootstrapDet_ntr_mul_conjTranspose {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) :
    ntr (M * Mᴴ) = (((Fintype.card ι : ℝ)⁻¹ * ∑ j, ∑ k, ‖M j k‖ ^ 2 : ℝ) : ℂ) := by
  unfold ntr Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- `|⟨M²⟩| ≤ n⁻¹ ‖M‖_HS² = ⟨M M^*⟩`, by `|M_ij M_ji| ≤ (|M_ij|² + |M_ji|²) / 2`. -/
private lemma BootstrapDet_ntr_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (M : Matrix ι ι ℂ) :
    ‖ntr (M ^ 2)‖ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ j, ∑ k, ‖M j k‖ ^ 2 := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [sq, Matrix.trace, norm_mul, norm_inv, Complex.norm_natCast]
  gcongr
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  calc ‖∑ i, ∑ j, M i j * M j i‖ ≤ ∑ i, ∑ j, ‖M i j‖ * ‖M j i‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (by simp))
    _ ≤ ∑ i, ∑ j, (‖M i j‖ ^ 2 + ‖M j i‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          nlinarith [sq_nonneg (‖M i j‖ - ‖M j i‖)]
    _ = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
        simp only [add_div, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j => ‖M j i‖ ^ 2 / 2)]
        simp only [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `|m'(z)| ≤ Im m / Im z` for the derivative `m' = ⟨M²⟩ / (1 - ⟨M²⟩)` of (A.43) [derivative_m_t_z_with_t_and_z]: `⟨M M^*⟩ = Im m / (Im m + η)` by (A.3) [equation_z_im_m] gives `|⟨M²⟩| ≤ Im m / (Im m + η)`. -/
private lemma BootstrapDet_mprime_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    ‖ntr (MSol Λ z ^ 2) / (1 - ntr (MSol Λ z ^ 2))‖ ≤ (mSol Λ z).im / z.im := by
  obtain ⟨hA3a, -⟩ := equation_z_im_m Λ hΛ z hz
  obtain ⟨hmim, -, -⟩ := mSol_spec Λ hΛ z hz
  have hn := BootstrapDet_ntr_mul_conjTranspose (MSol Λ z)
  rw [hA3a] at hn
  have hr : (mSol Λ z).im / ((mSol Λ z).im + z.im) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ j, ∑ k, ‖MSol Λ z j k‖ ^ 2 := by exact_mod_cast hn
  have h1 := BootstrapDet_ntr_sq_le (MSol Λ z)
  rw [← hr] at h1
  set ν := (mSol Λ z).im with hν
  set η := z.im with hη
  set t := ntr (MSol Λ z ^ 2) with ht
  have hden : 0 < ν + η := by linarith
  have hc1 : ν / (ν + η) < 1 := by rw [div_lt_one hden]; linarith
  have h2 : 1 - ν / (ν + η) ≤ ‖1 - t‖ := by
    have := norm_sub_norm_le (1 : ℂ) t
    rw [norm_one] at this
    linarith
  have h3 : 0 < 1 - ν / (ν + η) := by linarith
  rw [norm_div]
  calc ‖t‖ / ‖1 - t‖ ≤ (ν / (ν + η)) / (1 - ν / (ν + η)) :=
        div_le_div₀ (by positivity) h1 h3 h2
    _ = ν / η := by
        have hη0 : η ≠ 0 := hz.ne'
        have hden0 : ν + η ≠ 0 := hden.ne'
        have e : 1 - ν / (ν + η) = η / (ν + η) := by
          field_simp
          ring
        rw [e]
        field_simp

/-- `Im m ≤ 1` for every Hermitian `Λ` and `Im z > 0`: `Im m ≤ |m| ≤ ‖M‖ ≤ (η + Im m)⁻¹`. -/
private lemma BootstrapDet_im_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    (mSol Λ z).im ≤ 1 := by
  obtain ⟨hmim, hmtr, -⟩ := mSol_spec Λ hΛ z hz
  have hzm : 0 < (z + mSol Λ z).im := by rw [Complex.add_im]; linarith
  have h1 : opNorm (MSol Λ z) ≤ (z + mSol Λ z).im⁻¹ := opNorm_res_le Λ hΛ _ hzm
  have h2 : ‖mSol Λ z‖ ≤ opNorm (MSol Λ z) := by
    rw [hmtr]
    exact BootstrapDet_norm_ntr_le _
  have h3 : (mSol Λ z).im ≤ ‖mSol Λ z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
  have h4 : (mSol Λ z).im ≤ ((z + mSol Λ z).im)⁻¹ := h3.trans (h2.trans h1)
  rw [Complex.add_im] at h4
  have h5 : (mSol Λ z).im * (z.im + (mSol Λ z).im) ≤ 1 := by
    have hpos : 0 < z.im + (mSol Λ z).im := by linarith
    calc (mSol Λ z).im * (z.im + (mSol Λ z).im)
        ≤ (z.im + (mSol Λ z).im)⁻¹ * (z.im + (mSol Λ z).im) :=
          mul_le_mul_of_nonneg_right h4 hpos.le
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  nlinarith

/-- The operator norm of the identity is `1` on a nonempty index type. -/
private lemma BootstrapDet_opNorm_one {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    opNorm (1 : Matrix ι ι ℂ) = 1 := by
  unfold opNorm
  rw [map_one, norm_one]

/-- `‖M(z)‖ ≤ 5/4` for `‖Λ‖ ≤ 1/10` and `Im z > 0`, from the a priori bound behind (A.19) [taylor_expansion_M]. -/
private lemma BootstrapDet_opNorm_M54 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) :
    opNorm (MSol Λ z) ≤ 5 / 4 := by
  obtain ⟨-, -, hMn⟩ := mSol_apriori Λ hΛ hℓ z hz
  have hℓ0 : 0 ≤ opNorm Λ := norm_nonneg _
  have h1 : (1 - 2 * opNorm Λ)⁻¹ ≤ (4 / 5 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) (by linarith)
  norm_num at h1
  linarith

/-- `|m(z) - m(z')| ≤ η₀⁻¹ |z - z'|` on the convex set `{Im ≥ η₀}`, from `|m'| ≤ Im m / Im z ≤ η₀⁻¹`. -/
private lemma BootstrapDet_mSol_lip {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (η₀ : ℝ) (hη₀ : 0 < η₀) (z z' : ℂ)
    (hz : η₀ ≤ z.im) (hz' : η₀ ≤ z'.im) :
    ‖mSol Λ z - mSol Λ z'‖ ≤ η₀⁻¹ * ‖z - z'‖ := by
  refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := mSol Λ) (f' := fun w => ntr (MSol Λ w ^ 2) / (1 - ntr (MSol Λ w ^ 2)))
    (s := {w : ℂ | η₀ ≤ w.im}) (C := η₀⁻¹) ?_ ?_ (convex_halfSpace_im_ge η₀) hz' hz
  · intro w hw
    exact (derivative_m_t_z Λ hΛ w (lt_of_lt_of_le hη₀ hw) 0).1.hasDerivWithinAt
  · intro w hw
    have hw0 : 0 < w.im := lt_of_lt_of_le hη₀ hw
    refine (BootstrapDet_mprime_bound Λ hΛ w hw0).trans ?_
    have h1 := BootstrapDet_im_le_one Λ hΛ w hw0
    have h2 := (mSol_spec Λ hΛ w hw0).1
    rw [inv_eq_one_div, div_le_div_iff₀ hw0 hη₀]
    have : (mSol Λ w).im * η₀ ≤ 1 * η₀ := mul_le_mul_of_nonneg_right h1 hη₀.le
    have hw' : η₀ ≤ w.im := hw
    linarith

/-- Lipschitz bounds for (2.16) [self_m] and (2.17) [def_G0] on `{Im z ≥ η₀}`: for Hermitian `Λ`
with `‖Λ‖ ≤ 1/10`, `|m(z) - m(z')| ≤ η₀⁻¹ |z - z'|` and
`‖M(z) - M(z')‖ ≤ (25/16)(1 + η₀⁻¹) |z - z'|`. -/
theorem MSol_lipschitz {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (η₀ : ℝ) (hη₀ : 0 < η₀) (z z' : ℂ)
    (hz : η₀ ≤ z.im) (hz' : η₀ ≤ z'.im) :
    ‖mSol Λ z - mSol Λ z'‖ ≤ η₀⁻¹ * ‖z - z'‖ ∧
      opNorm (MSol Λ z - MSol Λ z') ≤ 25 / 16 * (1 + η₀⁻¹) * ‖z - z'‖ := by
  have hz0 : 0 < z.im := lt_of_lt_of_le hη₀ hz
  have hz0' : 0 < z'.im := lt_of_lt_of_le hη₀ hz'
  have hm := BootstrapDet_mSol_lip Λ hΛ η₀ hη₀ z z' hz hz'
  refine ⟨hm, ?_⟩
  obtain ⟨-, -, hs⟩ := mSol_spec Λ hΛ z hz0
  obtain ⟨-, -, hs'⟩ := mSol_spec Λ hΛ z' hz0'
  have hMK := mul_eq_one_comm.mp hs
  have hM1 := BootstrapDet_opNorm_M54 Λ hΛ hℓ z hz0
  have hM2 := BootstrapDet_opNorm_M54 Λ hΛ hℓ z' hz0'
  set c : ℂ := (z + mSol Λ z) - (z' + mSol Λ z') with hc
  have e : MSol Λ z - MSol Λ z' = MSol Λ z * (c • (1 : Matrix ι ι ℂ)) * MSol Λ z' := by
    have h1 : c • (1 : Matrix ι ι ℂ) = (Λ - (z' + mSol Λ z') • (1 : Matrix ι ι ℂ)) -
        (Λ - (z + mSol Λ z) • (1 : Matrix ι ι ℂ)) := by
      rw [hc, sub_smul]
      abel
    rw [h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc _ (Λ - (z' + mSol Λ z') • (1 : Matrix ι ι ℂ)),
      hs', Matrix.mul_one, hMK, Matrix.one_mul]
  have hcn : ‖c‖ ≤ (1 + η₀⁻¹) * ‖z - z'‖ := by
    have : c = (z - z') + (mSol Λ z - mSol Λ z') := by rw [hc]; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    linarith
  rw [e]
  have h1 : opNorm (c • (1 : Matrix ι ι ℂ)) ≤ (1 + η₀⁻¹) * ‖z - z'‖ := by
    rw [opNorm_smul, BootstrapDet_opNorm_one, mul_one]
    exact hcn
  have h2 := BootstrapDet_opNorm_mul_le (BootstrapDet_opNorm_mul_le hM1 h1) hM2
  refine h2.trans (le_of_eq ?_)
  ring

/-- The real inequality behind the derivative bound of the control parameter: with `u = ν / (N η)`, `|ν'| ≤ (ν / η) |d|`, `|η'| ≤ |d|`, `ν ≤ 1` and `η ≥ 1/N`, the derivative of `√u + (N η)⁻¹` is at most `2 N |d|` in modulus. -/
private lemma BootstrapDet_psi_bound (N ν η ν' η' dd : ℝ) (hN : 1 ≤ N) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hη : 1 / N ≤ η) (hν' : |ν'| ≤ ν / η * dd) (hη' : |η'| ≤ dd) (hdd : 0 ≤ dd) :
    |(ν' * (N * η) - ν * (N * η')) / (N * η) ^ 2 / (2 * Real.sqrt (ν / (N * η))) +
        -(N * η') / (N * η) ^ 2| ≤ 2 * N * dd := by
  have hN0 : 0 < N := by linarith
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  set P := N * η with hP
  have hP1 : 1 ≤ P := by
    have : 1 ≤ N * η := by
      calc (1 : ℝ) = N * (1 / N) := by field_simp
        _ ≤ N * η := by gcongr
    exact this
  have hP0 : 0 < P := by linarith
  set s := Real.sqrt (ν / P) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (div_pos hν hP0)
  have hs2 : s ^ 2 = ν / P := Real.sq_sqrt (div_pos hν hP0).le
  have hs1 : s ≤ 1 := by
    have : ν / P ≤ 1 := by rw [div_le_one hP0]; linarith
    calc s ≤ Real.sqrt 1 := Real.sqrt_le_sqrt this
      _ = 1 := Real.sqrt_one
  have hνs : ν = s ^ 2 * P := by rw [hs2]; field_simp
  have hnum : |ν' * P - ν * (N * η')| ≤ 2 * ν * N * dd := by
    have h1 : |ν' * P| ≤ ν * N * dd := by
      rw [abs_mul, abs_of_pos hP0]
      calc |ν'| * P ≤ ν / η * dd * P := by gcongr
        _ = ν * N * dd := by rw [hP]; field_simp
    have h2 : |ν * (N * η')| ≤ ν * N * dd := by
      rw [abs_mul, abs_mul, abs_of_pos hν, abs_of_pos hN0]
      calc ν * (N * |η'|) ≤ ν * (N * dd) := by gcongr
        _ = ν * N * dd := by ring
    calc |ν' * P - ν * (N * η')| ≤ |ν' * P| + |ν * (N * η')| := abs_sub _ _
      _ ≤ _ := by linarith
  have hT1 : |(ν' * P - ν * (N * η')) / P ^ 2 / (2 * s)| ≤ N * dd := by
    rw [abs_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < P ^ 2),
      abs_of_pos (by positivity : (0 : ℝ) < 2 * s), div_div, div_le_iff₀ (by positivity)]
    have : ν ≤ s * P ^ 2 := by
      rw [hνs]
      have h3 : s ≤ P := hs1.trans hP1
      nlinarith [mul_pos hs0 hP0]
    calc |ν' * P - ν * (N * η')| ≤ 2 * ν * N * dd := hnum
      _ ≤ 2 * (s * P ^ 2) * N * dd := by gcongr
      _ = N * dd * (P ^ 2 * (2 * s)) := by ring
  have hT2 : |-(N * η') / P ^ 2| ≤ N * dd := by
    rw [abs_div, abs_neg, abs_mul, abs_of_pos hN0, abs_of_pos (by positivity : (0 : ℝ) < P ^ 2),
      div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ P ^ 2 := by nlinarith
    calc N * |η'| ≤ N * dd := by gcongr
      _ = N * dd * 1 := by ring
      _ ≤ N * dd * P ^ 2 := by gcongr
  calc _ ≤ |(ν' * P - ν * (N * η')) / P ^ 2 / (2 * s)| + |-(N * η') / P ^ 2| := abs_add_le _ _
    _ ≤ N * dd + N * dd := add_le_add hT1 hT2
    _ = 2 * N * dd := by ring

/-- On `Im z > 0` the control parameter (2.22) [eq:aniso_local] is `√(Im m / (N η)) + (N η)⁻¹`. -/
private lemma BootstrapDet_psi_eq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (N : ℕ) (z : ℂ) (hz : 0 < z.im) :
    psiIso Λ N z = Real.sqrt ((mSol Λ z).im / ((N : ℝ) * z.im)) + ((N : ℝ) * z.im)⁻¹ := by
  have e1 : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  have hm := (mSol_spec Λ hΛ z hz).1
  unfold psiIso
  rw [e1, abs_of_pos hm, abs_of_pos hz, one_div]

/-- Along the segment from `z'` to `z` in `{Im ≥ N⁻¹}` the control parameter of (2.22) [eq:aniso_local] has a derivative of modulus at most `2 N |z - z'|`. -/
private lemma BootstrapDet_psi_deriv {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (N : ℕ) (hN : 1 ≤ N) (z z' : ℂ)
    (hz : ((N : ℝ))⁻¹ ≤ z.im) (hz' : ((N : ℝ))⁻¹ ≤ z'.im) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ g' : ℝ, HasDerivAt (fun r : ℝ =>
      Real.sqrt ((mSol Λ (z' + (r : ℂ) * (z - z'))).im /
        ((N : ℝ) * (z' + (r : ℂ) * (z - z')).im)) +
        ((N : ℝ) * (z' + (r : ℂ) * (z - z')).im)⁻¹) g' t ∧ |g'| ≤ 2 * N * ‖z - z'‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set d := z - z' with hd
  obtain ⟨ht0, ht1⟩ := ht
  have hwim : ((N : ℝ))⁻¹ ≤ (z' + (t : ℂ) * d).im := by
    have : (z' + (t : ℂ) * d).im = (1 - t) * z'.im + t * z.im := by
      simp [hd, Complex.mul_im]
      ring
    rw [this]
    nlinarith
  have hη0 : 0 < (z' + (t : ℂ) * d).im := lt_of_lt_of_le (by positivity) hwim
  have hw : HasDerivAt (fun r : ℝ => z' + (r : ℂ) * d) d t := by
    have := ((hasDerivAt_id t).ofReal_comp.mul_const d).const_add z'
    simpa using this
  have hm : HasDerivAt (fun r : ℝ => mSol Λ (z' + (r : ℂ) * d))
      (d * (ntr (MSol Λ (z' + (t : ℂ) * d) ^ 2) /
        (1 - ntr (MSol Λ (z' + (t : ℂ) * d) ^ 2)))) t := by
    have := (derivative_m_t_z Λ hΛ (z' + (t : ℂ) * d) hη0 0).1.scomp t hw
    rw [smul_eq_mul] at this
    exact this
  have hν : HasDerivAt (fun r : ℝ => (mSol Λ (z' + (r : ℂ) * d)).im)
      (d * (ntr (MSol Λ (z' + (t : ℂ) * d) ^ 2) /
        (1 - ntr (MSol Λ (z' + (t : ℂ) * d) ^ 2)))).im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hm
  have hη : HasDerivAt (fun r : ℝ => (z' + (r : ℂ) * d).im) d.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hw
  have hνpos := (mSol_spec Λ hΛ _ hη0).1
  have hP : (N : ℝ) * (z' + (t : ℂ) * d).im ≠ 0 := by positivity
  have hu : HasDerivAt (fun r : ℝ => (mSol Λ (z' + (r : ℂ) * d)).im /
      ((N : ℝ) * (z' + (r : ℂ) * d).im))
      (((d * (ntr (MSol Λ (z' + (t : ℂ) * d) ^ 2) /
        (1 - ntr (MSol Λ (z' + (t : ℂ) * d) ^ 2)))).im * ((N : ℝ) * (z' + (t : ℂ) * d).im) -
        (mSol Λ (z' + (t : ℂ) * d)).im * ((N : ℝ) * d.im)) /
        ((N : ℝ) * (z' + (t : ℂ) * d).im) ^ 2) t :=
    hν.div (hη.const_mul (N : ℝ)) hP
  have hupos : (mSol Λ (z' + (t : ℂ) * d)).im / ((N : ℝ) * (z' + (t : ℂ) * d).im) ≠ 0 :=
    (div_pos hνpos (by positivity)).ne'
  have hs := hu.sqrt hupos
  have hv : HasDerivAt (fun r : ℝ => ((N : ℝ) * (z' + (r : ℂ) * d).im)⁻¹)
      (-((N : ℝ) * d.im) / ((N : ℝ) * (z' + (t : ℂ) * d).im) ^ 2) t :=
    (hη.const_mul (N : ℝ)).inv hP
  refine ⟨_, hs.add hv, ?_⟩
  have hbd := BootstrapDet_mprime_bound Λ hΛ _ hη0
  have h1 := BootstrapDet_im_le_one Λ hΛ _ hη0
  refine BootstrapDet_psi_bound (N : ℝ) _ _ _ _ ‖d‖ hN1 hνpos h1 (by rwa [one_div]) ?_ ?_ (norm_nonneg _)
  · refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul]
    calc ‖d‖ * ‖ntr (MSol Λ (z' + (t : ℂ) * d) ^ 2) /
          (1 - ntr (MSol Λ (z' + (t : ℂ) * d) ^ 2))‖ ≤ ‖d‖ * ((mSol Λ (z' + (t : ℂ) * d)).im /
          (z' + (t : ℂ) * d).im) := by gcongr
      _ = _ := by ring
  · exact (Complex.abs_im_le_norm _)

/-- The control parameter of (2.22) [eq:aniso_local] is `2N`-Lipschitz on `{Im z ≥ N⁻¹}`, for every
Hermitian `Λ`. -/
theorem psiIso_lipschitz {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (N : ℕ) (hN : 1 ≤ N) (z z' : ℂ) (hz : ((N : ℝ))⁻¹ ≤ z.im)
    (hz' : ((N : ℝ))⁻¹ ≤ z'.im) :
    |psiIso Λ N z - psiIso Λ N z'| ≤ 2 * N * ‖z - z'‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hz0 : 0 < z.im := lt_of_lt_of_le (by positivity) hz
  have hz0' : 0 < z'.im := lt_of_lt_of_le (by positivity) hz'
  rw [BootstrapDet_psi_eq Λ hΛ N z hz0, BootstrapDet_psi_eq Λ hΛ N z' hz0']
  have key := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun r : ℝ => Real.sqrt ((mSol Λ (z' + (r : ℂ) * (z - z'))).im /
        ((N : ℝ) * (z' + (r : ℂ) * (z - z')).im)) +
        ((N : ℝ) * (z' + (r : ℂ) * (z - z')).im)⁻¹)
    (s := Set.Icc (0 : ℝ) 1) (C := 2 * N * ‖z - z'‖) (x := 0) (y := 1) ?_ ?_ (convex_Icc 0 1)
    (by simp) (by simp)
  · have e1 : z' + ((1 : ℝ) : ℂ) * (z - z') = z := by simp
    have e0 : z' + ((0 : ℝ) : ℂ) * (z - z') = z' := by simp
    simp only [e1, e0, sub_zero, norm_one, mul_one] at key
    simpa [Real.norm_eq_abs] using key
  · intro t ht
    obtain ⟨g', hg', -⟩ := BootstrapDet_psi_deriv Λ hΛ N hN z z' hz hz' t ht
    exact hg'.differentiableAt
  · intro t ht
    obtain ⟨g', hg', hb⟩ := BootstrapDet_psi_deriv Λ hΛ N hN z z' hz hz' t ht
    rw [hg'.deriv, Real.norm_eq_abs]
    exact hb

/-- The continuity step along a vertical line (deterministic): if consecutive points move by at
most `s`, the good bounds `β_g` do not decrease and dominate `s`, and at every point
`|x_g| ≤ 2 β_g` forces `|x_g| ≤ β_g`, then `|x_0| ≤ β_0` gives `|x_g| ≤ β_g` for all `g ≤ n`. -/
theorem march_down {D : ℕ} (n : ℕ) (x : ℕ → Fin D → ℂ) (β : ℕ → ℝ) (s : ℝ)
    (hstep : ∀ g < n, ‖x (g + 1) - x g‖ ≤ s) (hβ : ∀ g < n, β g ≤ β (g + 1))
    (hs : ∀ g < n, s ≤ β (g + 1)) (hdich : ∀ g ≤ n, ‖x g‖ ≤ 2 * β g → ‖x g‖ ≤ β g)
    (h0 : ‖x 0‖ ≤ β 0) : ∀ g ≤ n, ‖x g‖ ≤ β g := by
  intro g
  induction g with
  | zero => intro _; exact h0
  | succ g ih =>
    intro hg
    have hg' : g < n := by omega
    have h1 := ih hg'.le
    have h2 : ‖x (g + 1)‖ ≤ 2 * β (g + 1) := by
      have h3 := hstep g hg'
      have h4 : ‖x (g + 1)‖ ≤ ‖x g‖ + ‖x (g + 1) - x g‖ := by
        calc ‖x (g + 1)‖ = ‖x g + (x (g + 1) - x g)‖ := by rw [add_sub_cancel]
          _ ≤ _ := norm_add_le _ _
      linarith [hβ g hg', hs g hg']
    exact hdich (g + 1) hg h2

end RBMTransitionEdge

end
