module

public import RBMTransitionEdge.Det.Shift
public import RBMTransitionEdge.LocalLaw.Class
public import RBMTransitionEdge.Localized.Pathwise
public import RBMTransitionEdge.Localized.Expansion.Eval
public import RBMTransitionEdge.Localized.Expansion.Terminate
public import RBMTransitionEdge.Localized.Expansion.Gauss
public import RBMTransitionEdge.Localized.Expansion.Bound
public import RBMTransitionEdge.Localized.Expansion.Leaf
public import RBMTransitionEdge.Localized.Expansion.LoopRem

@[expose] public section

/-!
# Lemmas 5.2 and 5.4

The integrands `⟨Im G₀ Λ̃ Im G₁ Λ̃⟩` of (5.9) [estimate_localized_eigenvector_local_law] and
`⟨Im G_t Λ̂_t Im G_t Λ̂_t⟩` of (5.23) [estimate_localized_eigenvalue_local_law], and the bounds of
Lemma 5.2 [lemma_localized_eigenvector_local_law] and Lemma 5.4
[lemma_localized_eigenvalue_local_law] on their expectations: finite, nonnegative and at most
`N^{τ + C₅ ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`, from the polarization identity (5.29)
[expansion_of_im], the expansion of §5.3 and its terminal and remainder estimates.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The integrand `⟨Im G₀ Λ̃ Im G₁ Λ̃⟩` of (5.9) [estimate_localized_eigenvector_local_law]:
`z₁ = γ_k + iη` of (5.1) [eq:z1], `z₀ = z₁ - Δ_ev` and `Λ̃ = Λ - Δ_ev` of (5.2)
[definition_shift_eigenvector], `G₀ = (H - z₀)⁻¹`, `G₁ = (H_Λ - z₁)⁻¹`. -/
def evecLoop (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε : ℝ)
    (w : Fin D → Coords N) : ℝ :=
  (ntr (imRes (blockH D N w)
      (zOne (lam D N A) k ε - (shiftEv (lam D N A) (zOne (lam D N A) k ε) : ℂ)) *
    (lam D N A - (shiftEv (lam D N A) (zOne (lam D N A) k ε) : ℂ) •
      (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
    imRes (HLam D N A w) (zOne (lam D N A) k ε) *
    (lam D N A - (shiftEv (lam D N A) (zOne (lam D N A) k ε) : ℂ) •
      (1 : Matrix (Idx D N) (Idx D N) ℂ)))).re

/-- The integrand `⟨Im G_t Λ̂_t Im G_t Λ̂_t⟩` of (5.23)
[estimate_localized_eigenvalue_local_law]: `G_t = (H + tΛ - z_t)⁻¹`, `z_t = γ_k(t) + iη` of
(5.20) [eq:z1t], `Λ̂_t = Λ - Δ(t)` with `Δ(t)` of (5.19) [definition_shift_eigenvalue]. -/
def evalLoop (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε t : ℝ)
    (w : Fin D → Coords N) : ℝ :=
  (ntr (imRes (blockH D N w + (t : ℂ) • lam D N A) (zOne ((t : ℂ) • lam D N A) k ε) *
    (lam D N A - (shiftT (lam D N A) k ε t : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
    imRes (blockH D N w + (t : ℂ) • lam D N A) (zOne ((t : ℂ) • lam D N A) k ε) *
    (lam D N A - (shiftT (lam D N A) k ε t : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)))).re


section Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖X‖ ≤ ‖X‖_HS`. -/
private lemma LL_op_le_hs (X : Matrix ι ι ℂ) : opNorm X ≤ hsNorm X := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  obtain ⟨x, rfl⟩ : ∃ x : ι → ℂ, v = WithLp.toLp 2 x := ⟨v.ofLp, rfl⟩
  rw [Matrix.toEuclideanCLM_toLp]
  have hsq : ‖(WithLp.toLp 2 (X *ᵥ x) : EuclideanSpace ℂ ι)‖ ^ 2 ≤
      (hsNorm X * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, hsNorm,
      Real.sq_sqrt (by positivity), Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => ?_
    have h1 : ‖(X *ᵥ x) p‖ ≤ ∑ q, ‖X p q‖ * ‖x q‖ := by
      simp only [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun q => ‖X p q‖) (fun q => ‖x q‖)
    calc ‖(X *ᵥ x) p‖ ^ 2 ≤ (Real.sqrt (∑ q, ‖X p q‖ ^ 2) * Real.sqrt (∑ q, ‖x q‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
      _ = (∑ q, ‖X p q‖ ^ 2) * ∑ q, ‖x q‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    two_ne_zero).1 hsq

/-- `|⟨X⟩| ≤ ‖X‖`. -/
private lemma LL_ntr_le (X : Matrix ι ι ℂ) : ‖ntr X‖ ≤ opNorm X := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp [ntr, Matrix.trace, opNorm]
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    unfold ntr Matrix.trace
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, X.diag i‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, opNorm X := by
          gcongr
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun i _ => norm_apply_le_opNorm X i i)
      _ = opNorm X := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

/-- `‖X^*‖ = ‖X‖`. -/
private lemma LL_opNorm_conjTranspose (X : Matrix ι ι ℂ) : opNorm Xᴴ = opNorm X := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) X)

/-- `Im G = η G G^*` for `G = (X - z)⁻¹`, `X` Hermitian and `Im z = η > 0`. -/
private lemma LL_imRes_eq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    imRes X z = (z.im : ℂ) • (res X z * (res X z)ᴴ) := by
  obtain ⟨h1, h2⟩ := res_mul_sub X hX z hz
  set G := res X z
  have h3 : (X - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ)) * Gᴴ = 1 := by
    have := congrArg Matrix.conjTranspose h2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_one, Matrix.conjTranspose_sub,
      hX.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one] at this
    simpa using this
  have key : G - Gᴴ = (z - starRingEnd ℂ z) • (G * Gᴴ) := by
    have e1 : G * ((X - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ)) * Gᴴ) = G := by
      rw [h3, Matrix.mul_one]
    have e2 : G * ((X - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ)) * Gᴴ) =
        Gᴴ + (z - starRingEnd ℂ z) • (G * Gᴴ) := by
      have : X - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ) =
          (X - z • (1 : Matrix ι ι ℂ)) + (z - starRingEnd ℂ z) • (1 : Matrix ι ι ℂ) := by
        rw [sub_smul]; abel
      rw [this, Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, h2, Matrix.one_mul,
        Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
    calc G - Gᴴ = (Gᴴ + (z - starRingEnd ℂ z) • (G * Gᴴ)) - Gᴴ := by rw [← e2, e1]
      _ = (z - starRingEnd ℂ z) • (G * Gᴴ) := by abel
  unfold imRes
  rw [key, smul_smul]
  congr 1
  rw [Complex.sub_conj]
  push_cast
  field_simp


open scoped ComplexOrder in
/-- `Re ⟨Im G B Im G' B⟩ ≥ 0` for Hermitian `B`, `X`, `Y` and `Im z, Im z' > 0`, with
`G = (X - z)⁻¹`, `G' = (Y - z')⁻¹`. -/
private lemma LL_re_ntr_nonneg (X Y B : Matrix ι ι ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hB : B.IsHermitian) (z z' : ℂ) (hz : 0 < z.im) (hz' : 0 < z'.im) :
    0 ≤ (ntr (imRes X z * B * imRes Y z' * B)).re := by
  rw [LL_imRes_eq X hX z hz, LL_imRes_eq Y hY z' hz']
  set G := res X z
  set G' := res Y z'
  set M := G'ᴴ * B * G
  have hM : Mᴴ * M = Gᴴ * B * G' * (G'ᴴ * B * G) := by
    simp only [M, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hB.eq,
      Matrix.mul_assoc]
  have htr : ((z.im : ℂ) • (G * Gᴴ) * B * ((z'.im : ℂ) • (G' * G'ᴴ)) * B).trace =
      ((z.im * z'.im : ℝ) : ℂ) * (Mᴴ * M).trace := by
    rw [hM]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have : (G * Gᴴ * B * (G' * G'ᴴ) * B).trace = (Gᴴ * B * G' * (G'ᴴ * B * G)).trace := by
      rw [show G * Gᴴ * B * (G' * G'ᴴ) * B = G * (Gᴴ * B * G' * (G'ᴴ * B)) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [this]; push_cast; ring
  have hpos : 0 ≤ (Mᴴ * M).trace := (posSemidef_conjTranspose_mul_self M).trace_nonneg
  have hre : 0 ≤ (Mᴴ * M).trace.re := (Complex.nonneg_iff.mp hpos).1
  unfold ntr
  rw [htr, ← mul_assoc, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hz.le hz'.le)) hre

/-- An entry of a resolvent is a measurable function of the array. -/
private lemma LL_res_meas (X : Matrix ι ι ℂ) (z : ℂ) (i j : ι) :
    Measurable fun h : ι → ι → ℂ => res (Matrix.of h + X) z i j := by
  have hc : Continuous fun h : ι → ι → ℂ => (Matrix.of h + X - z • (1 : Matrix ι ι ℂ)) :=
    (continuous_id.add continuous_const).sub continuous_const
  have e : ∀ h : ι → ι → ℂ, res (Matrix.of h + X) z i j =
      (Matrix.of h + X - z • (1 : Matrix ι ι ℂ)).det⁻¹ *
        (Matrix.of h + X - z • (1 : Matrix ι ι ℂ)).adjugate i j := by
    intro h
    unfold res
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  simp only [e]
  exact (hc.matrix_det.measurable.inv).mul
    (((continuous_apply j).comp ((continuous_apply i).comp hc.matrix_adjugate)).measurable)


omit [DecidableEq ι] in
/-- Entrywise measurability is stable under products. -/
private lemma LL_meas_mul {α : Type*} [MeasurableSpace α] {F F' : α → Matrix ι ι ℂ}
    (hF : ∀ i j, Measurable fun x => F x i j) (hF' : ∀ i j, Measurable fun x => F' x i j)
    (i j : ι) : Measurable fun x => (F x * F' x) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hF i k).mul (hF' k j)

omit [DecidableEq ι] in
/-- The normalized trace of an entrywise measurable matrix function is measurable. -/
private lemma LL_meas_ntr {α : Type*} [MeasurableSpace α] {F : α → Matrix ι ι ℂ}
    (hF : ∀ i j, Measurable fun x => F x i j) : Measurable fun x => ntr (F x) := by
  unfold ntr Matrix.trace
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hF i i)

end Mat

/-! ### The starting loop at an array -/

/-- The value of the starting loop (5.32) [eq;expT0]: `⟨𝒢₀ Λ̃ 𝒢₁ Λ̃⟩`. -/
private lemma LL_start_evalH {D N : ℕ} (e : LoopEnv D N) (h : Idx D N → Idx D N → ℂ) :
    loopStart.evalH e h = ntr (e.G h 0 * e.Lt * e.G h 1 * e.Lt) := by
  have : Unique (Fin loopStart.nb → Fin D) := inferInstanceAs (Unique (Fin 0 → Fin D))
  unfold LoopExpr.evalH
  rw [Fintype.sum_unique]
  simp [loopStart, loopWordMat, Matrix.mul_assoc]

/-- `h + c Λ` is Hermitian for a Hermitian array `h` and real `c`. -/
private lemma LL_slot_herm {D N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℝ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    (Matrix.of h + (c : ℂ) • lam D N A).IsHermitian := by
  refine hh.add ?_
  have := lam_isHermitian D N A
  unfold Matrix.IsHermitian at this ⊢
  rw [Matrix.conjTranspose_smul, this]
  simp

/-- `‖𝒢_a‖ ≤ (Im z_a)⁻¹` at a Hermitian array, for either flag. -/
private lemma LL_G_norm {D N : ℕ} (e : LoopEnv D N) (a : Fin 2) (hz : 0 < (e.z a).im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    opNorm (e.G h a) ≤ (e.z a).im⁻¹ := by
  have hX := LL_slot_herm (D := D) e.A (e.c a) h hh
  unfold LoopEnv.G
  by_cases hs : e.s a
  · simp only [hs, ite_true]
    rw [show star (e.z a) = starRingEnd ℂ (e.z a) from rfl, res_conj _ hX _ hz,
      LL_opNorm_conjTranspose]
    exact opNorm_res_le _ hX _ hz
  · simp only [hs]
    exact opNorm_res_le _ hX _ hz

/-- The starting loop is a measurable function of the array. -/
private lemma LL_start_meas {D N : ℕ} (e : LoopEnv D N) :
    Measurable fun h => loopStart.evalH e h := by
  simp only [LL_start_evalH]
  have hG : ∀ a : Fin 2, ∀ i j, Measurable fun h : Idx D N → Idx D N → ℂ => e.G h a i j :=
    fun a i j => LL_res_meas _ _ i j
  have hc : ∀ i j, Measurable fun _ : Idx D N → Idx D N → ℂ => e.Lt i j :=
    fun _ _ => measurable_const
  exact LL_meas_ntr (LL_meas_mul (LL_meas_mul (LL_meas_mul (hG 0) hc) (hG 1)) hc)

/-- `|⟨𝒢₀ Λ̃ 𝒢₁ Λ̃⟩| ≤ (Im z₀)⁻¹ (Im z₁)⁻¹ ‖Λ̃‖²` at a Hermitian array. -/
private lemma LL_start_bound {D N : ℕ} (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ‖loopStart.evalH e h‖ ≤ (e.z 0).im⁻¹ * opNorm e.Lt * (e.z 1).im⁻¹ * opNorm e.Lt := by
  rw [LL_start_evalH]
  refine (LL_ntr_le _).trans ?_
  have h0 := LL_G_norm e 0 (hz 0) h hh
  have h1 := LL_G_norm e 1 (hz 1) h hh
  have hL : 0 ≤ opNorm e.Lt := norm_nonneg _
  have hG0 : 0 ≤ opNorm (e.G h 0) := norm_nonneg _
  have hG1 : 0 ≤ opNorm (e.G h 1) := norm_nonneg _
  calc opNorm (e.G h 0 * e.Lt * e.G h 1 * e.Lt)
      ≤ opNorm (e.G h 0) * opNorm e.Lt * opNorm (e.G h 1) * opNorm e.Lt := by
        refine (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ hL)
        refine (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ hG1)
        exact opNorm_mul_le _ _
    _ ≤ _ := by
        have := (hz 0).le
        gcongr

/-- The starting loop is integrable for a member of the class. -/
private lemma LL_start_int {D N : ℕ} {C : ℕ → ℝ} (μ : Measure (Idx D N → Idx D N → ℂ))
    (hμ : LLClass D N C 1 μ) (e : LoopEnv D N) (hz : ∀ a, 0 < (e.z a).im) :
    Integrable (fun h => loopStart.evalH e h) μ := by
  have := hμ.prob
  refine Integrable.of_bound (LL_start_meas e).aestronglyMeasurable
    ((e.z 0).im⁻¹ * opNorm e.Lt * (e.z 1).im⁻¹ * opNorm e.Lt) ?_
  filter_upwards [hμ.herm] with h hh
  exact LL_start_bound e hz h hh

/-! ### Pathwise facts -/

/-- `Λ - δ` is Hermitian for real `δ`. -/
private lemma LL_Lt_herm (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (δ : ℝ) :
    (lam D N A - (δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)).IsHermitian := by
  have := lam_isHermitian D N A
  unfold Matrix.IsHermitian at this ⊢
  rw [Matrix.conjTranspose_sub, this, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

/-- The block matrix `H` of (1.3) [matrix_H], read as an array, is Hermitian. -/
private lemma LL_blockH_herm (D N : ℕ) (w : Fin D → Coords N) :
    (Matrix.of (Matrix.of.symm (blockH D N w))).IsHermitian := by
  have h0 : lam D N (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
    ext p q
    simp [lam]
  have := HLam_isHermitian D N 0 w
  rw [HLam, h0, add_zero] at this
  rw [Equiv.apply_symm_apply]
  exact this

/-- (5.29) [expansion_of_im] for the integrand of (5.9)
[estimate_localized_eigenvector_local_law]: `⟨Im G₀ Λ̃ Im G₁ Λ̃⟩` is `-1/4` times the signed sum
of the four flagged starting loops at the slots `(H, z₀)`, `(H + Λ, z₁)`. -/
private lemma LL_evec_polar (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε : ℝ)
    (w : Fin D → Coords N) :
    evecLoop D N A k ε w = (-(1 / 4 : ℂ) * ∑ s : Fin 2 → Bool,
      (if s 0 = s 1 then (1 : ℂ) else -1) *
        loopStart.evalH (evecEnv D N A k ε s) (Matrix.of.symm (blockH D N w))).re := by
  have hp := loop_polar (evecEnv D N A k ε fun _ => false) (Matrix.of.symm (blockH D N w))
    (LL_blockH_herm D N w)
  have hS : ∀ s : Fin 2 → Bool,
      ({ evecEnv D N A k ε (fun _ => false) with s := s } : LoopEnv D N) = evecEnv D N A k ε s :=
    fun s => rfl
  simp only [hS] at hp
  rw [hp]
  simp only [evecEnv, LoopEnv.Lt, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.ofReal_zero, Complex.ofReal_one, zero_smul, one_smul, add_zero, Equiv.apply_symm_apply]
  unfold evecLoop HLam
  congr 1
  ring

/-- (5.29) [expansion_of_im] for the integrand of (5.23)
[estimate_localized_eigenvalue_local_law], at the slots `(H + tΛ, z_t)` twice. -/
private lemma LL_eval_polar (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε t : ℝ)
    (w : Fin D → Coords N) :
    evalLoop D N A k ε t w = (-(1 / 4 : ℂ) * ∑ s : Fin 2 → Bool,
      (if s 0 = s 1 then (1 : ℂ) else -1) *
        loopStart.evalH (evalEnv D N A k ε t s) (Matrix.of.symm (blockH D N w))).re := by
  have hp := loop_polar (evalEnv D N A k ε t fun _ => false) (Matrix.of.symm (blockH D N w))
    (LL_blockH_herm D N w)
  have hS : ∀ s : Fin 2 → Bool,
      ({ evalEnv D N A k ε t (fun _ => false) with s := s } : LoopEnv D N) =
        evalEnv D N A k ε t s :=
    fun s => rfl
  simp only [hS] at hp
  rw [hp]
  simp only [evalEnv, LoopEnv.Lt, Matrix.cons_val_zero, Matrix.cons_val_one,
    Equiv.apply_symm_apply]
  unfold evalLoop
  congr 1
  ring

/-- `⟨Im G₀ Λ̃ Im G₁ Λ̃⟩ ≥ 0` at every point, for `Im z₀, Im z₁ > 0`. -/
private lemma LL_evec_nonneg (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε : ℝ)
    (hz : ∀ a, 0 < ((evecEnv D N A k ε fun _ => false).z a).im) (w : Fin D → Coords N) :
    0 ≤ evecLoop D N A k ε w := by
  have hH := LL_blockH_herm D N w
  rw [Equiv.apply_symm_apply] at hH
  exact LL_re_ntr_nonneg _ _ _ hH (HLam_isHermitian D N A w) (LL_Lt_herm D N A _) _ _ (hz 0)
    (hz 1)

/-- `⟨Im G_t Λ̂_t Im G_t Λ̂_t⟩ ≥ 0` at every point, for `Im z_t > 0`. -/
private lemma LL_eval_nonneg (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (ε t : ℝ)
    (hz : ∀ a, 0 < ((evalEnv D N A k ε t fun _ => false).z a).im) (w : Fin D → Coords N) :
    0 ≤ evalLoop D N A k ε t w := by
  have hX := LL_slot_herm (D := D) A t _ (LL_blockH_herm D N w)
  rw [Equiv.apply_symm_apply] at hX
  exact LL_re_ntr_nonneg _ _ _ hX hX (LL_Lt_herm D N A _) _ _ (hz 0) (hz 0)

/-- The map `w ↦ H`, read as an array, is measurable. -/
private lemma LL_g_meas (D N : ℕ) :
    Measurable fun w : Fin D → Coords N => Matrix.of.symm (blockH D N w) := by
  refine measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => ?_
  simp only [Matrix.of_symm_apply, blockH, wig]
  split_ifs
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop

/-- The integral of `-1/4` times the real part of a signed sum of starting loops against the
law of `H`: integrable, nonnegative when the integrand is, and at most `Y` when the signed sum of
the expectations is at most `4Y`. -/
private lemma LL_assemble {D N : ℕ} {C : ℕ → ℝ} (L : EntryLaws C)
    (E : (Fin 2 → Bool) → LoopEnv D N) (hz : ∀ s a, 0 < ((E s).z a).im)
    (f : (Fin D → Coords N) → ℝ)
    (hf : ∀ w, f w = (-(1 / 4 : ℂ) * ∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
        loopStart.evalH (E s) (Matrix.of.symm (blockH D N w))).re)
    (hpos : ∀ w, 0 ≤ f w) (Y : ℝ)
    (hY : ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
        ∫ h, loopStart.evalH (E s) h ∂((blockLaw D N L).map
          fun w => Matrix.of.symm (blockH D N w))‖ ≤ 4 * Y) :
    Integrable f (blockLaw D N L) ∧ 0 ≤ ∫ w, f w ∂(blockLaw D N L) ∧
      ∫ w, f w ∂(blockLaw D N L) ≤ Y := by
  set P := blockLaw D N L
  set g := fun w => Matrix.of.symm (blockH D N w)
  have hg : AEMeasurable g P := (LL_g_meas D N).aemeasurable
  have hFμ : ∀ s, Integrable (fun h => loopStart.evalH (E s) h) (P.map g) :=
    fun s => LL_start_int _ (llClass_blockH D N C L) (E s) (hz s)
  have hFP : ∀ s, Integrable (fun w => loopStart.evalH (E s) (g w)) P := fun s =>
    (integrable_map_measure (LL_start_meas _).aestronglyMeasurable hg).mp (hFμ s)
  have hsum : Integrable (fun w => -(1 / 4 : ℂ) * ∑ s : Fin 2 → Bool,
      (if s 0 = s 1 then (1 : ℂ) else -1) * loopStart.evalH (E s) (g w)) P :=
    (integrable_finsetSum _ fun s _ => (hFP s).const_mul _).const_mul _
  have hfe : f = fun w => (-(1 / 4 : ℂ) * ∑ s : Fin 2 → Bool,
      (if s 0 = s 1 then (1 : ℂ) else -1) * loopStart.evalH (E s) (g w)).re := funext hf
  have hint : Integrable f P := by rw [hfe]; exact hsum.re
  refine ⟨hint, integral_nonneg hpos, ?_⟩
  have hI : ∫ w, f w ∂P = (-(1 / 4 : ℂ) * ∑ s : Fin 2 → Bool,
      (if s 0 = s 1 then (1 : ℂ) else -1) *
        ∫ h, loopStart.evalH (E s) h ∂(P.map g)).re := by
    have hre := integral_re (𝕜 := ℂ) hsum
    simp only [RCLike.re_to_complex] at hre
    rw [hfe, hre]
    congr 1
    rw [integral_const_mul, integral_finsetSum _ fun s _ => (hFP s).const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_const_mul, integral_map hg (LL_start_meas _).aestronglyMeasurable]
  rw [hI]
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_mul]
  have : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [this]
  linarith


/-- `1 ≤ 𝔯(k) ≤ DN` for `1 ≤ k` and `2k ≤ DN + 1`. -/
private lemma LL_rk_bounds (D N k : ℕ) (hk : 1 ≤ k) (hkN : 2 * k ≤ D * N + 1) :
    1 ≤ rk D N k ∧ rk D N k ≤ (D : ℝ) * N := by
  unfold rk
  have h1 : 1 ≤ min k (D * N + 1 - k) := le_min hk (by omega)
  have h2 : min k (D * N + 1 - k) ≤ D * N := (min_le_right _ _).trans (by omega)
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- `η ≥ D⁻¹ N^{-1+ε}` for `η = N^{-2/3+ε} 𝔯(k)^{-1/3}`. -/
private lemma LL_eta_lower (D N k : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hkN : 2 * k ≤ D * N + 1) (ε : ℝ) :
    (D : ℝ)⁻¹ * (N : ℝ) ^ (-1 + ε) ≤ etaK D N k ε := by
  obtain ⟨hr1, hr2⟩ := LL_rk_bounds D N k hk hkN
  have hx : (0 : ℝ) < N := by exact_mod_cast hN
  have hD0 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hr0 : (0 : ℝ) < rk D N k := by linarith
  unfold etaK
  have h1 : ((D : ℝ) * N) ^ (-(1 / 3 : ℝ)) ≤ rk D N k ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hr0 hr2 (by norm_num)
  rw [Real.mul_rpow (by linarith) hx.le] at h1
  have h2 : (D : ℝ)⁻¹ ≤ (D : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hD0 (by norm_num)
  have h3 : (N : ℝ) ^ (-1 + ε) = (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_add hx]; ring_nf
  rw [h3]
  calc (D : ℝ)⁻¹ * ((N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * (N : ℝ) ^ (-(1 / 3 : ℝ)))
      = (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * ((D : ℝ)⁻¹ * (N : ℝ) ^ (-(1 / 3 : ℝ))) := by ring
    _ ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * ((D : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(1 / 3 : ℝ))) := by
        gcongr
    _ ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + ε) * rk D N k ^ (-(1 / 3 : ℝ)) := by gcongr

/-- `N^{-5/3} ‖A‖² ≤ N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS`. -/
private lemma LL_target_lower (D N k : ℕ) (hk : 1 ≤ k) (hkN : 2 * k ≤ D * N + 1)
    (A : Matrix (Fin N) (Fin N) ℂ) (hop : opNorm A ≤ hsNorm A) :
    (N : ℝ) ^ (-(5 / 3 : ℝ)) * opNorm A ^ 2 ≤
      (N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2 := by
  obtain ⟨hr1, -⟩ := LL_rk_bounds D N k hk hkN
  have h1 : 1 ≤ rk D N k ^ (2 / 3 : ℝ) := Real.one_le_rpow hr1 (by norm_num)
  have h0 : 0 ≤ opNorm A := norm_nonneg _
  have h2 : opNorm A ^ 2 ≤ hsNorm A ^ 2 := pow_le_pow_left₀ h0 hop 2
  have hN : 0 ≤ (N : ℝ) ^ (-(5 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [mul_assoc]
  gcongr
  calc opNorm A ^ 2 ≤ 1 * hsNorm A ^ 2 := by linarith
    _ ≤ _ := by gcongr

/-- The bound of a leaf stopped by `Ψ ≥ 4` ((5.48) [eq:Tsmallthansize] and criterion (i) above
(5.49) [operation_sequence]): `N^{-size₁} η^{-E} ‖A‖² ≤ N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS` when
`0 ≤ E ≤ size₂ + 1`, `Ψ ≥ 4`, `ε ≤ 1/3` and `D^E ≤ N`. -/
private lemma LL_psi_arith (D N k : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hkN : 2 * k ≤ D * N + 1) (ε : ℝ) (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) (s₁ s₂ E : ℤ)
    (hE0 : 0 ≤ E) (hE1 : E ≤ s₂ + 1)
    (hpsi : 4 ≤ ((s₁ - s₂ : ℤ) : ℝ) + ε * ((s₂ + 2 : ℤ) : ℝ))
    (hDE : (D : ℝ) ^ E.toNat ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) (hop : opNorm A ≤ hsNorm A) :
    (N : ℝ) ^ (-s₁) * etaK D N k ε ^ (-E) * opNorm A ^ 2 ≤
      (N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2 := by
  set x : ℝ := (N : ℝ) with hxdef
  have hx1 : (1 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hN
  have hx0 : (0 : ℝ) < x := by linarith
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  set e := E.toNat with hedef
  have hEe : (e : ℤ) = E := Int.toNat_of_nonneg hE0
  set y : ℝ := (D : ℝ)⁻¹ * x ^ (-1 + ε) with hydef
  have hy0 : 0 < y := by positivity
  have hyη : y ≤ etaK D N k ε := LL_eta_lower D N k hD hN hk hkN ε
  have hη : etaK D N k ε ^ (-E) ≤ (D : ℝ) ^ e * x ^ ((1 - ε) * e) := by
    rw [← hEe, _root_.zpow_neg, zpow_natCast]
    calc (etaK D N k ε ^ e)⁻¹ ≤ (y ^ e)⁻¹ :=
          inv_anti₀ (pow_pos hy0 e) (pow_le_pow_left₀ hy0.le hyη e)
      _ = (D : ℝ) ^ e * x ^ ((1 - ε) * e) := by
          rw [← inv_pow, hydef, mul_inv, inv_inv, ← Real.rpow_neg hx0.le, mul_pow,
            ← Real.rpow_natCast (x ^ (-(-1 + ε))), ← Real.rpow_mul hx0.le]
          ring_nf
  have hs : x ^ (-s₁) = x ^ ((-s₁ : ℤ) : ℝ) := (Real.rpow_intCast x (-s₁)).symm
  have hexp : ((-s₁ : ℤ) : ℝ) + (1 - ε) * e ≤ -3 + ε := by
    have he : (e : ℝ) = (E : ℝ) := by exact_mod_cast hEe
    have hE1' : (E : ℝ) ≤ s₂ + 1 := by exact_mod_cast hE1
    push_cast at hpsi ⊢
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hE1' (by linarith : (0 : ℝ) ≤ 1 - ε)]
  have hop0 : 0 ≤ opNorm A := norm_nonneg _
  calc x ^ (-s₁) * etaK D N k ε ^ (-E) * opNorm A ^ 2
      ≤ x ^ ((-s₁ : ℤ) : ℝ) * ((D : ℝ) ^ e * x ^ ((1 - ε) * e)) * opNorm A ^ 2 := by
        rw [hs]; gcongr
    _ = (D : ℝ) ^ e * x ^ (((-s₁ : ℤ) : ℝ) + (1 - ε) * e) * opNorm A ^ 2 := by
        rw [Real.rpow_add hx0]; ring
    _ ≤ x * x ^ (-3 + ε) * opNorm A ^ 2 := by
        gcongr
    _ = x ^ (-2 + ε) * opNorm A ^ 2 := by
        rw [show -2 + ε = 1 + (-3 + ε) by ring, Real.rpow_add hx0 1 (-3 + ε), Real.rpow_one]
    _ ≤ x ^ (-(5 / 3 : ℝ)) * opNorm A ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
          (by positivity)
    _ ≤ _ := LL_target_lower D N k hk hkN A hop


/-- An expression of the class (5.33) [definition_class_of_expression_loop] of Type II (`Λ̃₁`,
`Λ̃₂` in different loops) has at least two loops. -/
private lemma LL_typeII_len (T : LoopExpr) (hwf : T.wf = true) (hII : T.typeI = false) :
    2 ≤ T.loops.length := by
  unfold LoopExpr.wf at hwf
  simp only [Bool.and_eq_true, beq_iff_eq] at hwf
  obtain ⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, -⟩ := hwf
  unfold LoopExpr.typeI at hII
  rcases hl : T.loops with _ | ⟨w, _ | ⟨w', rest⟩⟩
  · simp [hl] at h0
  · simp only [hl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h0 h1
    simp only [hl, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff] at hII
    have m0 : LoopLetter.lamt 0 ∈ w := List.count_pos_iff.mp (by omega)
    have m1 : LoopLetter.lamt 1 ∈ w := List.count_pos_iff.mp (by omega)
    rcases hII with h | h <;> simp_all
  · simp

/-- On the expansion of §5.3, `size₂ + 1(k₁ = 0) + 1(k₂ = 0) ≥ 0`, from (5.37)
[number_of_G_type_1]. -/
private lemma LL_E_nonneg (ε : ℝ) (n : ℕ) (T : LoopExpr) (hT : T ∈ loopIter ε n [loopStart]) :
    0 ≤ T.size.2 + (if T.kk 0 = 0 then 1 else 0) + (if T.kk 1 = 0 then 1 else 0) := by
  obtain ⟨hwf, hk01, -, -⟩ := loop_reach ε n T (Or.inl hT)
  obtain ⟨hI, hII⟩ := loop_count_res ε n T (Or.inl hT)
  have hk2 := loop_kk_typeII ε n T (Or.inl hT)
  have hs2 : T.size.2 = T.charsZ.1 - T.charsZ.2.1 + T.charsZ.2.2.1 := rfl
  have hu : T.charsZ.2.2.1 = (T.weights.length : ℤ) := rfl
  have hn : T.charsZ.2.1 = (T.loops.length : ℤ) := rfl
  rw [hs2]
  cases htype : T.typeI
  · have hlen := LL_typeII_len T hwf htype
    have := hII htype
    have := hk2 htype
    split_ifs <;> omega
  · have := hI htype
    split_ifs <;> omega

/-! ### Finite families and the signed sums -/

/-- A threshold uniform over a finite set. -/
private lemma LL_fin {α : Type*} (s : Finset α) (P : α → ℕ → Prop)
    (h : ∀ x ∈ s, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → P x N) :
    ∃ N₀ : ℕ, ∀ x ∈ s, ∀ N, N₀ ≤ N → P x N := by
  choose! f hf using h
  exact ⟨s.sup f, fun x hx N hN => hf x hx N ((Finset.le_sup hx).trans hN)⟩

/-- `X ≤ N^a` for all large `N`. -/
private lemma LL_large (a X : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → X ≤ (N : ℝ) ^ a := by
  have h := ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop X)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨N₀, hN₀⟩

/-- The signed sum over the flags commutes with a list sum. -/
private lemma LL_swap {α : Type*} (l : List α) (c : (Fin 2 → Bool) → ℂ)
    (f : (Fin 2 → Bool) → α → ℂ) :
    ∑ s, c s * (l.map (f s)).sum = (l.map fun T => ∑ s, c s * f s T).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]

/-- A list sum of terms of norm at most `X`. -/
private lemma LL_list_norm {α : Type*} (l : List α) (g : α → ℂ) (X : ℝ)
    (h : ∀ T ∈ l, ‖g T‖ ≤ X) : ‖(l.map g).sum‖ ≤ l.length * X := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun T hT => h T (List.mem_cons_of_mem a hT)
    calc ‖g a + (l.map g).sum‖ ≤ ‖g a‖ + ‖(l.map g).sum‖ := norm_add_le _ _
      _ ≤ X + l.length * X := add_le_add h1 h2
      _ = ((l.length + 1 : ℕ) : ℝ) * X := by push_cast; ring

/-- The signed flag sum `Σ_s ±1 · a_s` is at most `4 max_s |a_s|`. -/
private lemma LL_flag_norm (a : (Fin 2 → Bool) → ℂ) (X : ℝ) (h : ∀ s, ‖a s‖ ≤ X) :
    ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) * a s‖ ≤ 4 * X := by
  refine (norm_sum_le _ _).trans ?_
  have hc : Fintype.card (Fin 2 → Bool) = 4 := by simp
  calc ∑ s : Fin 2 → Bool, ‖(if s 0 = s 1 then (1 : ℂ) else -1) * a s‖
      ≤ ∑ _s : Fin 2 → Bool, X := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [norm_mul]
        split_ifs <;> simpa using h s
    _ = 4 * X := by
        rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]; norm_num

/-- The signed sum of the expectations of the starting loops, from the tree identity of the
expansion of §5.3 and bounds on the signed sums of its leaves and remainders. -/
private lemma LL_combine {D N : ℕ} (μ : Measure (Idx D N → Idx D N → ℂ))
    (E : (Fin 2 → Bool) → LoopEnv D N) (I J : List LoopExpr) (l : ℕ) (X err : ℝ)
    (htree : ∀ s, ‖(∫ h, loopStart.evalH (E s) h ∂μ) -
        (I.map fun T => ∫ h, T.evalH (E s) h ∂μ).sum -
        (J.map fun T => ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
          (if 2 ≤ p + q then T.remPQ (E s) μ p q else 0)).sum‖ ≤ err)
    (hI : ∀ T ∈ I, ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
        ∫ h, T.evalH (E s) h ∂μ‖ ≤ 4 * X)
    (hJ : ∀ T ∈ J, ∀ p q : ℕ, 2 ≤ p + q → p < l + 1 → q < l + 1 →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) * T.remPQ (E s) μ p q‖ ≤ X)
    (herr : err ≤ X) (hX : 0 ≤ X) :
    ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
        ∫ h, loopStart.evalH (E s) h ∂μ‖ ≤
      (4 * I.length + (l + 1) * (l + 1) * J.length + 4) * X := by
  set c : (Fin 2 → Bool) → ℂ := fun s => if s 0 = s 1 then (1 : ℂ) else -1 with hcdef
  set R : (Fin 2 → Bool) → LoopExpr → ℂ := fun s T =>
    ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
      (if 2 ≤ p + q then T.remPQ (E s) μ p q else 0) with hRdef
  set d : (Fin 2 → Bool) → ℂ := fun s => (∫ h, loopStart.evalH (E s) h ∂μ) -
    (I.map fun T => ∫ h, T.evalH (E s) h ∂μ).sum - (J.map (R s)).sum with hddef
  have hsplit : ∑ s, c s * ∫ h, loopStart.evalH (E s) h ∂μ =
      (I.map fun T => ∑ s, c s * ∫ h, T.evalH (E s) h ∂μ).sum +
        (J.map fun T => ∑ s, c s * R s T).sum + ∑ s, c s * d s := by
    rw [← LL_swap I c (fun s T => ∫ h, T.evalH (E s) h ∂μ), ← LL_swap J c R,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hddef]
    ring
  have hRb : ∀ T ∈ J, ‖∑ s, c s * R s T‖ ≤ (l + 1) * (l + 1) * X := by
    intro T hT
    have hswap : ∑ s, c s * R s T = ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        (if 2 ≤ p + q then ∑ s, c s * T.remPQ (E s) μ p q else 0) := by
      simp only [hRdef, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs <;> simp
    rw [hswap]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p ∈ Finset.range (l + 1), ‖∑ q ∈ Finset.range (l + 1 - p),
          (if 2 ≤ p + q then ∑ s, c s * T.remPQ (E s) μ p q else 0)‖
        ≤ ∑ p ∈ Finset.range (l + 1), ((l + 1 - p : ℕ) : ℝ) * X := by
          refine Finset.sum_le_sum fun p hp => (norm_sum_le _ _).trans ?_
          calc ∑ q ∈ Finset.range (l + 1 - p),
                ‖(if 2 ≤ p + q then ∑ s, c s * T.remPQ (E s) μ p q else 0)‖
              ≤ ∑ _q ∈ Finset.range (l + 1 - p), X := by
                refine Finset.sum_le_sum fun q hq => ?_
                split_ifs with hpq
                · exact hJ T hT p q hpq (Finset.mem_range.mp hp)
                    (by have := Finset.mem_range.mp hq; omega)
                · simpa using hX
            _ = ((l + 1 - p : ℕ) : ℝ) * X := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ _p ∈ Finset.range (l + 1), ((l : ℝ) + 1) * X := by
          refine Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right ?_ hX
          have : (l + 1 - p : ℕ) ≤ l + 1 := Nat.sub_le _ _
          exact_mod_cast this
      _ = (l + 1) * (l + 1) * X := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hdb : ‖∑ s, c s * d s‖ ≤ 4 * X :=
    LL_flag_norm d X fun s => (htree s).trans herr
  rw [hsplit]
  have h1 := LL_list_norm I _ (4 * X) hI
  have h2 := LL_list_norm J _ _ hRb
  calc ‖(I.map fun T => ∑ s, c s * ∫ h, T.evalH (E s) h ∂μ).sum +
        (J.map fun T => ∑ s, c s * R s T).sum + ∑ s, c s * d s‖
      ≤ ‖(I.map fun T => ∑ s, c s * ∫ h, T.evalH (E s) h ∂μ).sum‖ +
        ‖(J.map fun T => ∑ s, c s * R s T).sum‖ + ‖∑ s, c s * d s‖ := norm_add₃_le
    _ ≤ I.length * (4 * X) + J.length * ((l + 1) * (l + 1) * X) + 4 * X := by gcongr
    _ = _ := by ring

/-! ### The bound on the signed sum of the starting loops -/

/-- The hypotheses of Lemmas 5.2 [lemma_localized_eigenvector_local_law] and 5.4
[lemma_localized_eigenvalue_local_law] at size `N` ((2.8) [eq:condA2], `1 ≤ k`, `2k ≤ DN + 1`),
a member `μ` of the class and the slots `E` of either lemma, imply `P μ A k E`. -/
private def LL_ok (D : ℕ) (δA εA : ℝ) (C : ℕ → ℝ) (ε : ℝ) (N : ℕ)
    (P : Measure (Idx D N → Idx D N → ℂ) → Matrix (Fin N) (Fin N) ℂ → ℕ →
      ((Fin 2 → Bool) → LoopEnv D N) → Prop) : Prop :=
  ∀ μ : Measure (Idx D N → Idx D N → ℂ), LLClass D N C 1 μ →
    ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
    hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
    ∀ E : (Fin 2 → Bool) → LoopEnv D N,
      (E = evecEnv D N A k ε ∨ ∃ t ∈ Set.Icc (0 : ℝ) 1, E = evalEnv D N A k ε t) → P μ A k E

/-- The signed sum of the four flagged starting loops (5.32) [eq;expT0] at the slots of
Lemma 5.2 [lemma_localized_eigenvector_local_law] or of Lemma 5.4
[lemma_localized_eigenvalue_local_law] is at most `4 N^{τ + 2ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS` in
expectation, for every member of the class: the expansion of §5.3 with its leaves (5.54)–(5.59),
the leaves stopped by `Ψ` and the remainders of Lemma 5.5 [claim_estimate_remainder_terms]. -/
private lemma LL_main (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA) (hεA : 0 < εA)
    (C : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (hεA' : ε < εA) (hε3 : ε < 1 / 3) (τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → LL_ok D δA εA C ε N fun μ A k E =>
      ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
          ∫ h, loopStart.evalH (E s) h ∂μ‖ ≤
        4 * ((N : ℝ) ^ (τ + 2 * ε) *
          ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2)) := by
  obtain ⟨c₀, K, hc₀, -, N₁, hN₁⟩ :=
    loop_env_admissible D hD δA εA ε hδA hεA hε (by linarith) hε3.le
  obtain ⟨n, hn⟩ := loop_terminates ε hε (by linarith)
  obtain ⟨l, -, N₂, hN₂⟩ :=
    loop_tree_sum D hD δA (ε / 2) 1 K ε hδA (by positivity) le_rfl C n 2 two_pos
  set I := loopIter ε n [loopStart] with hIdef
  set J := loopInner ε n [loopStart] with hJdef
  have hτ2 : 0 < τ / 2 := by positivity
  have hD1 : 1 ≤ D := by omega
  -- the slots of either lemma
  have hslots : ∀ N, N₁ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ E : (Fin 2 → Bool) → LoopEnv D N,
      (E = evecEnv D N A k ε ∨ ∃ t ∈ Set.Icc (0 : ℝ) 1, E = evalEnv D N A k ε t) → ∀ s,
        (E s).A = A ∧ 2 * 1 * opNorm (E s).A ≤ 1 / 10 ∧ (∀ a, |(E s).c a| ≤ 1) ∧
        (∀ a, (E s).z a ∈ specDom (ε / 2) N ∧ 0 < ((E s).z a).im ∧
          ((E s).z a).im = etaK D N k ε ∧
          c₀ ≤ (N : ℝ) * ((E s).z a).im * (mSol (((E s).c a : ℂ) • lam D N (E s).A)
            ((E s).z a)).im) ∧
        |(E s).δ| ≤ K * avgSq (lam D N (E s).A) := by
    intro N hN A hA k hk hkN hhs E hE s
    have hEA : (E s).A = A := by rcases hE with rfl | ⟨t, -, rfl⟩ <;> rfl
    have hmem : (∃ s', E s = evecEnv D N A k ε s') ∨
        ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s', E s = evalEnv D N A k ε t s' := by
      rcases hE with rfl | ⟨t, ht, rfl⟩
      · exact Or.inl ⟨s, rfl⟩
      · exact Or.inr ⟨t, ht, s, rfl⟩
    obtain ⟨h2A, hc, hz, hδ⟩ := hN₁ N hN A hA k hk hkN hhs (E s) hmem
    exact ⟨hEA, by linarith, hc, hz, hδ⟩
  -- the leaves
  obtain ⟨NI, hNI⟩ : ∃ NI : ℕ, ∀ T ∈ I.toFinset, ∀ N, NI ≤ N →
      LL_ok D δA εA C ε N fun μ A k E =>
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            ∫ h, T.evalH (E s) h ∂μ‖ ≤
          4 * ((N : ℝ) ^ (τ / 2 + 2 * ε) *
            ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2)) := by
    refine LL_fin _ _ fun T hT => ?_
    have hT' : T ∈ I := List.mem_toFinset.mp hT
    by_cases hkk : T.kk 0 = 0 ∧ T.kk 1 = 0
    · obtain ⟨N₀, h⟩ := loop_leaf_bound D hD δA εA ε hδA hεA hε (by linarith) hε3.le C n T hT'
        hkk (τ / 2) hτ2
      refine ⟨N₀, fun N hN μ hμ A hA k hk hkN hhs E hE => ?_⟩
      have hX0 : 0 ≤ (N : ℝ) ^ (τ / 2 + 2 * ε) *
          ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2) := by
        unfold rk; positivity
      have h' := h N hN μ hμ A hA k hk hkN hhs
      rcases hE with rfl | ⟨t, ht, rfl⟩
      · linarith [h'.1]
      · linarith [h'.2 t ht]
    · have hpsi : 4 ≤ T.psi ε := (hn T hT').resolve_right hkk
      have hwf := (loop_reach ε n T (Or.inl hT')).1
      obtain ⟨Ng, hg⟩ := loop_generic_bound D hD δA (ε / 2) c₀ 1 K hδA (by positivity) hc₀ le_rfl
        C T hwf (τ / 2) hτ2
      have hE0 := LL_E_nonneg ε n T hT'
      set Ee : ℤ := T.size.2 + (if T.kk 0 = 0 then 1 else 0) + (if T.kk 1 = 0 then 1 else 0)
        with hEe
      have hE1 : Ee ≤ T.size.2 + 1 := by
        rw [hEe]
        split_ifs <;> omega
      obtain ⟨N₃, hN₃⟩ := LL_large 1 ((D : ℝ) ^ Ee.toNat) one_pos
      refine ⟨max (max Ng N₁) (max N₃ 1), fun N hN μ hμ A hA k hk hkN hhs E hE => ?_⟩
      have hNg : Ng ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
      have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
      have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
      have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
      have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      refine LL_flag_norm _ _ fun s => ?_
      obtain ⟨hEA, h2A, hc, hz, hδ⟩ := hslots N hN1' A hA k hk hkN hhs E hE s
      have hb := hg N hNg μ hμ (E s) (by rw [hEA]; exact hA) h2A hc
        (fun a => ⟨(hz a).1, (hz a).2.1, (hz a).2.2.2⟩) hδ
      rw [(hz 0).2.2.1, (hz 1).2.2.1, min_self, hEA] at hb
      refine hb.trans ?_
      have hDE : (D : ℝ) ^ Ee.toNat ≤ N := by
        have := hN₃ N hN3
        rwa [Real.rpow_one] at this
      have hpsi' : 4 ≤ ((T.size.1 - T.size.2 : ℤ) : ℝ) + ε * ((T.size.2 + 2 : ℤ) : ℝ) := hpsi
      have harith := LL_psi_arith D N k hD1 hN1 hk hkN ε hε hε3.le T.size.1 T.size.2 Ee hE0 hE1
        hpsi' hDE A (LL_op_le_hs A)
      have hT0 : 0 ≤ (N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2 := by
        unfold rk; positivity
      calc (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (-T.size.1) * etaK D N k ε ^ (-Ee) * opNorm A ^ 2)
          ≤ (N : ℝ) ^ (τ / 2) *
              ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2) := by
            gcongr
        _ ≤ (N : ℝ) ^ (τ / 2 + 2 * ε) *
              ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2) := by
            exact mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) hT0
  -- the remainders
  obtain ⟨NJ, hNJ⟩ : ∃ NJ : ℕ,
      ∀ x ∈ J.toFinset ×ˢ (Finset.range (l + 1) ×ˢ Finset.range (l + 1)), ∀ N, NJ ≤ N →
      LL_ok D δA εA C ε N fun μ A k E => 2 ≤ x.2.1 + x.2.2 →
        ‖∑ s : Fin 2 → Bool, (if s 0 = s 1 then (1 : ℂ) else -1) *
            x.1.remPQ (E s) μ x.2.1 x.2.2‖ ≤
          (N : ℝ) ^ (τ / 2 + 2 * ε) *
            ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2) := by
    refine LL_fin _ _ fun x hx => ?_
    obtain ⟨T, p, q⟩ := x
    simp only [Finset.mem_product, List.mem_toFinset] at hx
    by_cases hpq : 2 ≤ p + q
    · obtain ⟨N₀, h⟩ := loop_rem_bound D hD δA εA ε hδA hεA hε (by linarith) hε3.le C n T hx.1
        p q hpq (τ / 2) hτ2
      refine ⟨N₀, fun N hN μ hμ A hA k hk hkN hhs E hE _ => ?_⟩
      have h' := h N hN μ hμ A hA k hk hkN hhs
      rcases hE with rfl | ⟨t, ht, rfl⟩
      · exact h'.1
      · exact h'.2 t ht
    · exact ⟨0, fun N _ μ _ A _ k _ _ _ E _ h => absurd h hpq⟩
  -- the number of terms
  obtain ⟨NB, hNB⟩ := LL_large (τ / 2)
    (4 * I.length + (l + 1) * (l + 1) * J.length + 4 : ℝ) hτ2
  refine ⟨max (max N₁ N₂) (max (max NI NJ) (max NB 1)), ?_⟩
  intro N hN μ hμ A hA k hk hkN hhs E hE
  have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNI' : NI ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hN
  have hNJ' : NJ ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)) hN
  have hNB' : NB ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hN
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx0 : (0 : ℝ) < N := by linarith
  set T₀ : ℝ := (N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2 with hT₀
  have hT0 : 0 ≤ T₀ := by rw [hT₀]; unfold rk; positivity
  set X : ℝ := (N : ℝ) ^ (τ / 2 + 2 * ε) * T₀ with hX
  have hX0 : 0 ≤ X := by positivity
  have htree : ∀ s, ‖(∫ h, loopStart.evalH (E s) h ∂μ) -
      (I.map fun T => ∫ h, T.evalH (E s) h ∂μ).sum -
      (J.map fun T => ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (l + 1 - p),
        (if 2 ≤ p + q then T.remPQ (E s) μ p q else 0)).sum‖ ≤
      (N : ℝ) ^ (-(2 : ℝ)) * opNorm A ^ 2 := by
    intro s
    obtain ⟨hEA, h2A, hc, hz, hδ⟩ := hslots N hN1' A hA k hk hkN hhs E hE s
    have := hN₂ N hN2 μ hμ (E s) (by rw [hEA]; exact hA) h2A hc
      (fun a => ⟨(hz a).1, (hz a).2.1⟩) hδ
    rwa [hEA] at this
  have herr : (N : ℝ) ^ (-(2 : ℝ)) * opNorm A ^ 2 ≤ X := by
    have h1 : (N : ℝ) ^ (-(2 : ℝ)) * opNorm A ^ 2 ≤ (N : ℝ) ^ (-(5 / 3 : ℝ)) * opNorm A ^ 2 :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
        (sq_nonneg _)
    have h2 := LL_target_lower D N k hk hkN A (LL_op_le_hs A)
    have h3 : T₀ ≤ X := le_mul_of_one_le_left hT0
      (Real.one_le_rpow hx1 (by positivity))
    linarith
  have hcomb := LL_combine μ E I J l X _ htree
    (fun T hT => hNI T (List.mem_toFinset.mpr hT) N hNI' μ hμ A hA k hk hkN hhs E hE)
    (fun T hT p q hpq hp hq => hNJ (T, p, q)
      (Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hT,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr hp, Finset.mem_range.mpr hq⟩⟩)
      N hNJ' μ hμ A hA k hk hkN hhs E hE hpq)
    herr hX0
  refine hcomb.trans ?_
  have hB := hNB N hNB'
  have hY : 0 ≤ (N : ℝ) ^ (τ + 2 * ε) * T₀ := by positivity
  calc (4 * I.length + (l + 1) * (l + 1) * J.length + 4 : ℝ) * X
      ≤ (N : ℝ) ^ (τ / 2) * X := mul_le_mul_of_nonneg_right hB hX0
    _ = (N : ℝ) ^ (τ + 2 * ε) * T₀ := by
        rw [hX, ← mul_assoc, ← Real.rpow_add hx0]
        ring_nf
    _ ≤ 4 * ((N : ℝ) ^ (τ + 2 * ε) * T₀) := by linarith

/-- Lemma 5.2 [lemma_localized_eigenvector_local_law], (5.9)
[estimate_localized_eigenvector_local_law]: under (2.8) [eq:condA2] and `2k ≤ DN + 1`, for
every sufficiently small `ε > 0` in `η = N^{-2/3+ε} 𝔯(k)^{-1/3}` and every `τ > 0`, the
expectation `E⟨Im G₀ Λ̃ Im G₁ Λ̃⟩` is finite, nonnegative and at most
`N^{τ + C₅ ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS` for `N ≥ N₀(τ, ε)`, with `C₅` independent of `ε`. -/
theorem localized_eigenvector_local_law (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA)
    (hεA : 0 < εA) (C : ℕ → ℝ) :
    ∃ C₅ : ℝ, 0 < C₅ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ τ : ℝ, 0 < τ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : EntryLaws C,
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        Integrable (evecLoop D N A k ε) (blockLaw D N L) ∧
        0 ≤ ∫ w, evecLoop D N A k ε w ∂(blockLaw D N L) ∧
        ∫ w, evecLoop D N A k ε w ∂(blockLaw D N L) ≤
          (N : ℝ) ^ (τ + C₅ * ε) *
            ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2) := by
  refine ⟨2, two_pos, min εA (1 / 3), lt_min hεA (by norm_num), fun ε hε hε₁ τ hτ => ?_⟩
  have hεA' : ε < εA := lt_of_lt_of_le hε₁ (min_le_left _ _)
  have hε3 : ε < 1 / 3 := lt_of_lt_of_le hε₁ (min_le_right _ _)
  obtain ⟨N₀, hN₀⟩ := LL_main D hD δA εA hδA hεA C ε hε hεA' hε3 τ hτ
  obtain ⟨c₀, K, -, -, N₁, hN₁⟩ :=
    loop_env_admissible D hD δA εA ε hδA hεA hε (by linarith) hε3.le
  refine ⟨max N₀ N₁, fun N hN L A hA k hk hkN hhs => ?_⟩
  have hz : ∀ s a, 0 < ((evecEnv D N A k ε s).z a).im := fun s a =>
    ((hN₁ N (le_of_max_le_right hN) A hA k hk hkN hhs _ (Or.inl ⟨s, rfl⟩)).2.2.1 a).2.1
  exact LL_assemble L (evecEnv D N A k ε) hz (evecLoop D N A k ε) (LL_evec_polar D N A k ε)
    (LL_evec_nonneg D N A k ε (hz _)) _
    (hN₀ N (le_of_max_le_left hN) _ (llClass_blockH D N C L) A hA k hk hkN hhs _ (Or.inl rfl))

/-- Lemma 5.4 [lemma_localized_eigenvalue_local_law], (5.23)
[estimate_localized_eigenvalue_local_law]: under (2.8) [eq:condA2] and `2k ≤ DN + 1`, for
every sufficiently small `ε > 0` and every `τ > 0`, uniformly in `t ∈ [0, 1]`, the expectation
`E⟨Im G_t Λ̂_t Im G_t Λ̂_t⟩` is finite, nonnegative and at most
`N^{τ + C₅ ε} N^{-5/3} 𝔯(k)^{2/3} ‖A‖²_HS` for `N ≥ N₀(τ, ε)`, with `C₅` independent of `ε`. -/
theorem localized_eigenvalue_local_law (D : ℕ) (hD : 2 ≤ D) (δA εA : ℝ) (hδA : 0 < δA)
    (hεA : 0 < εA) (C : ℕ → ℝ) :
    ∃ C₅ : ℝ, 0 < C₅ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ τ : ℝ, 0 < τ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : EntryLaws C,
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D * N + 1 →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        Integrable (evalLoop D N A k ε t) (blockLaw D N L) ∧
        0 ≤ ∫ w, evalLoop D N A k ε t w ∂(blockLaw D N L) ∧
        ∫ w, evalLoop D N A k ε t w ∂(blockLaw D N L) ≤
          (N : ℝ) ^ (τ + C₅ * ε) *
            ((N : ℝ) ^ (-(5 / 3 : ℝ)) * rk D N k ^ (2 / 3 : ℝ) * hsNorm A ^ 2) := by
  refine ⟨2, two_pos, min εA (1 / 3), lt_min hεA (by norm_num), fun ε hε hε₁ τ hτ => ?_⟩
  have hεA' : ε < εA := lt_of_lt_of_le hε₁ (min_le_left _ _)
  have hε3 : ε < 1 / 3 := lt_of_lt_of_le hε₁ (min_le_right _ _)
  obtain ⟨N₀, hN₀⟩ := LL_main D hD δA εA hδA hεA C ε hε hεA' hε3 τ hτ
  obtain ⟨c₀, K, -, -, N₁, hN₁⟩ :=
    loop_env_admissible D hD δA εA ε hδA hεA hε (by linarith) hε3.le
  refine ⟨max N₀ N₁, fun N hN L A hA k hk hkN hhs t ht => ?_⟩
  have hz : ∀ s a, 0 < ((evalEnv D N A k ε t s).z a).im := fun s a =>
    ((hN₁ N (le_of_max_le_right hN) A hA k hk hkN hhs _ (Or.inr ⟨t, ht, s, rfl⟩)).2.2.1 a).2.1
  exact LL_assemble L (evalEnv D N A k ε t) hz (evalLoop D N A k ε t)
    (LL_eval_polar D N A k ε t) (LL_eval_nonneg D N A k ε t (hz _)) _
    (hN₀ N (le_of_max_le_left hN) _ (llClass_blockH D N C L) A hA k hk hkN hhs _
      (Or.inr ⟨t, ht, rfl⟩))

end RBMTransitionEdge

end
