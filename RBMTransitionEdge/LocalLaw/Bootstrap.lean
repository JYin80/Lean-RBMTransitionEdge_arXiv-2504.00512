module

public import RBMTransitionEdge.LocalLaw.FluctNet
public import RBMTransitionEdge.LocalLaw.BootstrapDet
public import RBMTransitionEdge.LocalLaw.Uniform
public import RBMTransitionEdge.LocalLaw.Stability
public import RBMTransitionEdge.LocalLaw.DysonBounds
public import RBMTransitionEdge.Det.MhatSpec
public import RBMTransitionEdge.Det.EdgeStability
public import RBMTransitionEdge.Det.Density

@[expose] public section

/-!
# One step of the bootstrap

The bootstrap domain of one level of the continuity argument for Lemma 2.9 [lem_loc] and one step
of the bootstrap: from an a priori bound `|(G - M)_{st}| ≺ φ` to the bounds on the block traces,
the isotropic entries and the averages, through the fluctuation bounds, the self-consistent
equation for the block traces and its stability.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The bootstrap domain `{|E| ≤ τ⁻¹, ℓ_N ≤ η ≤ 2}` of one level of the continuity argument. -/
def bootDom (τ : ℝ) (ℓ : ℕ → ℝ) (N : ℕ) : Set ℂ :=
  {z | |z.re| ≤ τ⁻¹ ∧ ℓ N ≤ z.im ∧ z.im ≤ 2}

/-! ### Norms, traces and the interaction -/

/-- The normalized trace is subtractive. -/
private lemma Boot_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

/-- The normalized trace is cyclic: `⟨P Q⟩ = ⟨Q P⟩`. -/
private lemma Boot_ntr_comm {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P * Q) = ntr (Q * P) := by
  simp [ntr, Matrix.trace_mul_comm P Q]

/-- The normalized trace on an empty index type vanishes. -/
private lemma Boot_ntr_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (B : Matrix ι ι ℂ) :
    ntr B = 0 := by
  simp [ntr, Matrix.trace]

/-- The operator norm is nonnegative. -/
private lemma Boot_opNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    0 ≤ opNorm X := norm_nonneg _

/-- The operator norm is subadditive. -/
private lemma Boot_opNorm_add_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι ℂ) :
    opNorm (X + Y) ≤ opNorm X + opNorm Y := by
  unfold opNorm
  rw [map_add]
  exact norm_add_le _ _

/-- The operator norm of a difference. -/
private lemma Boot_opNorm_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι ℂ) :
    opNorm (X - Y) ≤ opNorm X + opNorm Y := by
  unfold opNorm
  rw [map_sub]
  exact norm_sub_le _ _

/-- The operator norm of a product of matrices with bounded norms. -/
private lemma Boot_opNorm_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ}
    {x y : ℝ} (hX : opNorm X ≤ x) (hY : opNorm Y ≤ y) : opNorm (X * Y) ≤ x * y :=
  (opNorm_mul_le X Y).trans
    (mul_le_mul hX hY (Boot_opNorm_nonneg Y) ((Boot_opNorm_nonneg X).trans hX))

/-- `|D⟨E_a W⟩| ≤ B` when the diagonal entries of `W` are at most `B` in modulus. -/
private lemma Boot_blk_le (D N : ℕ) (a : Fin D) (W : Matrix (Idx D N) (Idx D N) ℂ)
    (B : ℝ) (hB : 0 ≤ B) (h : ∀ p, ‖W p p‖ ≤ B) : ‖(D : ℂ) * ntr (Ea D N a * W)‖ ≤ B := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : IsEmpty (Idx D 0) := ⟨fun p => p.2.elim0⟩
    simp [Boot_ntr_of_isEmpty, hB]
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

/-- `|x_a| ≤ ‖W‖` for the block traces `x = blockTr W`, i.e. `|blockTr W|_∞ ≤ ‖W‖`. -/
private lemma Boot_blockTr_le (D N : ℕ) (W : Matrix (Idx D N) (Idx D N) ℂ) :
    ‖blockTr D N W‖ ≤ opNorm W :=
  (pi_norm_le_iff_of_nonneg (Boot_opNorm_nonneg W)).mpr fun a =>
    Boot_blk_le D N a W _ (Boot_opNorm_nonneg W) (fun p => norm_apply_le_opNorm W p p)

/-- The block traces are additive. -/
private lemma Boot_blockTr_sub (D N : ℕ) (X Y : Matrix (Idx D N) (Idx D N) ℂ) :
    blockTr D N (X - Y) = blockTr D N X - blockTr D N Y := by
  funext a
  simp only [blockTr, Pi.sub_apply, Boot_ntr_sub, mul_sub]

/-- `|⟨M⟩| ≤ ‖M‖`. -/
private lemma Boot_ntr_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    ‖ntr M‖ ≤ opNorm M := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp [ntr, Matrix.trace, Boot_opNorm_nonneg]
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    unfold ntr Matrix.trace
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, M.diag i‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, opNorm M := by
          gcongr
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun i _ => norm_apply_le_opNorm M i i)
      _ = opNorm M := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

/-- `|x^* T y| ≤ ‖T‖` for `|x|, |y| ≤ 1`. -/
private lemma Boot_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
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

/-- `|v| = ‖v‖` in `EuclideanSpace ℂ (Fin D)`. -/
private lemma Boot_vnorm_eq {D : ℕ} (x : Fin D → ℂ) :
    vnorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin D))‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

private lemma Boot_vnorm_nonneg {D : ℕ} (x : Fin D → ℂ) : 0 ≤ vnorm x := Real.sqrt_nonneg _

/-- `|x - y| ≤ |x| + |y|`. -/
private lemma Boot_vnorm_sub {D : ℕ} (x y : Fin D → ℂ) :
    vnorm (x - y) ≤ vnorm x + vnorm y := by
  simp only [Boot_vnorm_eq, WithLp.toLp_sub]
  exact norm_sub_le _ _

/-- `|x + y| ≤ |x| + |y|`. -/
private lemma Boot_vnorm_add {D : ℕ} (x y : Fin D → ℂ) :
    vnorm (x + y) ≤ vnorm x + vnorm y := by
  simp only [Boot_vnorm_eq, WithLp.toLp_add]
  exact norm_add_le _ _

/-- `|c x| = |c| |x|`. -/
private lemma Boot_vnorm_smul {D : ℕ} (c : ℂ) (x : Fin D → ℂ) :
    vnorm (c • x) = ‖c‖ * vnorm x := by
  simp only [Boot_vnorm_eq, WithLp.toLp_smul]
  exact norm_smul _ _

/-- `|x|_∞ ≤ |x|`. -/
private lemma Boot_sup_le_vnorm {D : ℕ} (x : Fin D → ℂ) : ‖x‖ ≤ vnorm x := by
  refine (pi_norm_le_iff_of_nonneg (Boot_vnorm_nonneg x)).mpr fun a => ?_
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun b => ‖x b‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)

/-- `|x| ≤ √D |x|_∞`. -/
private lemma Boot_vnorm_le_sup {D : ℕ} (x : Fin D → ℂ) : vnorm x ≤ Real.sqrt D * ‖x‖ := by
  rw [vnorm, ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (Nat.cast_nonneg D)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ a, ‖x a‖ ^ 2 ≤ ∑ _a : Fin D, ‖x‖ ^ 2 :=
        Finset.sum_le_sum fun a _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x a) 2
    _ = D * ‖x‖ ^ 2 := by simp

/-- `|B v| ≤ ‖B‖ |v|`. -/
private lemma Boot_vnorm_mulVec {D : ℕ} (B : Matrix (Fin D) (Fin D) ℂ) (v : Fin D → ℂ) :
    vnorm (B *ᵥ v) ≤ opNorm B * vnorm v := by
  rw [Boot_vnorm_eq, Boot_vnorm_eq]
  have h : (WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin D)) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) B (WithLp.toLp 2 v) := rfl
  rw [h]
  exact ContinuousLinearMap.le_opNorm _ _

section Boot_Lam

open scoped Matrix.Norms.L2Operator

/-- The embedding `J_a` of `ℂ^N` as the block `a` of `Idx D N`. -/
private def Boot_J (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Fin N) ℂ :=
  Matrix.of fun p i => if p = (a, i) then 1 else 0

/-- `J_a^* J_a = 1`. -/
private lemma Boot_J_conj_mul (D N : ℕ) (a : Fin D) :
    (Boot_J D N a)ᴴ * Boot_J D N a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Boot_J, Matrix.of_apply,
    Matrix.one_apply]
  have : ∀ p : Idx D N, star (if p = (a, i) then (1 : ℂ) else 0) * (if p = (a, j) then 1 else 0) =
      if p = (a, i) then (if i = j then 1 else 0) else 0 := by
    intro p
    by_cases h : p = (a, i)
    · subst h
      by_cases hij : i = j <;> simp [hij]
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `‖J_a‖ ≤ 1`. -/
private lemma Boot_J_norm (D N : ℕ) (hN : 1 ≤ N) (a : Fin D) :
    ‖Boot_J D N a‖ ≤ 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (Boot_J D N a)
  rw [Boot_J_conj_mul, norm_one] at h1
  have h0 : 0 ≤ ‖Boot_J D N a‖ := norm_nonneg _
  nlinarith

/-- `‖J_a M J_b^*‖ ≤ ‖M‖`. -/
private lemma Boot_block_norm (D N : ℕ) (hN : 1 ≤ N) (a b : Fin D)
    (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖Boot_J D N a * M * (Boot_J D N b)ᴴ‖ ≤ ‖M‖ := by
  have ha := Boot_J_norm D N hN a
  have hb := Boot_J_norm D N hN b
  calc ‖Boot_J D N a * M * (Boot_J D N b)ᴴ‖
      ≤ ‖Boot_J D N a * M‖ * ‖(Boot_J D N b)ᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Boot_J D N a‖ * ‖M‖) * ‖(Boot_J D N b)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
    _ = ‖M‖ := by ring

/-- The entries of the block embedding `J_a M J_b^*`. -/
private lemma Boot_block_apply (D N : ℕ) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ)
    (p q : Idx D N) :
    (Boot_J D N a * M * (Boot_J D N b)ᴴ) p q =
      if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = a <;> by_cases h2 : q1 = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Boot_J, Prod.ext_iff, h1, h2]

/-- `Λ` as the sum of the embedded blocks `A` and `A^*`. -/
private lemma Boot_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = ∑ a : Fin D, ∑ b : Fin D,
      ((if fwd D a b then Boot_J D N a * A * (Boot_J D N b)ᴴ else 0) +
        (if fwd D b a then Boot_J D N a * Aᴴ * (Boot_J D N b)ᴴ else 0)) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.add_apply]
  have e1 : ∀ a b : Fin D,
      (if fwd D a b then Boot_J D N a * A * (Boot_J D N b)ᴴ else 0) p q =
      if fwd D a b ∧ p.1 = a ∧ q.1 = b then A p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D a b <;> simp [h, Boot_block_apply]
  have e2 : ∀ a b : Fin D,
      (if fwd D b a then Boot_J D N a * Aᴴ * (Boot_J D N b)ᴴ else 0) p q =
      if fwd D b a ∧ p.1 = a ∧ q.1 = b then Aᴴ p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D b a <;> simp [h, Boot_block_apply]
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
private lemma Boot_opNorm_lam (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := by
  change ‖lam D N A‖ ≤ 2 * (D : ℝ) ^ 2 * ‖A‖
  rw [Boot_lam_eq]
  have hb : ∀ a b : Fin D,
      ‖(if fwd D a b then Boot_J D N a * A * (Boot_J D N b)ᴴ else 0) +
      (if fwd D b a then Boot_J D N a * Aᴴ * (Boot_J D N b)ᴴ else 0)‖ ≤
        2 * ‖A‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D a b then Boot_J D N a * A * (Boot_J D N b)ᴴ else 0)‖ ≤
        ‖A‖ := by
      split_ifs
      · exact Boot_block_norm D N hN a b A
      · simp
    have h2 : ‖(if fwd D b a then Boot_J D N a * Aᴴ * (Boot_J D N b)ᴴ else 0)‖ ≤
        ‖A‖ := by
      split_ifs
      · exact (Boot_block_norm D N hN a b Aᴴ).trans (by rw [Matrix.l2_opNorm_conjTranspose])
      · simp
    linarith
  calc ‖∑ a : Fin D, ∑ b : Fin D, _‖ ≤ ∑ a : Fin D, ‖∑ b : Fin D, _‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin D, ∑ b : Fin D, 2 * ‖A‖ := by
        refine Finset.sum_le_sum fun a _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb a b)
    _ = 2 * (D : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Boot_Lam

/-- `⟨Λ⟩ = 0`: the interaction `Λ = lam D N A` of (1.3) [matrix_H] has zero diagonal. -/
private lemma Boot_ntr_lam (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : ntr (lam D N A) = 0 := by
  have h : ∀ p : Idx D N, lam D N A p p = 0 := by
    intro p
    have hf : ¬ fwd D p.1 p.1 := by
      unfold fwd
      omega
    simp [lam, hf]
  simp [ntr, Matrix.trace, Matrix.diag, h]

/-- For `D = 1` the interaction vanishes. -/
private lemma Boot_lam_one (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : lam 1 N A = 0 := by
  ext p q
  simp [lam, fwd]

/-- `D⟨E_a M⟩ = m` for every block, for `D ≥ 1`, `N ≥ 1` and `z ∉ ℝ`: the block traces of
(2.17) [def_G0] are the solution of (2.16) [self_m]. -/
private lemma Boot_blockTr_M (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : z.im ≠ 0) :
    blockTr D N (MExt (lam D N A) z) = fun _ => mExt (lam D N A) z := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  funext a
  simp only [blockTr]
  rw [Boot_ntr_comm]
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

/-- `M(z) = MSol` on the upper half plane. -/
private lemma Boot_MExt_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : 0 < z.im) : mExt Λ z = mSol Λ z ∧ MExt Λ z = MSol Λ z := by
  have he1 : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  exact ⟨he1, by simp [MExt, MSol, he1]⟩

/-- `‖M‖ ≤ 5/4` and `|m| < 1` for `‖Λ‖ ≤ 1/10`, `Im z > 0` (from (A.19) [taylor_expansion_M]). -/
private lemma Boot_M_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) :
    opNorm (MExt Λ z) ≤ 5 / 4 ∧ ‖mExt Λ z‖ < 1 := by
  obtain ⟨e1, e2⟩ := Boot_MExt_eq Λ z hz
  obtain ⟨-, hm, hM⟩ := mSol_apriori Λ hΛ hℓ z hz
  refine ⟨?_, by rw [e1]; exact hm⟩
  rw [e2]
  refine hM.le.trans ?_
  have h0 := Boot_opNorm_nonneg Λ
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- `|m| ≥ 7/(8(Z + 1))` for `|z| ≤ Z`, `Im z > 0`, `‖Λ‖ ≤ 1/10`: from `⟨(Λ - z - m) M⟩ = 1`. -/
private lemma Boot_m_lower {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (Z : ℝ) (z : ℂ)
    (hzZ : ‖z‖ ≤ Z) (hz : 0 < z.im) : 7 / (8 * (Z + 1)) ≤ ‖mExt Λ z‖ := by
  obtain ⟨hm, hinv, -⟩ := MExt_spec Λ hΛ z hz.ne'
  obtain ⟨hMn, hm1⟩ := Boot_M_le Λ hΛ hℓ z hz
  set m := mExt Λ z
  set M := MExt Λ z
  have h1 : ntr (Λ * M) - (z + m) * m = 1 := by
    have := congrArg ntr hinv
    rw [Matrix.sub_mul, Boot_ntr_sub, Matrix.smul_mul, Matrix.one_mul] at this
    have e1 : ntr ((z + m) • M) = (z + m) * ntr M := by
      simp only [ntr, Matrix.trace_smul, smul_eq_mul]; ring
    have e2 : ntr (1 : Matrix ι ι ℂ) = 1 := by
      have hc : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp only [ntr, Matrix.trace_one]
      field_simp
    rw [e1, e2, ← hm] at this
    exact this
  have h2 : ‖ntr (Λ * M)‖ ≤ 1 / 10 * (5 / 4) :=
    (Boot_ntr_le _).trans (Boot_opNorm_mul_le hℓ hMn)
  have h3 : 7 / 8 ≤ ‖(z + m) * m‖ := by
    have : (z + m) * m = ntr (Λ * M) - 1 := by rw [← h1]; ring
    rw [this]
    have := norm_sub_norm_le (1 : ℂ) (ntr (Λ * M))
    rw [norm_one, norm_sub_rev] at this
    linarith
  have h4 : ‖z + m‖ ≤ Z + 1 := (norm_add_le _ _).trans (by linarith)
  have hZ : 0 < Z + 1 := by linarith [norm_nonneg z]
  rw [norm_mul] at h3
  rw [div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg m, norm_nonneg (z + m)]

/-- `N^{-δ} ≤ c` for large `N`. -/
private lemma Boot_rpow_neg_small {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) ^ (-δ) ≤ c := by
  have h := ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually
    (ge_mem_nhds hc)
  exact Filter.eventually_atTop.mp h

/-- `C ≤ N^ε` for large `N`. -/
private lemma Boot_rpow_large {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C ≤ (N : ℝ) ^ ε := by
  have h := ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop C)
  exact Filter.eventually_atTop.mp h

/-! ### Monotonicity of `Im m / η` along vertical lines -/

/-- `η ↦ Im m(E + iη)/η` does not increase on `η > 0`: by Definition 2.7 [defn_Mm] and (2.19)
[eq:density_rhoN], `Im m(E + iη)/η = ∫ ρ(x) ((x - E)² + η²)⁻¹ dx`. -/
private lemma Boot_imm_anti {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (E η η' : ℝ)
    (hη : 0 < η) (hηη : η ≤ η') :
    (mSol Λ ((E : ℂ) + (η' : ℂ) * Complex.I)).im / η' ≤
      (mSol Λ ((E : ℂ) + (η : ℂ) * Complex.I)).im / η := by
  obtain ⟨hρ0, hρc, hρi, -, hrep⟩ := rho_stieltjes Λ hΛ hℓ
  have hden : ∀ t : ℝ, 0 < t → ∀ x : ℝ, t ^ 2 ≤ (x - E) ^ 2 + t ^ 2 := fun t _ x => by
    nlinarith [sq_nonneg (x - E)]
  have hint2 : ∀ t : ℝ, 0 < t → Integrable (fun x : ℝ => rho Λ x / ((x - E) ^ 2 + t ^ 2)) := by
    intro t ht
    refine Integrable.mono' (hρi.div_const (t ^ 2)) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · refine Continuous.aestronglyMeasurable (hρc.div (by fun_prop) fun x => ?_)
      have := hden t ht x
      positivity
    · have h1 := hden t ht x
      have ht2 : 0 < t ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hρ0 x) (by positivity))]
      exact div_le_div_of_nonneg_left (hρ0 x) ht2 h1
  have key : ∀ t : ℝ, 0 < t → (mSol Λ ((E : ℂ) + (t : ℂ) * Complex.I)).im / t =
      ∫ x, rho Λ x / ((x - E) ^ 2 + t ^ 2) := by
    intro t ht
    have hz : 0 < ((E : ℂ) + (t : ℂ) * Complex.I).im := by simpa using ht
    rw [hrep _ hz]
    have hpt : ∀ x : ℝ, (x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro x h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hint : Integrable
        (fun x : ℝ => (rho Λ x : ℂ) / ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I))) := by
      refine Integrable.mono' (hρi.div_const t) ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (Continuous.div (Complex.continuous_ofReal.comp hρc) (by fun_prop)
          hpt).aestronglyMeasurable
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]
        have h1 : t ≤ ‖(x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I)‖ := by
          have him' : ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I)).im = -t := by simp
          have := Complex.abs_im_le_norm ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I))
          rwa [him', abs_neg, abs_of_pos ht] at this
        exact div_le_div_of_nonneg_left (hρ0 x) ht h1
    have him := integral_im hint
    simp only [RCLike.im_to_complex] at him
    rw [← him, ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hd : 0 < (x - E) ^ 2 + t ^ 2 := by positivity
    have hre : ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I)).re = x - E := by simp
    have him' : ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I)).im = -t := by simp
    have hns : Complex.normSq ((x : ℂ) - ((E : ℂ) + (t : ℂ) * Complex.I)) =
        (x - E) ^ 2 + t ^ 2 := by
      rw [Complex.normSq_apply, hre, him']; ring
    simp only
    rw [Complex.div_im, hns, hre, him']
    simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, zero_div, zero_sub]
    field_simp
  rw [key η' (lt_of_lt_of_le hη hηη), key η hη]
  refine integral_mono (hint2 η' (lt_of_lt_of_le hη hηη)) (hint2 η hη) fun x => ?_
  have h1 : (x - E) ^ 2 + η ^ 2 ≤ (x - E) ^ 2 + η' ^ 2 := by nlinarith
  have h2 : 0 < (x - E) ^ 2 + η ^ 2 := by positivity
  exact div_le_div_of_nonneg_left (hρ0 x) h2 h1

/-! ### The spectral inputs of the stability of the vector equation -/

/-- `(p + |q|)/2 ≤ |p + q|` for `p ≥ 0` and `Re q ≥ 0`. -/
private lemma Boot_norm_add_re (p : ℝ) (q : ℂ) (hp : 0 ≤ p) (hq : 0 ≤ q.re) :
    (p + ‖q‖) / 2 ≤ ‖(p : ℂ) + q‖ := by
  have e1 : ‖(p : ℂ) + q‖ ^ 2 = (p + q.re) ^ 2 + q.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have e2 : ‖q‖ ^ 2 = q.re ^ 2 + q.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h0 : 0 ≤ (p + ‖q‖) / 2 := by positivity
  rw [← pow_le_pow_iff_left₀ h0 (norm_nonneg _) two_ne_zero, e1]
  nlinarith [sq_nonneg (p - ‖q‖), norm_nonneg q]

/-- The spectral inputs for `D = 1`, where `Λ = 0`, `m = m_sc` and `M = m`: the single eigenvalue
`μ₀ = 1 - m²` of `1 - M̂ σ_θ` satisfies `√(κ+η)/(Z+1) ≤ |μ₀| ≤ (Z+2)√(κ+η)` for `|z| ≤ Z`,
by Definition 2.7 [defn_Mm] and (2.18) [eq:semidensity] (`E^± = ±2`). -/
private lemma Boot_stab_one (Z : ℝ) (hZ : 0 < Z) (N : ℕ) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (θ : ℝ) (z : ℂ) (hzn : ‖z‖ ≤ Z)
    (hz : 0 < z.im) :
    ∃ μ : Fin 1 → ℂ,
      (∀ l, (1 - Mhat (lam 1 N A) z z * sigTheta 1 θ) *ᵥ fourierVec 1 l =
        μ l • fourierVec 1 l) ∧
      (∀ l, Real.sqrt (kappa (lam 1 N A) z.re + z.im) / (Z + 1) ≤ ‖μ l‖) ∧
      (∀ l, ‖μ l‖ ≤ (Z + 2) * Real.sqrt (kappa (lam 1 N A) z.re + z.im)) := by
  have : Nonempty (Idx 1 N) := ⟨(0, ⟨0, hN⟩)⟩
  rw [Boot_lam_one]
  set Λ : Matrix (Idx 1 N) (Idx 1 N) ℂ := 0 with hΛdef
  have hΛ : Λ.IsHermitian := Matrix.isHermitian_zero
  obtain ⟨hm, hinv, -⟩ := MExt_spec Λ hΛ z hz.ne'
  set m := mExt Λ z with hmdef
  set M := MExt Λ z with hMdef
  set c : ℂ := -(z + m) with hcdef
  have hc : c • M = 1 := by
    rw [← hinv, hΛdef, hcdef, zero_sub, Matrix.neg_mul,
      Matrix.smul_mul (z + m) (1 : Matrix (Idx 1 N) (Idx 1 N) ℂ) M, Matrix.one_mul M, neg_smul]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    have := congrFun (congrFun hc (0, ⟨0, hN⟩)) (0, ⟨0, hN⟩)
    simp at this
  have hM1 : M = c⁻¹ • (1 : Matrix (Idx 1 N) (Idx 1 N) ℂ) := by
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hntr1 : ntr (1 : Matrix (Idx 1 N) (Idx 1 N) ℂ) = 1 := by
    have hcard : (Fintype.card (Idx 1 N) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [ntr, Matrix.trace_one]
    field_simp
  have hntrc : ntr M = c⁻¹ := by
    have e : ntr (c⁻¹ • (1 : Matrix (Idx 1 N) (Idx 1 N) ℂ)) =
        c⁻¹ * ntr (1 : Matrix (Idx 1 N) (Idx 1 N) ℂ) := by
      simp only [ntr, Matrix.trace_smul, smul_eq_mul]; ring
    rw [hM1, e, hntr1, mul_one]
  have hmc : m = c⁻¹ := hm.trans hntrc
  have hM : M = m • (1 : Matrix (Idx 1 N) (Idx 1 N) ℂ) := by rw [hM1, hmc]
  have hmz : m * (z + m) = -1 := by
    have h1 : m * c = 1 := by rw [hmc]; exact inv_mul_cancel₀ hc0
    rw [hcdef] at h1
    linear_combination -h1
  obtain ⟨-, hm1⟩ := Boot_M_le Λ hΛ (by rw [hΛdef]; unfold opNorm; simp) z hz
  have hE : Ea 1 N 0 = 1 := by
    ext p q
    have : p.1 = 0 := Subsingleton.elim _ _
    simp [Ea, Matrix.diagonal_apply, Matrix.one_apply, this]
  have hσ : sigTheta 1 θ 0 0 = 1 := by
    simp [sigTheta]
  have hMhat : Mhat Λ z z 0 0 = m ^ 2 := by
    simp only [Mhat, hE, Matrix.mul_one, Nat.cast_one, one_mul]
    rw [← hMdef, hM, smul_mul_smul_comm, Matrix.one_mul]
    simp only [ntr, Matrix.trace_smul, smul_eq_mul] at hntr1 ⊢
    rw [mul_left_comm, hntr1, mul_one, sq]
  have hL : ∀ v : Fin 1 → ℂ, (1 - Mhat Λ z z * sigTheta 1 θ) *ᵥ v = (1 - m ^ 2) • v := by
    intro v
    funext a
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hσ, hMhat]
  refine ⟨fun _ => 1 - m ^ 2, fun l => hL _, ?_⟩
  -- the edges of the semicircle law
  obtain ⟨-, -, hEp, hEm, -⟩ := rho_zero (ι := Idx 1 N)
  have hκ : kappa Λ z.re = min |2 - z.re| |z.re + 2| := by
    rw [kappa, hEp, hEm]
    congr 2
    ring
  set E := z.re
  set η := z.im
  set κ := kappa Λ E
  have hzE : z = (E : ℂ) + (η : ℂ) * Complex.I := (Complex.re_add_im z).symm
  set p := ‖z - 2‖
  set q := ‖z + 2‖
  have hp1 : |E - 2| ≤ p := by
    have := Complex.abs_re_le_norm (z - 2); simpa using this
  have hp2 : η ≤ p := by
    have := Complex.abs_im_le_norm (z - 2)
    have h2 : (z - 2).im = η := by simp [η]
    rw [h2, abs_of_pos hz] at this
    exact this
  have hq1 : |E + 2| ≤ q := by
    have := Complex.abs_re_le_norm (z + 2); simpa using this
  have hq2 : η ≤ q := by
    have := Complex.abs_im_le_norm (z + 2)
    have h2 : (z + 2).im = η := by simp [η]
    rw [h2, abs_of_pos hz] at this
    exact this
  have hp3 : p ≤ |E - 2| + η := by
    have := Complex.norm_le_abs_re_add_abs_im (z - 2)
    have h1 : (z - 2).re = E - 2 := by simp [E]
    have h2 : (z - 2).im = η := by simp [η]
    rw [h1, h2, abs_of_pos hz] at this
    exact this
  have hq3 : q ≤ |E + 2| + η := by
    have := Complex.norm_le_abs_re_add_abs_im (z + 2)
    have h1 : (z + 2).re = E + 2 := by simp [E]
    have h2 : (z + 2).im = η := by simp [η]
    rw [h1, h2, abs_of_pos hz] at this
    exact this
  have hpZ : p ≤ Z + 2 := (norm_sub_le _ _).trans (by simp; linarith)
  have hqZ : q ≤ Z + 2 := (norm_add_le _ _).trans (by simp; linarith)
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact le_min (abs_nonneg _) (abs_nonneg _)
  have hlow : κ + η ≤ p * q := by
    rw [hκ]
    have hs : 4 ≤ |E - 2| + |E + 2| := by
      have := abs_sub_abs_le_abs_sub (E + 2) (E - 2)
      have h4 : |(E + 2) - (E - 2)| = 4 := by norm_num [abs_of_pos]
      cases abs_cases (E - 2) <;> cases abs_cases (E + 2) <;> linarith
    have e2 : |2 - E| = |E - 2| := abs_sub_comm _ _
    rcases le_total |E - 2| |E + 2| with h | h
    · have : min |2 - E| |E + 2| = |E - 2| := by rw [e2]; exact min_eq_left h
      rw [this]
      have hq0 : 2 ≤ q := by linarith
      nlinarith [abs_nonneg (E - 2)]
    · have : min |2 - E| |E + 2| = |E + 2| := by rw [e2]; exact min_eq_right h
      rw [this]
      have hp0 : 2 ≤ p := by linarith
      nlinarith [abs_nonneg (E + 2)]
  have hup : p * q ≤ (Z + 2) * (κ + η) := by
    rw [hκ]
    have e2 : |2 - E| = |E - 2| := abs_sub_comm _ _
    have hp0 : 0 ≤ p := norm_nonneg _
    have hq0 : 0 ≤ q := norm_nonneg _
    rcases le_total |E - 2| |E + 2| with h | h
    · have : min |2 - E| |E + 2| = |E - 2| := by rw [e2]; exact min_eq_left h
      rw [this]
      nlinarith
    · have : min |2 - E| |E + 2| = |E + 2| := by rw [e2]; exact min_eq_right h
      rw [this]
      nlinarith
  -- `|1 - m²| = |m| |z + 2m|` and `|z + 2m|² = |z - 2| |z + 2|`
  have e1 : 1 - m ^ 2 = -(m * (z + 2 * m)) := by linear_combination hmz
  have e2 : (z + 2 * m) ^ 2 = (z - 2) * (z + 2) := by linear_combination 4 * hmz
  have hn2 : ‖z + 2 * m‖ ^ 2 = p * q := by
    rw [← norm_pow, e2, norm_mul]
  have hmlow : 1 / (Z + 1) ≤ ‖m‖ := by
    have h1 : ‖m‖ * ‖z + m‖ = 1 := by
      rw [← norm_mul, hmz, norm_neg, norm_one]
    have h2 : ‖z + m‖ ≤ Z + 1 := (norm_add_le _ _).trans (by linarith)
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg m]
  have hsq : ‖1 - m ^ 2‖ ^ 2 = ‖m‖ ^ 2 * (p * q) := by
    rw [e1, norm_neg, norm_mul, mul_pow, hn2]
  have hd2 : Real.sqrt (κ + η) ^ 2 = κ + η := Real.sq_sqrt (by linarith)
  have hd0 : 0 ≤ Real.sqrt (κ + η) := Real.sqrt_nonneg _
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have h0 : 0 ≤ Real.sqrt (κ + η) / (Z + 1) := by positivity
    rw [← pow_le_pow_iff_left₀ h0 (norm_nonneg _) two_ne_zero, hsq, div_pow, hd2]
    have hm2 : 1 / (Z + 1) ^ 2 ≤ ‖m‖ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hmlow 2
      rwa [div_pow, one_pow] at this
    calc (κ + η) / (Z + 1) ^ 2 = 1 / (Z + 1) ^ 2 * (κ + η) := by ring
      _ ≤ ‖m‖ ^ 2 * (p * q) := mul_le_mul hm2 hlow (by linarith) (sq_nonneg _)
  · have h0 : 0 ≤ (Z + 2) * Real.sqrt (κ + η) := by positivity
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero, hsq, mul_pow, hd2]
    have hm2 : ‖m‖ ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ (norm_nonneg m) hm1.le 2
      rwa [one_pow] at this
    have hpq0 : 0 ≤ p * q := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖m‖ ^ 2 * (p * q) ≤ 1 * ((Z + 2) * (κ + η)) :=
          mul_le_mul hm2 hup hpq0 zero_le_one
      _ ≤ (Z + 2) ^ 2 * (κ + η) := by nlinarith

/-- The spectral inputs for `D ≥ 2` on `{|z| ≤ τ_s⁻¹, η > 0}`, from (A.17) [eq:otherM2],
(A.18) [eq:akbk2], the stability of `1 - M̂` and its Fourier diagonalization ((3.1) [def_ML],
(A.25) [eq_lambdak]): the eigenvalues `μ_l = 1 - θ_l λ̂_l` of `1 - M̂ σ_θ` satisfy
`|μ_l| ≥ d/C_s`, `|μ_l| ≤ C_u (d + a)`, `|μ_0| ≤ C₁ d` and `|μ_l| ≥ c_B a` for `l ≠ 0`, with
`d = √(κ + η) ≤ d_max` and `a = (1 - θ) + θ ‖A‖²_HS / N`. -/
private lemma Boot_stab_two (D : ℕ) (hD : 2 ≤ D) (δA τs dmax : ℝ) (hδA : 0 < δA) (hτs : 0 < τs)
    (hdmax : 0 < dmax) :
    ∃ Cs Cu C₁ cB : ℝ, 0 < Cs ∧ 0 < Cu ∧ 0 < C₁ ∧ 0 < cB ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      opNorm (lam D N A) ≤ 1 / 10 →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ τs⁻¹ → 0 < z.im →
      Real.sqrt (kappa (lam D N A) z.re + z.im) ≤ dmax →
      ∃ μ : Fin D → ℂ,
        (∀ l, (1 - Mhat (lam D N A) z z * sigTheta D θ) *ᵥ fourierVec D l =
          μ l • fourierVec D l) ∧
        (∀ l, Real.sqrt (kappa (lam D N A) z.re + z.im) / Cs ≤ ‖μ l‖) ∧
        (∀ l, ‖μ l‖ ≤ Cu * (Real.sqrt (kappa (lam D N A) z.re + z.im) +
          (1 - θ + θ * (hsNorm A ^ 2 / N)))) ∧
        (∀ l : Fin D, (l : ℕ) = 0 →
          ‖μ l‖ ≤ C₁ * Real.sqrt (kappa (lam D N A) z.re + z.im)) ∧
        (∀ l : Fin D, (l : ℕ) ≠ 0 → cB * (1 - θ + θ * (hsNorm A ^ 2 / N)) ≤ ‖μ l‖) := by
  obtain ⟨Cst, hCst, Nst, hst⟩ := one_minus_Mhat_stability D hD δA τs hδA hτs
  obtain ⟨cnz, hcnz, Nnz, hnz⟩ := one_minus_Mhat_nonzero D hD δA τs hδA hτs
  obtain ⟨Com, hCom, Nom, hom⟩ := otherM2 D hD δA τs hδA hτs
  obtain ⟨Ced, hCed, hed⟩ := one_minus_M2_edge τs hτs
  refine ⟨Cst + 2 * dmax + 2 / cnz, 1 + Ced + 2 * Com, Ced, min 1 cnz / 2, by positivity,
    by positivity, hCed, by positivity, max (max Nst Nnz) (max Nom 1), ?_⟩
  intro N hN A hA hℓ θ hθ0 hθ1 z hzn hz hdm
  have hNst : Nst ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNnz : Nnz ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNom : Nom ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  have hΛ := lam_isHermitian D N A
  set Λ := lam D N A with hΛdef
  set d := Real.sqrt (kappa Λ z.re + z.im) with hddef
  set h := hsNorm A ^ 2 / N with hhdef
  set a := 1 - θ + θ * h with hadef
  have hκ0 : 0 ≤ kappa Λ z.re := le_min (abs_nonneg _) (abs_nonneg _)
  have hd : 0 < d := Real.sqrt_pos.mpr (by linarith)
  have hh : 0 ≤ h := by positivity
  have ha : 0 ≤ a := by rw [hadef]; nlinarith
  set lh : Fin D → ℂ := fun l => circEig (Mhat Λ z z) l with hlh
  obtain ⟨hom0, homl⟩ := hom N hNom A hA z hzn hz z (Or.inl rfl)
  obtain ⟨e1, e2⟩ := Boot_MExt_eq Λ z hz
  have hed' := hed (Idx D N) Λ hΛ hℓ (Boot_ntr_lam D N A) z hzn hz
  -- the mean mode
  have h0up : ∀ l : Fin D, (l : ℕ) = 0 → ‖1 - lh l‖ ≤ Ced * d := by
    intro l hl
    simp only [hlh]
    rw [hom0 l hl, e2]
    exact hed'
  have h0low : ∀ l : Fin D, (l : ℕ) = 0 → d / Cst ≤ ‖1 - lh l‖ := by
    intro l hl
    obtain ⟨hdet, hinv⟩ := hst N hNst A hA z hzn hz z (Or.inl rfl)
    set T := 1 - Mhat Λ z z with hT
    have heig : T *ᵥ fourierVec D l = (1 - lh l) • fourierVec D l := by
      have := stabOp_eigvec D hD N 1 A z z hz.ne' hz.ne' l
      have hs1 : sigTheta D 1 = 1 := by simp [sigTheta]
      rw [hs1, Matrix.mul_one] at this
      rw [this]
      simp only [hl, ↓reduceIte, one_mul]
      rfl
    have hu : fourierVec D l = (1 - lh l) • (T⁻¹ *ᵥ fourierVec D l) := by
      rw [← Matrix.mulVec_smul, ← heig, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
    have hv : 0 < vnorm (fourierVec D l) := by
      refine Real.sqrt_pos.mpr ?_
      have h0 : ‖fourierVec D l ⟨0, by omega⟩‖ ^ 2 ≤ ∑ a, ‖fourierVec D l a‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => ‖fourierVec D l b‖ ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ _)
      have h1 : 0 < ‖fourierVec D l ⟨0, by omega⟩‖ ^ 2 := by
        have : fourierVec D l ⟨0, by omega⟩ = ((Real.sqrt D)⁻¹ : ℂ) := by
          simp [fourierVec, hl]
        rw [this]
        have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
        have : ((Real.sqrt D)⁻¹ : ℂ) ≠ 0 := by
          have : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hDpos).ne'
          exact_mod_cast inv_ne_zero this
        positivity
      linarith
    have h2 : vnorm (fourierVec D l) ≤ ‖1 - lh l‖ * (Cst / d) * vnorm (fourierVec D l) := by
      calc vnorm (fourierVec D l) = ‖1 - lh l‖ * vnorm (T⁻¹ *ᵥ fourierVec D l) := by
            rw [← Boot_vnorm_smul, ← hu]
        _ ≤ ‖1 - lh l‖ * (opNorm T⁻¹ * vnorm (fourierVec D l)) :=
            mul_le_mul_of_nonneg_left (Boot_vnorm_mulVec _ _) (norm_nonneg _)
        _ ≤ ‖1 - lh l‖ * ((Cst / d) * vnorm (fourierVec D l)) := by
            gcongr
        _ = _ := by ring
    have h3 : 1 ≤ ‖1 - lh l‖ * (Cst / d) := by
      by_contra hc
      push Not at hc
      nlinarith
    rw [div_le_iff₀ hCst]
    rw [mul_div_assoc', le_div_iff₀ hd] at h3
    linarith
  -- the other modes
  have hw : ∀ l : Fin D, (l : ℕ) ≠ 0 →
      0 ≤ (1 - lh l).re ∧ cnz * (d + h) ≤ ‖1 - lh l‖ ∧
        ‖1 - lh l‖ ≤ Ced * d + 2 * Com * (d + h) := by
    intro l hl
    obtain ⟨hre, hle⟩ := homl l
    obtain ⟨hre0, hle0⟩ := homl ⟨0, by omega⟩
    set y := (mSol Λ z).im
    have hy : 0 < y := (mSol_spec Λ hΛ z hz).1
    have hd1 : y / (y + z.im) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    refine ⟨?_, hnz N hNnz A hA z hzn hz z (Or.inl rfl) l hl, ?_⟩
    · simp only [Complex.sub_re, Complex.ofReal_re] at hre
      simp only [Complex.sub_re, Complex.one_re, hlh]
      linarith
    · have e : 1 - lh l = (1 - lh ⟨0, by omega⟩) -
          ((((y / (y + z.im)) : ℝ) : ℂ) - lh ⟨0, by omega⟩) +
          ((((y / (y + z.im)) : ℝ) : ℂ) - lh l) := by ring
      rw [e]
      have h1 := h0up ⟨0, by omega⟩ rfl
      calc _ ≤ ‖1 - lh ⟨0, by omega⟩‖ + ‖(((y / (y + z.im)) : ℝ) : ℂ) - lh ⟨0, by omega⟩‖ +
            ‖(((y / (y + z.im)) : ℝ) : ℂ) - lh l‖ :=
            (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
        _ ≤ Ced * d + Com * (d + h) + Com * (d + h) := by gcongr
        _ = _ := by ring
  have hμ : ∀ l : Fin D, (l : ℕ) ≠ 0 →
      1 - (θ : ℂ) * lh l = ((1 - θ : ℝ) : ℂ) + (θ : ℂ) * (1 - lh l) := by
    intro l _; push_cast; ring
  have hμlow : ∀ l : Fin D, (l : ℕ) ≠ 0 →
      ((1 - θ) + θ * ‖1 - lh l‖) / 2 ≤ ‖1 - (θ : ℂ) * lh l‖ := by
    intro l hl
    rw [hμ l hl]
    have hre : 0 ≤ ((θ : ℂ) * (1 - lh l)).re := by
      rw [Complex.re_ofReal_mul]
      exact mul_nonneg hθ0 (hw l hl).1
    have := Boot_norm_add_re (1 - θ) ((θ : ℂ) * (1 - lh l)) (by linarith) hre
    rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ0] at this
  have hμup : ∀ l : Fin D, (l : ℕ) ≠ 0 →
      ‖1 - (θ : ℂ) * lh l‖ ≤ (1 - θ) + θ * ‖1 - lh l‖ := by
    intro l hl
    rw [hμ l hl]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hθ0, abs_of_nonneg (by linarith)]
  refine ⟨fun l => 1 - (if (l : ℕ) = 0 then 1 else (θ : ℂ)) * lh l,
    fun l => stabOp_eigvec D hD N θ A z z hz.ne' hz.ne' l, ?_, ?_, ?_, ?_⟩
  · intro l
    by_cases hl : (l : ℕ) = 0
    · simp only [hl, ite_true, one_mul]
      refine le_trans ?_ (h0low l hl)
      exact div_le_div_of_nonneg_left hd.le hCst (by linarith [hdmax, div_pos two_pos hcnz])
    · simp only [hl, ite_false]
      refine le_trans ?_ (hμlow l hl)
      have hCs : 0 < Cst + 2 * dmax + 2 / cnz := by positivity
      have h1 : 2 * d / (Cst + 2 * dmax + 2 / cnz) ≤ 1 := by
        rw [div_le_one hCs]
        have : 0 < 2 / cnz := by positivity
        linarith
      have h2 : 2 * d / (Cst + 2 * dmax + 2 / cnz) ≤ cnz * d := by
        rw [div_le_iff₀ hCs]
        have : cnz * d * (2 / cnz) = 2 * d := by field_simp
        nlinarith [mul_pos hcnz hd, hCst, hdmax]
      have h3 := (hw l hl).2.1
      have h4 : cnz * d ≤ ‖1 - lh l‖ := le_trans (by nlinarith) h3
      have : d / (Cst + 2 * dmax + 2 / cnz) = (2 * d / (Cst + 2 * dmax + 2 / cnz)) / 2 := by
        ring
      rw [this]
      gcongr
      nlinarith
  · intro l
    by_cases hl : (l : ℕ) = 0
    · simp only [hl, ite_true, one_mul]
      refine (h0up l hl).trans ?_
      nlinarith
    · simp only [hl, ite_false]
      refine (hμup l hl).trans ?_
      have h3 := (hw l hl).2.2
      have h5 : θ * ‖1 - lh l‖ ≤ Ced * d + 2 * Com * d + 2 * Com * (θ * h) := by
        calc θ * ‖1 - lh l‖ ≤ θ * (Ced * d + 2 * Com * (d + h)) :=
              mul_le_mul_of_nonneg_left h3 hθ0
          _ ≤ Ced * d + 2 * Com * d + 2 * Com * (θ * h) := by
              nlinarith [mul_nonneg (sub_nonneg.2 hθ1)
                (by positivity : (0 : ℝ) ≤ Ced * d + 2 * Com * d)]
      nlinarith
  · intro l hl
    simp only [hl, ite_true, one_mul]
    exact h0up l hl
  · intro l hl
    simp only [hl, ite_false]
    refine le_trans ?_ (hμlow l hl)
    have h3 := (hw l hl).2.1
    have h4 : θ * (cnz * h) ≤ θ * ‖1 - lh l‖ :=
      mul_le_mul_of_nonneg_left (le_trans (by nlinarith) h3) hθ0
    have hm1 : min 1 cnz ≤ 1 := min_le_left _ _
    have hm2 : min 1 cnz ≤ cnz := min_le_right _ _
    have hm0 : 0 < min 1 cnz := lt_min one_pos hcnz
    have : min 1 cnz * (1 - θ + θ * h) ≤ (1 - θ) + θ * (cnz * h) := by
      nlinarith [mul_nonneg hθ0 hh]
    rw [hadef] at *
    linarith

/-- The spectral inputs of the stability of the vector equation on `{|z| ≤ τ_s⁻¹, η > 0}` for all
`D ≥ 1`, as required by the deterministic dichotomy for the vector equation: eigenvalue bounds
for `1 - M̂ σ_θ` in the Fourier basis ((3.1) [def_ML], (A.25) [eq_lambdak]) in terms of
`d = √(κ + η) ≤ d_max` and `a = (1 - θ) + θ ‖A‖²_HS / N`, the bound `c_q ≤ |m³| ≤ 1`, and
`‖Λ‖ ≤ 1/10`. -/
private lemma Boot_stab_inputs (D : ℕ) (hD : 1 ≤ D) (δA τs : ℝ) (hδA : 0 < δA) (hτs : 0 < τs) :
    ∃ Cs Cu C₁ cB cq dmax : ℝ, 0 < Cs ∧ 0 < Cu ∧ 0 < C₁ ∧ 0 < cB ∧ 0 < cq ∧ 0 < dmax ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N ∧
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      opNorm (lam D N A) ≤ 1 / 10 ∧
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ τs⁻¹ → 0 < z.im →
        cq ≤ ‖mExt (lam D N A) z ^ 3‖ ∧ ‖mExt (lam D N A) z ^ 3‖ ≤ 1 ∧
        Real.sqrt (kappa (lam D N A) z.re + z.im) ≤ dmax ∧
        ∃ μ : Fin D → ℂ,
          (∀ l, (1 - Mhat (lam D N A) z z * sigTheta D θ) *ᵥ fourierVec D l =
            μ l • fourierVec D l) ∧
          (∀ l, Real.sqrt (kappa (lam D N A) z.re + z.im) / Cs ≤ ‖μ l‖) ∧
          (∀ l, ‖μ l‖ ≤ Cu * (Real.sqrt (kappa (lam D N A) z.re + z.im) +
            (1 - θ + θ * (hsNorm A ^ 2 / N)))) ∧
          (∀ l : Fin D, (l : ℕ) = 0 →
            ‖μ l‖ ≤ C₁ * Real.sqrt (kappa (lam D N A) z.re + z.im)) ∧
          (∀ l : Fin D, (l : ℕ) ≠ 0 → cB * (1 - θ + θ * (hsNorm A ^ 2 / N)) ≤ ‖μ l‖) := by
  obtain ⟨Cec, hCec, hec⟩ := edge_close_to_edge_sc
  set Z := τs⁻¹ with hZdef
  have hZ : 0 < Z := inv_pos.mpr hτs
  set dmax := Real.sqrt (2 + Cec / 10 + 2 * Z) with hdmaxdef
  have hdmax : 0 < dmax := Real.sqrt_pos.mpr (by positivity)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨Nl, hNl⟩ := Boot_rpow_neg_small hδA (show (0 : ℝ) < 1 / (20 * (D : ℝ) ^ 2) by positivity)
  -- the common facts
  have hcommon : ∀ N : ℕ, Nl ≤ N → 1 ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ,
      opNorm A ≤ (N : ℝ) ^ (-δA) → opNorm (lam D N A) ≤ 1 / 10 ∧
      ∀ z : ℂ, ‖z‖ ≤ Z → 0 < z.im →
        (7 / (8 * (Z + 1))) ^ 3 ≤ ‖mExt (lam D N A) z ^ 3‖ ∧ ‖mExt (lam D N A) z ^ 3‖ ≤ 1 ∧
        Real.sqrt (kappa (lam D N A) z.re + z.im) ≤ dmax := by
    intro N hN hN1 A hA
    have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
    have hΛ := lam_isHermitian D N A
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    have hℓ : opNorm (lam D N A) ≤ 1 / 10 := by
      refine (Boot_opNorm_lam D N hN1 A).trans ?_
      have h1 := (hA.trans (hNl N hN))
      calc 2 * (D : ℝ) ^ 2 * opNorm A ≤ 2 * (D : ℝ) ^ 2 * (1 / (20 * (D : ℝ) ^ 2)) := by gcongr
        _ = 1 / 10 := by field_simp; ring
    refine ⟨hℓ, fun z hzn hz => ⟨?_, ?_, ?_⟩⟩
    · rw [norm_pow]
      exact pow_le_pow_left₀ (by positivity) (Boot_m_lower _ hΛ hℓ Z z hzn hz) 3
    · rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (Boot_M_le _ hΛ hℓ z hz).2.le
    · have hE := hec (Idx D N) (lam D N A) hΛ hℓ
      have hκ : kappa (lam D N A) z.re ≤ |Eplus (lam D N A) - z.re| := min_le_left _ _
      have hre : |z.re| ≤ Z := (Complex.abs_re_le_norm z).trans hzn
      have him : z.im ≤ Z := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hzn)
      have hEp : |Eplus (lam D N A)| ≤ 2 + Cec / 10 := by
        have h1 : |2 - Eplus (lam D N A)| ≤ Cec * opNorm (lam D N A) := by
          linarith [abs_nonneg (2 + Eminus (lam D N A))]
        have h2 : Cec * opNorm (lam D N A) ≤ Cec / 10 := by nlinarith
        have h3 := abs_sub_abs_le_abs_sub (Eplus (lam D N A)) 2
        rw [abs_sub_comm] at h3
        norm_num at h3
        linarith
      have h4 : |Eplus (lam D N A) - z.re| ≤ |Eplus (lam D N A)| + |z.re| := abs_sub _ _
      exact Real.sqrt_le_sqrt (by linarith)
  rcases (show D = 1 ∨ 2 ≤ D by omega) with rfl | hD2
  · refine ⟨Z + 1, Z + 2, Z + 2, 1, (7 / (8 * (Z + 1))) ^ 3, dmax, by positivity, by positivity,
      by positivity, one_pos, by positivity, hdmax, max Nl 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
    refine ⟨hN1, fun A hA => ?_⟩
    obtain ⟨hℓ, hc⟩ := hcommon N ((le_max_left _ _).trans hN) hN1 A hA
    refine ⟨hℓ, fun θ hθ0 hθ1 z hzn hz => ?_⟩
    obtain ⟨hc1, hc2, hc3⟩ := hc z hzn hz
    obtain ⟨μ, h1, h2, h3⟩ := Boot_stab_one Z hZ N hN1 A θ z hzn hz
    have hκ0 : 0 ≤ kappa (lam 1 N A) z.re := le_min (abs_nonneg _) (abs_nonneg _)
    have ha : 0 ≤ 1 - θ + θ * (hsNorm A ^ 2 / N) := by
      have : 0 ≤ θ * (hsNorm A ^ 2 / N) := by positivity
      linarith
    refine ⟨hc1, hc2, hc3, μ, h1, h2, fun l => (h3 l).trans ?_, fun l _ => h3 l, ?_⟩
    · have := Real.sqrt_nonneg (kappa (lam 1 N A) z.re + z.im)
      nlinarith
    · intro l hl
      exact absurd (Subsingleton.elim l 0 ▸ rfl : (l : ℕ) = 0) hl
  · obtain ⟨Cs, Cu, C₁, cB, hCs, hCu, hC₁, hcB, N₂, hN₂⟩ :=
      Boot_stab_two D hD2 δA τs dmax hδA hτs hdmax
    refine ⟨Cs, Cu, C₁, cB, (7 / (8 * (Z + 1))) ^ 3, dmax, hCs, hCu, hC₁, hcB, by positivity,
      hdmax, max (max Nl 1) N₂, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
    refine ⟨hN1, fun A hA => ?_⟩
    obtain ⟨hℓ, hc⟩ := hcommon N ((le_max_left _ _).trans ((le_max_left _ _).trans hN)) hN1 A hA
    refine ⟨hℓ, fun θ hθ0 hθ1 z hzn hz => ?_⟩
    obtain ⟨hc1, hc2, hc3⟩ := hc z hzn hz
    exact ⟨hc1, hc2, hc3, hN₂ N ((le_max_right _ _).trans hN) A hA hℓ θ hθ0 hθ1 z hzn hz hc3⟩

/-! ### One point and one vertical line of the continuity argument -/

/-- One point of the continuity argument for the block traces `x = blockTr(G - M)`: if the
dichotomy for the vector equation holds at `z` with error `r̄` and cubic constant `5√D`, and
`1(‖R_x̃‖ ≤ 5/2) |⟨E_a R_x̃ H̲G⟩| ≤ ρ` for every block `a`, with `√D D ρ ≤ r̄` and `β ≤ 1/5`, then
`|x| ≤ 2β` forces `|x| ≤ β`. -/
private lemma Boot_point (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (rbar ρ β : ℝ) (hβ : β ≤ 1 / 5)
    (hdich : ∀ x : Fin D → ℂ, vnorm x ≤ 1 →
      vnorm ((1 - Mhat (lam D N A) z z * sigTheta D θ) *ᵥ x -
        quadForm (qTensor (lam D N A) z) (sigTheta D θ *ᵥ x)) ≤
          rbar + 5 * Real.sqrt D * vnorm x ^ 3 →
      vnorm x ≤ β ∨ 2 * β < vnorm x)
    (herr : ∀ a : Fin D,
      (if opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z))) ≤
          5 / 2 then
        ‖ntr (Ea D N a * resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) *
          hgUnder D N θ H (lam D N A) z)‖ else 0) ≤ ρ)
    (hρ : Real.sqrt D * (D * ρ) ≤ rbar)
    (hx : vnorm (blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)) ≤ 2 * β) :
    vnorm (blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)) ≤ β := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  set Λ := lam D N A with hΛdef
  set G := res (H + Λ) z with hGdef
  set M := MExt Λ z with hMdef
  set m := mExt Λ z with hmdef
  set x := blockTr D N (G - M) with hxdef
  have hxv : vnorm x ≤ 2 / 5 := by linarith
  have hxs : ‖x‖ ≤ 2 / 5 := (Boot_sup_le_vnorm x).trans hxv
  have hbM : blockTr D N M = fun _ => m := Boot_blockTr_M D N hD hN A z hz.ne'
  have hbG : blockTr D N G = fun a => m + x a := by
    funext a
    have := congrFun (Boot_blockTr_sub D N G M) a
    rw [← hxdef, hbM] at this
    simp only [Pi.sub_apply] at this
    rw [this]
    ring
  have hMn : opNorm M ≤ 5 / 4 := (Boot_M_le Λ hΛ hℓ z hz).1
  obtain ⟨hR, hRM, hT3⟩ := resX_taylor D N hD hN θ hθ0 hθ1 A z hz hMn x hxs
  set R := resX Λ z (sigTheta D θ *ᵥ fun a => m + x a) with hRdef
  have hRn : opNorm R ≤ 5 / 2 := by
    have e : R = (R - M) + M := by abel
    rw [e]
    refine (Boot_opNorm_add_le _ _).trans ?_
    nlinarith
  have hG : G = R - R * hgUnder D N θ H Λ z := by
    have := res_eq_resX_sub D N θ A H hH z hz (by rw [hbG]; exact hR)
    rw [hbG] at this
    exact this
  set err := blockTr D N (R * hgUnder D N θ H Λ z) with herrdef
  have herr' : ‖err‖ ≤ D * ρ := by
    have hρ0 : 0 ≤ ρ := by
      have h1 := herr ⟨0, hD⟩
      rw [hbG] at h1
      simp only [← hRdef, hRn, ite_true] at h1
      exact (norm_nonneg _).trans h1
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
    have h1 := herr a
    rw [hbG] at h1
    simp only [← hRdef, hRn, ite_true] at h1
    simp only [herrdef, blockTr, norm_mul, Complex.norm_natCast]
    rw [← Matrix.mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  have hxeq : x = blockTr D N R - (fun _ => m) - err := by
    have h1 : blockTr D N G = blockTr D N R - err := by
      conv_lhs => rw [hG]
      exact Boot_blockTr_sub D N R _
    funext a
    have := congrFun h1 a
    rw [hbG] at this
    simp only [Pi.sub_apply] at this ⊢
    linear_combination this
  have hid : (1 - Mhat Λ z z * sigTheta D θ) *ᵥ x - quadForm (qTensor Λ z) (sigTheta D θ *ᵥ x) =
      (blockTr D N R - (fun _ => m) - Mhat Λ z z *ᵥ (sigTheta D θ *ᵥ x) -
        quadForm (qTensor Λ z) (sigTheta D θ *ᵥ x)) - err := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    have key : ∀ y P Q : Fin D → ℂ, y = blockTr D N R - (fun _ => m) - err →
        y - P - Q = (blockTr D N R - (fun _ => m) - P - Q) - err := by
      intro y P Q hy
      rw [hy]
      abel
    exact key x _ _ hxeq
  have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hbound : vnorm ((1 - Mhat Λ z z * sigTheta D θ) *ᵥ x -
      quadForm (qTensor Λ z) (sigTheta D θ *ᵥ x)) ≤ rbar + 5 * Real.sqrt D * vnorm x ^ 3 := by
    rw [hid]
    refine (Boot_vnorm_sub _ _).trans ?_
    have h1 := Boot_vnorm_le_sup (blockTr D N R - (fun _ => m) - Mhat Λ z z *ᵥ
      (sigTheta D θ *ᵥ x) - quadForm (qTensor Λ z) (sigTheta D θ *ᵥ x))
    have h2 := Boot_vnorm_le_sup err
    have h3 : ‖x‖ ^ 3 ≤ vnorm x ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (Boot_sup_le_vnorm x) 3
    have h4 : Real.sqrt D * ‖err‖ ≤ Real.sqrt D * (D * ρ) := mul_le_mul_of_nonneg_left herr' hsD
    have h5 : Real.sqrt D * ‖blockTr D N R - (fun _ => m) - Mhat Λ z z *ᵥ (sigTheta D θ *ᵥ x) -
        quadForm (qTensor Λ z) (sigTheta D θ *ᵥ x)‖ ≤ Real.sqrt D * (5 * ‖x‖ ^ 3) :=
      mul_le_mul_of_nonneg_left hT3 hsD
    nlinarith
  rcases hdich x (by linarith) hbound with h | h
  · exact h
  · linarith

/-- The continuity step along a vertical line for nonnegative reals: if consecutive values move
by at most `s`, the bounds `β_g` do not decrease and dominate `s`, and `v_g ≤ 2 β_g` forces
`v_g ≤ β_g`, then `v_0 ≤ β_0` gives `v_g ≤ β_g` for all `g ≤ n`. -/
private lemma Boot_march (n : ℕ) (v β : ℕ → ℝ) (s : ℝ)
    (hstep : ∀ g < n, v (g + 1) ≤ v g + s) (hβ : ∀ g < n, β g ≤ β (g + 1))
    (hs : ∀ g < n, s ≤ β (g + 1)) (hdich : ∀ g ≤ n, v g ≤ 2 * β g → v g ≤ β g)
    (h0 : v 0 ≤ β 0) : ∀ g ≤ n, v g ≤ β g := by
  intro g
  induction g with
  | zero => intro _; exact h0
  | succ g ih =>
    intro hg
    have hg' : g < n := by omega
    have h1 := ih hg'.le
    exact hdich (g + 1) hg (by linarith [hstep g hg', hβ g hg', hs g hg'])

/-! ### Size of the good bound and of the control parameter -/

/-- A lower bound for the good bound: `min(K_L/d_max, K_B/√r̄₀) r̄ ≤ stabBound … r̄ d a` for
`0 < r̄ ≤ r̄₀`, `0 < d ≤ d_max` and `K_B ≤ K_A`. -/
private lemma Boot_stabBound_lower (cL K₁ KL KA KB r₀ dmax rbar d a : ℝ) (hKL : 0 < KL)
    (hKB : 0 < KB) (hBA : KB ≤ KA) (hr : 0 < rbar) (hr₀ : rbar ≤ r₀) (hd : 0 < d)
    (hdd : d ≤ dmax) :
    min (KL / dmax) (KB / Real.sqrt r₀) * rbar ≤ stabBound cL K₁ KL KA KB rbar d a := by
  have hr0 : 0 < r₀ := lt_of_lt_of_le hr hr₀
  have hsr : 0 < Real.sqrt r₀ := Real.sqrt_pos.mpr hr0
  have hdm : 0 < dmax := lt_of_lt_of_le hd hdd
  have hq : KB / Real.sqrt r₀ * rbar ≤ KB * Real.sqrt rbar := by
    have h1 : rbar ≤ Real.sqrt rbar * Real.sqrt r₀ := by
      calc rbar = Real.sqrt rbar * Real.sqrt rbar := (Real.mul_self_sqrt hr.le).symm
        _ ≤ Real.sqrt rbar * Real.sqrt r₀ :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr₀) (Real.sqrt_nonneg _)
    rw [div_mul_eq_mul_div, div_le_iff₀ hsr]
    nlinarith
  unfold stabBound
  split_ifs with h1 h2
  · calc min (KL / dmax) (KB / Real.sqrt r₀) * rbar ≤ KL / dmax * rbar :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le
      _ ≤ KL / d * rbar := by gcongr
      _ = KL * rbar / d := by ring
  · refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le) (hq.trans ?_)
    exact mul_le_mul_of_nonneg_right hBA (Real.sqrt_nonneg _)
  · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le) hq

/-- Upper bounds for the good bound at `r̄ = c r̄₁` with `c ≥ 1`: `stabBound … r̄ d a ≤ K_A √r̄`
and `stabBound … r̄ d a ≤ (K_L + K_A)(1 + √c_L + 1/√c_L) c min(r̄₁/d, √r̄₁)`, for
`K_L √c_L ≤ K_B ≤ K_A`. -/
private lemma Boot_stabBound_upper (cL K₁ KL KA KB c rbar₁ d a : ℝ) (hcL : 0 < cL) (hKL : 0 < KL)
    (hLB : KL * Real.sqrt cL ≤ KB) (hBA : KB ≤ KA) (hc : 1 ≤ c) (hr : 0 < rbar₁) (hd : 0 < d) :
    stabBound cL K₁ KL KA KB (c * rbar₁) d a ≤ KA * Real.sqrt (c * rbar₁) ∧
      stabBound cL K₁ KL KA KB (c * rbar₁) d a ≤
        (KL + KA) * (1 + Real.sqrt cL + (Real.sqrt cL)⁻¹) * c *
          min (rbar₁ / d) (Real.sqrt rbar₁) := by
  set r := c * rbar₁ with hrdef
  have hr0 : 0 < r := by positivity
  have hscL : 0 < Real.sqrt cL := Real.sqrt_pos.mpr hcL
  have hKB : 0 < KB := lt_of_lt_of_le (mul_pos hKL hscL) hLB
  have hKA : 0 < KA := lt_of_lt_of_le hKB hBA
  set Mc := 1 + Real.sqrt cL + (Real.sqrt cL)⁻¹ with hMc
  have hMc1 : 1 ≤ Mc := by have := inv_pos.mpr hscL; linarith
  have hMcs : Real.sqrt cL ≤ Mc := by have := inv_pos.mpr hscL; linarith
  have hMci : (Real.sqrt cL)⁻¹ ≤ Mc := by linarith
  have hsr : Real.sqrt r ≤ c * Real.sqrt rbar₁ := by
    rw [hrdef, Real.sqrt_mul (by linarith)]
    have : Real.sqrt c ≤ c := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  have hrd : r / d = c * (rbar₁ / d) := by rw [hrdef]; ring
  -- the two bounds `β ≤ K Mc r/d` and `β ≤ K Mc √r`
  have hlin_sq : r ≤ cL * d ^ 2 → r / d ≤ Real.sqrt cL * Real.sqrt r := by
    intro h
    have h1 : Real.sqrt r ≤ Real.sqrt cL * d := by
      rw [← Real.sqrt_sq hd.le, ← Real.sqrt_mul hcL.le]
      exact Real.sqrt_le_sqrt h
    rw [div_le_iff₀ hd]
    calc r = Real.sqrt r * Real.sqrt r := (Real.mul_self_sqrt hr0.le).symm
      _ ≤ Real.sqrt r * (Real.sqrt cL * d) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ = Real.sqrt cL * Real.sqrt r * d := by ring
  have hquad_sq : ¬ r ≤ cL * d ^ 2 → Real.sqrt r ≤ (Real.sqrt cL)⁻¹ * (r / d) := by
    intro h
    push Not at h
    have h1 : Real.sqrt cL * d ≤ Real.sqrt r := by
      rw [← Real.sqrt_sq hd.le, ← Real.sqrt_mul hcL.le]
      exact Real.sqrt_le_sqrt h.le
    rw [inv_mul_eq_div, le_div_iff₀ hscL, le_div_iff₀ hd]
    calc Real.sqrt r * Real.sqrt cL * d = Real.sqrt r * (Real.sqrt cL * d) := by ring
      _ ≤ Real.sqrt r * Real.sqrt r := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ = r := Real.mul_self_sqrt hr0.le
  have hA : stabBound cL K₁ KL KA KB r d a ≤ KA * Real.sqrt r := by
    unfold stabBound
    split_ifs with h1 h2
    · have := hlin_sq h1
      calc KL * r / d = KL * (r / d) := by ring
        _ ≤ KL * (Real.sqrt cL * Real.sqrt r) := mul_le_mul_of_nonneg_left this hKL.le
        _ = KL * Real.sqrt cL * Real.sqrt r := by ring
        _ ≤ KA * Real.sqrt r :=
          mul_le_mul_of_nonneg_right (hLB.trans hBA) (Real.sqrt_nonneg _)
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_right hBA (Real.sqrt_nonneg _)
  have hB1 : stabBound cL K₁ KL KA KB r d a ≤ (KL + KA) * Mc * (r / d) := by
    unfold stabBound
    have hrd0 : 0 ≤ r / d := by positivity
    split_ifs with h1 h2
    · rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by nlinarith) hrd0
    · have := hquad_sq h1
      calc KA * Real.sqrt r ≤ KA * ((Real.sqrt cL)⁻¹ * (r / d)) :=
            mul_le_mul_of_nonneg_left this hKA.le
        _ ≤ (KL + KA) * Mc * (r / d) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (by nlinarith [inv_pos.mpr hscL]) hrd0
    · have := hquad_sq h1
      calc KB * Real.sqrt r ≤ KB * ((Real.sqrt cL)⁻¹ * (r / d)) :=
            mul_le_mul_of_nonneg_left this hKB.le
        _ ≤ (KL + KA) * Mc * (r / d) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (by nlinarith [inv_pos.mpr hscL]) hrd0
  have hB2 : stabBound cL K₁ KL KA KB r d a ≤ (KL + KA) * Mc * Real.sqrt r :=
    hA.trans (mul_le_mul_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _))
  refine ⟨hA, ?_⟩
  have hK0 : 0 ≤ (KL + KA) * Mc := by positivity
  rw [mul_assoc, mul_min_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ c),
    mul_min_of_nonneg _ _ hK0]
  refine le_min ?_ ?_
  · rw [← hrd]; exact hB1
  · exact hB2.trans (mul_le_mul_of_nonneg_left hsr hK0)

/-- The size of `r̄ = (1 + φ)⁶ Ψ_φ²` in the bootstrap domain: with `u ≥ 1`, `Nη ≥ u⁸`,
`0 ≤ Im m ≤ 1` and `0 ≤ φ ≤ u`, `r̄ ≤ 384/u`. -/
private lemma Boot_rbar_le (t y φ u : ℝ) (hu : 1 ≤ u) (ht : u ^ 8 ≤ t) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (hφ0 : 0 ≤ φ) (hφu : φ ≤ u) :
    (1 + φ) ^ 6 * (Real.sqrt ((y + φ) / t) + 1 / t) ^ 2 ≤ 384 / u := by
  have hu0 : 0 < u := by linarith
  have hu7 : 1 ≤ u ^ 7 := one_le_pow₀ hu
  have hu8 : u ^ 8 = u * u ^ 7 := by ring
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have h1 : (y + φ) / t ≤ 2 / u ^ 7 := by
    rw [div_le_div_iff₀ ht0 (by positivity)]
    nlinarith
  have h2 : (1 / t) ^ 2 ≤ 1 / u ^ 7 := by
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    have h7 : u ^ 7 ≤ u ^ 8 := by rw [hu8]; nlinarith
    have ht1 : 1 ≤ t := le_trans (one_le_pow₀ hu) ht
    nlinarith
  have hs2 : Real.sqrt ((y + φ) / t) ^ 2 = (y + φ) / t := Real.sq_sqrt (by positivity)
  have h3 : (Real.sqrt ((y + φ) / t) + 1 / t) ^ 2 ≤ 6 / u ^ 7 := by
    have := sq_nonneg (Real.sqrt ((y + φ) / t) - 1 / t)
    have e : (6 : ℝ) / u ^ 7 = 2 * (2 / u ^ 7) + 2 * (1 / u ^ 7) := by ring
    rw [e]
    nlinarith
  have h4 : (1 + φ) ^ 6 ≤ (2 * u) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
  calc (1 + φ) ^ 6 * (Real.sqrt ((y + φ) / t) + 1 / t) ^ 2 ≤ (2 * u) ^ 6 * (6 / u ^ 7) :=
        mul_le_mul h4 h3 (sq_nonneg _) (by positivity)
    _ = 384 / u := by field_simp; ring

/-- The lower bound `r̄ ≥ 1/(4N²)` for `0 < η ≤ 2` and `φ ≥ 0`. -/
private lemma Boot_rbar_ge (N : ℕ) (hN : 1 ≤ N) (η y φ : ℝ) (hη : 0 < η) (hη2 : η ≤ 2)
    (hφ0 : 0 ≤ φ) :
    1 / (4 * (N : ℝ) ^ 2) ≤
      (1 + φ) ^ 6 * (Real.sqrt ((y + φ) / ((N : ℝ) * η)) + 1 / ((N : ℝ) * η)) ^ 2 := by
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 1 / (2 * (N : ℝ)) ≤ 1 / ((N : ℝ) * η) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have h2 : 1 / (2 * (N : ℝ)) ≤ Real.sqrt ((y + φ) / ((N : ℝ) * η)) + 1 / ((N : ℝ) * η) := by
    have := Real.sqrt_nonneg ((y + φ) / ((N : ℝ) * η))
    linarith
  have h3 : (1 / (2 * (N : ℝ))) ^ 2 ≤
      (Real.sqrt ((y + φ) / ((N : ℝ) * η)) + 1 / ((N : ℝ) * η)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  have h4 : (1 : ℝ) ≤ (1 + φ) ^ 6 := one_le_pow₀ (by linarith)
  have e : 1 / (4 * (N : ℝ) ^ 2) = (1 / (2 * (N : ℝ))) ^ 2 := by field_simp; ring
  rw [e]
  nlinarith [sq_nonneg (1 / (2 * (N : ℝ)))]

/-- `r̄ = (1 + φ)⁶ Ψ_φ²` does not decrease as `η` decreases along a vertical line and `φ` does not
decrease: for `0 < η₁ ≤ η₂` and `0 ≤ φ₂ ≤ φ₁`, `r̄(E + iη₂, φ₂) ≤ r̄(E + iη₁, φ₁)`. -/
private lemma Boot_rbar_mono {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (N : ℕ) (hN : 1 ≤ N)
    (E η₁ η₂ φ₁ φ₂ : ℝ) (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hφ₂ : 0 ≤ φ₂) (hφ : φ₂ ≤ φ₁) :
    (1 + φ₂) ^ 6 * psiPhi Λ N ((E : ℂ) + (η₂ : ℂ) * Complex.I) φ₂ ^ 2 ≤
      (1 + φ₁) ^ 6 * psiPhi Λ N ((E : ℂ) + (η₁ : ℂ) * Complex.I) φ₁ ^ 2 := by
  have hη₂ : 0 < η₂ := lt_of_lt_of_le hη₁ hη
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hz₁ : 0 < ((E : ℂ) + (η₁ : ℂ) * Complex.I).im := by simpa using hη₁
  have hz₂ : 0 < ((E : ℂ) + (η₂ : ℂ) * Complex.I).im := by simpa using hη₂
  have him := Boot_imm_anti Λ hΛ hℓ E η₁ η₂ hη₁ hη
  simp only [psiPhi, (Boot_MExt_eq Λ _ hz₁).1, (Boot_MExt_eq Λ _ hz₂).1]
  have e₁ : ((E : ℂ) + (η₁ : ℂ) * Complex.I).im = η₁ := by simp
  have e₂ : ((E : ℂ) + (η₂ : ℂ) * Complex.I).im = η₂ := by simp
  rw [e₁, e₂]
  set y₁ := (mSol Λ ((E : ℂ) + (η₁ : ℂ) * Complex.I)).im
  set y₂ := (mSol Λ ((E : ℂ) + (η₂ : ℂ) * Complex.I)).im
  have hy₂ : 0 < y₂ := (mSol_spec Λ hΛ _ hz₂).1
  have h1 : (y₂ + φ₂) / (N * η₂) ≤ (y₁ + φ₁) / (N * η₁) := by
    have ha : φ₂ / η₂ ≤ φ₁ / η₁ :=
      (div_le_div_of_nonneg_left hφ₂ hη₁ hη).trans (div_le_div_of_nonneg_right hφ hη₁.le)
    have e : ∀ y φ η : ℝ, 0 < η → (y + φ) / (N * η) = (y / η + φ / η) / N := by
      intro y φ η hη; field_simp
    rw [e y₂ φ₂ η₂ hη₂, e y₁ φ₁ η₁ hη₁]
    exact div_le_div_of_nonneg_right (by linarith) hN0.le
  have h2 : 1 / (N * η₂) ≤ 1 / (N * η₁) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have h3 : Real.sqrt ((y₂ + φ₂) / (N * η₂)) + 1 / (N * η₂) ≤
      Real.sqrt ((y₁ + φ₁) / (N * η₁)) + 1 / (N * η₁) :=
    add_le_add (Real.sqrt_le_sqrt h1) h2
  have h4 : (Real.sqrt ((y₂ + φ₂) / (N * η₂)) + 1 / (N * η₂)) ^ 2 ≤
      (Real.sqrt ((y₁ + φ₁) / (N * η₁)) + 1 / (N * η₁)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have h5 : (1 + φ₂) ^ 6 ≤ (1 + φ₁) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
  exact mul_le_mul h5 h4 (sq_nonneg _) (by positivity)

/-- `‖E_a‖ ≤ 1`. -/
private lemma Boot_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  have : opNorm (Ea D N a) = ‖fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0‖ := by
    unfold opNorm Ea
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  rw [this]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- The decomposition `G - M = (R_x̃ - M) - R_x̃ H̲G` of the bootstrap: for Hermitian `H`,
`Im z > 0`, `‖Λ‖ ≤ 1/10` and `|x|_∞ ≤ 2/5` for the block traces `x = blockTr(G - M)`, the matrix
`R_x̃`, `x̃ = σ_θ blockTr G`, satisfies `‖R_x̃‖ ≤ 5/2` and `‖R_x̃ - M‖ ≤ (25/8) |x|_∞`. -/
private lemma Boot_decomp (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (hx : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 2 / 5) :
    opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z))) ≤ 5 / 2 ∧
      opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) -
        MExt (lam D N A) z) ≤
          25 / 8 * ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ∧
      res (H + lam D N A) z - MExt (lam D N A) z =
        (resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) -
          MExt (lam D N A) z) -
          resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) *
            hgUnder D N θ H (lam D N A) z := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  set Λ := lam D N A with hΛdef
  set G := res (H + Λ) z with hGdef
  set M := MExt Λ z with hMdef
  set m := mExt Λ z with hmdef
  set x := blockTr D N (G - M) with hxdef
  have hbM : blockTr D N M = fun _ => m := Boot_blockTr_M D N hD hN A z hz.ne'
  have hbG : blockTr D N G = fun a => m + x a := by
    funext a
    have := congrFun (Boot_blockTr_sub D N G M) a
    rw [← hxdef, hbM] at this
    simp only [Pi.sub_apply] at this
    rw [this]
    ring
  have hMn : opNorm M ≤ 5 / 4 := (Boot_M_le Λ hΛ hℓ z hz).1
  obtain ⟨hR, hRM, -⟩ := resX_taylor D N hD hN θ hθ0 hθ1 A z hz hMn x hx
  rw [hbG]
  set R := resX Λ z (sigTheta D θ *ᵥ fun a => m + x a) with hRdef
  have hRn : opNorm R ≤ 5 / 2 := by
    have e : R = (R - M) + M := by abel
    rw [e]
    refine (Boot_opNorm_add_le _ _).trans ?_
    nlinarith [norm_nonneg x]
  have hG : G = R - R * hgUnder D N θ H Λ z := by
    have := res_eq_resX_sub D N θ A H hH z hz (by rw [hbG]; exact hR)
    rw [hbG] at this
    exact this
  refine ⟨hRn, hRM, ?_⟩
  conv_lhs => rw [hG]
  abel

/-- One vertical line of the continuity argument (deterministic): on the grid
`z_g = E + iη_g`, `g = 0, …, n`, from `η_0 = 2` down to `η_n`, with steps `≤ 2/N⁵`, `η_g ≥ N⁻¹`,
`φ_g ≥ 0` non-decreasing in `g`, `r̄_g = (1 + φ_g)⁶ Ψ_{φ_g}(z_g)²`, the dichotomy for the vector
equation at every grid point with error `c r̄_g`, the error bounds `ρ_g` of the block-trace
equation, and the bound `ρ_a` of `⟨E_b M H̲G⟩` at the top, the block traces `x = blockTr(G - M)`
satisfy `|x(z_n)| ≤ β_n = stabBound … (c r̄_n) √(κ + η_n) a`. -/
private lemma Boot_line (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (E : ℝ) (n : ℕ) (ηg : ℕ → ℝ)
    (hηg : ∀ g ≤ n, (N : ℝ)⁻¹ ≤ ηg g ∧ ηg g ≤ 2) (hηg0 : ηg 0 = 2)
    (hstepη : ∀ g < n, ηg (g + 1) ≤ ηg g ∧ ηg g - ηg (g + 1) ≤ 2 / (N : ℝ) ^ 5)
    (φv : ℕ → ℝ) (hφ0 : ∀ g ≤ n, 0 ≤ φv g) (hφmono : ∀ g < n, φv g ≤ φv (g + 1))
    (cL K₁ KL KA KB r₀ dmax a c ρa : ℝ) (ρ : ℕ → ℝ)
    (hcL : 0 < cL) (hK₁ : 0 < K₁) (hKL : 0 < KL) (hLB : KL * Real.sqrt cL ≤ KB)
    (hBA : KB ≤ KA) (hKr : KA * Real.sqrt r₀ ≤ 1 / 2) (hc : 1 ≤ c)
    (hd : ∀ g ≤ n, Real.sqrt (kappa (lam D N A) E + ηg g) ≤ dmax)
    (hsmall : ∀ g ≤ n, c * ((1 + φv g) ^ 6 *
      psiPhi (lam D N A) N ((E : ℂ) + (ηg g : ℂ) * Complex.I) (φv g) ^ 2) ≤ 4 / 25 * r₀)
    (hdich : ∀ g ≤ n, ∀ x : Fin D → ℂ, vnorm x ≤ 1 →
      vnorm ((1 - Mhat (lam D N A) ((E : ℂ) + (ηg g : ℂ) * Complex.I)
          ((E : ℂ) + (ηg g : ℂ) * Complex.I) * sigTheta D θ) *ᵥ x -
        quadForm (qTensor (lam D N A) ((E : ℂ) + (ηg g : ℂ) * Complex.I))
          (sigTheta D θ *ᵥ x)) ≤
        c * ((1 + φv g) ^ 6 *
          psiPhi (lam D N A) N ((E : ℂ) + (ηg g : ℂ) * Complex.I) (φv g) ^ 2) +
          5 * Real.sqrt D * vnorm x ^ 3 →
      vnorm x ≤ stabBound cL K₁ KL KA KB (c * ((1 + φv g) ^ 6 *
          psiPhi (lam D N A) N ((E : ℂ) + (ηg g : ℂ) * Complex.I) (φv g) ^ 2))
          (Real.sqrt (kappa (lam D N A) E + ηg g)) a ∨
        2 * stabBound cL K₁ KL KA KB (c * ((1 + φv g) ^ 6 *
          psiPhi (lam D N A) N ((E : ℂ) + (ηg g : ℂ) * Complex.I) (φv g) ^ 2))
          (Real.sqrt (kappa (lam D N A) E + ηg g)) a < vnorm x)
    (herr : ∀ g ≤ n, ∀ b : Fin D,
      (if opNorm (resX (lam D N A) ((E : ℂ) + (ηg g : ℂ) * Complex.I) (sigTheta D θ *ᵥ
          blockTr D N (res (H + lam D N A) ((E : ℂ) + (ηg g : ℂ) * Complex.I)))) ≤ 5 / 2 then
        ‖ntr (Ea D N b * resX (lam D N A) ((E : ℂ) + (ηg g : ℂ) * Complex.I) (sigTheta D θ *ᵥ
          blockTr D N (res (H + lam D N A) ((E : ℂ) + (ηg g : ℂ) * Complex.I))) *
          hgUnder D N θ H (lam D N A) ((E : ℂ) + (ηg g : ℂ) * Complex.I))‖ else 0) ≤ ρ g)
    (hρ : ∀ g ≤ n, Real.sqrt D * (D * ρ g) ≤ c * ((1 + φv g) ^ 6 *
      psiPhi (lam D N A) N ((E : ℂ) + (ηg g : ℂ) * Complex.I) (φv g) ^ 2))
    (htop : ∀ b : Fin D, ‖ntr (Ea D N b * MExt (lam D N A) ((E : ℂ) + (ηg 0 : ℂ) * Complex.I) *
      hgUnder D N θ H (lam D N A) ((E : ℂ) + (ηg 0 : ℂ) * Complex.I))‖ ≤ ρa)
    (hρa : Real.sqrt D * (4 / 3 * (D * ρa)) ≤
      min (KL / dmax) (KB / Real.sqrt r₀) * (c * ((1 + φv 0) ^ 6 *
        psiPhi (lam D N A) N ((E : ℂ) + (ηg 0 : ℂ) * Complex.I) (φv 0) ^ 2)))
    (hstepN : Real.sqrt D * (2 / (N : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 25 / 16 * (1 + N))) ≤
      min (KL / dmax) (KB / Real.sqrt r₀) * (1 / (4 * (N : ℝ) ^ 2))) :
    vnorm (blockTr D N (res (H + lam D N A) ((E : ℂ) + (ηg n : ℂ) * Complex.I) -
      MExt (lam D N A) ((E : ℂ) + (ηg n : ℂ) * Complex.I))) ≤
      stabBound cL K₁ KL KA KB (c * ((1 + φv n) ^ 6 *
          psiPhi (lam D N A) N ((E : ℂ) + (ηg n : ℂ) * Complex.I) (φv n) ^ 2))
        (Real.sqrt (kappa (lam D N A) E + ηg n)) a ∧
      stabBound cL K₁ KL KA KB (c * ((1 + φv n) ^ 6 *
          psiPhi (lam D N A) N ((E : ℂ) + (ηg n : ℂ) * Complex.I) (φv n) ^ 2))
        (Real.sqrt (kappa (lam D N A) E + ηg n)) a ≤ 1 / 5 := by
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hΛ := lam_isHermitian D N A
  have hHΛ : (H + lam D N A).IsHermitian := hH.add hΛ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set Λ := lam D N A with hΛdef
  set zg : ℕ → ℂ := fun g => (E : ℂ) + (ηg g : ℂ) * Complex.I with hzg
  have hzim : ∀ g, (zg g).im = ηg g := fun g => by simp [hzg]
  have hηpos : ∀ g ≤ n, 0 < ηg g := fun g hg => lt_of_lt_of_le (by positivity) (hηg g hg).1
  set rb : ℕ → ℝ := fun g => (1 + φv g) ^ 6 * psiPhi Λ N (zg g) (φv g) ^ 2 with hrb
  set dd : ℕ → ℝ := fun g => Real.sqrt (kappa Λ E + ηg g) with hdd
  set β : ℕ → ℝ := fun g => stabBound cL K₁ KL KA KB (c * rb g) (dd g) a with hβdef
  set cβ := min (KL / dmax) (KB / Real.sqrt r₀) with hcβ
  set v : ℕ → ℝ := fun g => vnorm (blockTr D N (res (H + Λ) (zg g) - MExt Λ (zg g))) with hv
  have hκ0 : 0 ≤ kappa Λ E := le_min (abs_nonneg _) (abs_nonneg _)
  have hdpos : ∀ g ≤ n, 0 < dd g := fun g hg => Real.sqrt_pos.mpr (by linarith [hηpos g hg])
  -- size of `r̄`
  have hrb_ge : ∀ g ≤ n, 1 / (4 * (N : ℝ) ^ 2) ≤ rb g := by
    intro g hg
    have hz : 0 < (zg g).im := by rw [hzim]; exact hηpos g hg
    have hy : 0 ≤ (mExt Λ (zg g)).im := by
      rw [(Boot_MExt_eq Λ _ hz).1]; exact (mSol_spec Λ hΛ _ hz).1.le
    have := Boot_rbar_ge N hN (ηg g) (mExt Λ (zg g)).im (φv g) (hηpos g hg) (hηg g hg).2 (hφ0 g hg)
    simp only [hrb, psiPhi, hzim]
    exact this
  have hrb_pos : ∀ g ≤ n, 0 < rb g := fun g hg =>
    lt_of_lt_of_le (by positivity) (hrb_ge g hg)
  have hr₀ : 0 < r₀ := by
    have h1 := hsmall 0 (Nat.zero_le _)
    have h2 : 0 < c * rb 0 := mul_pos (by linarith) (hrb_pos 0 (Nat.zero_le _))
    have h3 : 0 < 4 / 25 * r₀ := lt_of_lt_of_le h2 h1
    linarith
  have hdmax : 0 < dmax := lt_of_lt_of_le (hdpos 0 (Nat.zero_le _)) (hd 0 (Nat.zero_le _))
  have hscL : 0 < Real.sqrt cL := Real.sqrt_pos.mpr hcL
  have hKB : 0 < KB := lt_of_lt_of_le (mul_pos hKL hscL) hLB
  have hcβ0 : 0 < cβ := lt_min (by positivity) (by positivity)
  have hcr : ∀ g ≤ n, c * rb g ≤ r₀ := fun g hg => by
    have := hsmall g hg; linarith
  -- bounds on `β`
  have hβle : ∀ g ≤ n, β g ≤ 1 / 5 := by
    intro g hg
    have h1 := (Boot_stabBound_upper cL K₁ KL KA KB c (rb g) (dd g) a hcL hKL hLB hBA hc
      (hrb_pos g hg) (hdpos g hg)).1
    have h2 : Real.sqrt (c * rb g) ≤ 2 / 5 * Real.sqrt r₀ := by
      have : Real.sqrt (c * rb g) ≤ Real.sqrt (4 / 25 * r₀) := Real.sqrt_le_sqrt (hsmall g hg)
      rw [Real.sqrt_mul (show (0 : ℝ) ≤ 4 / 25 by norm_num) r₀] at this
      have e : Real.sqrt (4 / 25) = 2 / 5 := by
        rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num
      rwa [e] at this
    have hKA : 0 < KA := lt_of_lt_of_le hKB hBA
    calc β g ≤ KA * Real.sqrt (c * rb g) := h1
      _ ≤ KA * (2 / 5 * Real.sqrt r₀) := mul_le_mul_of_nonneg_left h2 hKA.le
      _ = 2 / 5 * (KA * Real.sqrt r₀) := by ring
      _ ≤ 1 / 5 := by linarith
  have hβlow : ∀ g ≤ n, cβ * (c * rb g) ≤ β g := fun g hg =>
    Boot_stabBound_lower cL K₁ KL KA KB r₀ dmax (c * rb g) (dd g) a hKL hKB hBA
      (mul_pos (by linarith) (hrb_pos g hg)) (hcr g hg) (hdpos g hg) (hd g hg)
  set s := cβ * (1 / (4 * (N : ℝ) ^ 2)) with hsdef
  refine ⟨Boot_march n v β s ?_ ?_ ?_ ?_ ?_ n le_rfl, hβle n le_rfl⟩
  · -- one grid step moves `x` by at most `s`
    intro g hg
    have hg1 : g + 1 ≤ n := hg
    have hz1 : 0 < (zg (g + 1)).im := by rw [hzim]; exact hηpos _ hg1
    have hz0 : 0 < (zg g).im := by rw [hzim]; exact hηpos _ hg.le
    obtain ⟨hη1, hη2⟩ := hstepη g hg
    have hΔ : ‖zg (g + 1) - zg g‖ = ηg g - ηg (g + 1) := by
      have e : zg (g + 1) - zg g = ((ηg (g + 1) - ηg g : ℝ) : ℂ) * Complex.I := by
        simp only [hzg]; push_cast; ring
      rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      ring
    have hGd := opNorm_res_sub_le (H + Λ) hHΛ (zg (g + 1)) (zg g) hz1 hz0
    have hMd := (MSol_lipschitz Λ hΛ hℓ (N : ℝ)⁻¹ (by positivity) (zg (g + 1)) (zg g)
      (by rw [hzim]; exact (hηg _ hg1).1) (by rw [hzim]; exact (hηg _ hg.le).1)).2
    rw [← (Boot_MExt_eq Λ _ hz1).2, ← (Boot_MExt_eq Λ _ hz0).2, inv_inv] at hMd
    rw [hΔ] at hGd hMd
    have hprod : (N : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤ (zg (g + 1)).im * (zg g).im := by
      rw [hzim, hzim]
      exact mul_le_mul (hηg _ hg1).1 (hηg _ hg.le).1 (by positivity) (hηpos _ hg1).le
    have hGd' : opNorm (res (H + Λ) (zg (g + 1)) - res (H + Λ) (zg g)) ≤
        (ηg g - ηg (g + 1)) * (N : ℝ) ^ 2 := by
      refine hGd.trans ?_
      rw [div_le_iff₀ (mul_pos hz1 hz0)]
      have hΔ0 : 0 ≤ ηg g - ηg (g + 1) := by linarith
      calc ηg g - ηg (g + 1) = (ηg g - ηg (g + 1)) * (N : ℝ) ^ 2 * ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) := by
            field_simp
        _ ≤ (ηg g - ηg (g + 1)) * (N : ℝ) ^ 2 * ((zg (g + 1)).im * (zg g).im) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
    have hdiff : vnorm (blockTr D N (res (H + Λ) (zg (g + 1)) - MExt Λ (zg (g + 1))) -
        blockTr D N (res (H + Λ) (zg g) - MExt Λ (zg g))) ≤ s := by
      rw [← Boot_blockTr_sub]
      refine (Boot_vnorm_le_sup _).trans ?_
      have e : res (H + Λ) (zg (g + 1)) - MExt Λ (zg (g + 1)) - (res (H + Λ) (zg g) - MExt Λ (zg g)) =
          (res (H + Λ) (zg (g + 1)) - res (H + Λ) (zg g)) -
            (MExt Λ (zg (g + 1)) - MExt Λ (zg g)) := by abel
      have h1 := Boot_blockTr_le D N
        (res (H + Λ) (zg (g + 1)) - MExt Λ (zg (g + 1)) - (res (H + Λ) (zg g) - MExt Λ (zg g)))
      have h2 := Boot_opNorm_sub_le (res (H + Λ) (zg (g + 1)) - res (H + Λ) (zg g))
        (MExt Λ (zg (g + 1)) - MExt Λ (zg g))
      have hΔ0 : 0 ≤ ηg g - ηg (g + 1) := by linarith
      have h3 : opNorm (res (H + Λ) (zg (g + 1)) - res (H + Λ) (zg g)) +
          opNorm (MExt Λ (zg (g + 1)) - MExt Λ (zg g)) ≤
          2 / (N : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 25 / 16 * (1 + N)) := by
        have h4 : (ηg g - ηg (g + 1)) * (N : ℝ) ^ 2 + 25 / 16 * (1 + N) * (ηg g - ηg (g + 1)) ≤
            2 / (N : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 25 / 16 * (1 + N)) := by
          have : (ηg g - ηg (g + 1)) * ((N : ℝ) ^ 2 + 25 / 16 * (1 + N)) ≤
              2 / (N : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 25 / 16 * (1 + N)) :=
            mul_le_mul_of_nonneg_right hη2 (by positivity)
          linarith
        linarith
      have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
      calc Real.sqrt D * ‖blockTr D N (res (H + Λ) (zg (g + 1)) - MExt Λ (zg (g + 1)) -
            (res (H + Λ) (zg g) - MExt Λ (zg g)))‖
          ≤ Real.sqrt D * (2 / (N : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 25 / 16 * (1 + N))) :=
            mul_le_mul_of_nonneg_left (h1.trans (by rw [e]; exact h2.trans h3)) hsD
        _ ≤ s := hstepN
    have := Boot_vnorm_add (blockTr D N (res (H + Λ) (zg g) - MExt Λ (zg g)))
      (blockTr D N (res (H + Λ) (zg (g + 1)) - MExt Λ (zg (g + 1))) -
        blockTr D N (res (H + Λ) (zg g) - MExt Λ (zg g)))
    rw [add_sub_cancel] at this
    simp only [hv]
    linarith
  · -- the good bounds do not decrease along the line
    intro g hg
    have hg1 : g + 1 ≤ n := hg
    obtain ⟨hη1, -⟩ := hstepη g hg
    have hrr : rb g ≤ rb (g + 1) :=
      Boot_rbar_mono Λ hΛ hℓ N hN E (ηg (g + 1)) (ηg g) (φv (g + 1)) (φv g) (hηpos _ hg1) hη1
        (hφ0 g hg.le) (hφmono g hg)
    exact stabBound_mono cL K₁ KL KA KB hcL hK₁ hKL hLB hBA (c * rb g) (c * rb (g + 1)) (dd g)
      (dd (g + 1)) a (mul_pos (by linarith) (hrb_pos g hg.le))
      (mul_le_mul_of_nonneg_left hrr (by linarith)) (hdpos _ hg1)
      (Real.sqrt_le_sqrt (by linarith))
  · -- the good bounds dominate one step
    intro g hg
    have hg1 : g + 1 ≤ n := hg
    refine le_trans ?_ (hβlow _ hg1)
    refine mul_le_mul_of_nonneg_left ?_ hcβ0.le
    have h1 := hrb_ge _ hg1
    have h2 : rb (g + 1) ≤ c * rb (g + 1) := le_mul_of_one_le_left (hrb_pos _ hg1).le hc
    linarith
  · -- the dichotomy at every grid point
    intro g hg hx
    have hz : 0 < (zg g).im := by rw [hzim]; exact hηpos g hg
    exact Boot_point D N hD hN θ hθ0 hθ1 A hℓ H hH (zg g) hz (c * rb g) (ρ g) (β g) (hβle g hg)
      (hdich g hg) (herr g hg) (hρ g hg) hx
  · -- the top of the line
    have hz : 2 ≤ (zg 0).im := by rw [hzim, hηg0]
    have hc0 := blockTr_contraction D N θ hθ0 hθ1 A H hH (zg 0) hz
    have hr : ‖rVec D N θ H Λ (zg 0)‖ ≤ D * ρa := by
      have hρa0 : 0 ≤ ρa := (norm_nonneg _).trans (htop ⟨0, hD⟩)
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun b => ?_
      simp only [rVec, norm_neg, norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (htop b) (Nat.cast_nonneg _)
    have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
    calc v 0 ≤ Real.sqrt D * ‖blockTr D N (res (H + Λ) (zg 0) - MExt Λ (zg 0))‖ :=
          Boot_vnorm_le_sup _
      _ ≤ Real.sqrt D * (4 / 3 * (D * ρa)) := by
          refine mul_le_mul_of_nonneg_left (hc0.trans ?_) hsD
          exact mul_le_mul_of_nonneg_left hr (by norm_num)
      _ ≤ cβ * (c * rb 0) := hρa
      _ ≤ β 0 := hβlow 0 (Nat.zero_le _)

/-- The union bound over `(N⁵ + 2) D` events: `(N⁵ + 2) D N^{-(D'+7)} ≤ N^{-D'}` for
`D ≤ N`, `N ≥ 2`. -/
private lemma Boot_card_bound (N D : ℕ) (hDN' : D ≤ N) (hN2' : 2 ≤ N) (D' : ℝ) :
    ((N : ℝ) ^ 5 + 2) * D * (N : ℝ) ^ (-(D' + 7)) ≤ (N : ℝ) ^ (-D') := by
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hN7 : ((N : ℝ) ^ 5 + 2) * D ≤ (N : ℝ) ^ 7 := by
    have hDN : (D : ℝ) ≤ N := by exact_mod_cast hDN'
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2'
    have h5 : (N : ℝ) ^ 5 + 2 ≤ (N : ℝ) ^ 6 := by
      have : (2 : ℝ) ≤ (N : ℝ) ^ 5 := le_trans hN2 (by
        calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (N : ℝ) ^ 5 := pow_le_pow_right₀ hNr1 (by norm_num))
      nlinarith [pow_pos hN0 5]
    calc ((N : ℝ) ^ 5 + 2) * D ≤ (N : ℝ) ^ 6 * N :=
          mul_le_mul h5 hDN (Nat.cast_nonneg _) (by positivity)
      _ = (N : ℝ) ^ 7 := by ring
  have e7 : (N : ℝ) ^ (-(7 : ℝ)) = ((N : ℝ) ^ 7)⁻¹ := by
    rw [Real.rpow_neg hN0.le, show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e : (N : ℝ) ^ (-(D' + 7)) = (N : ℝ) ^ (-D') * ((N : ℝ) ^ 7)⁻¹ := by
    rw [show -(D' + 7) = -D' + -(7 : ℝ) by ring, Real.rpow_add hN0, e7]
  rw [e]
  have hpos : 0 < (N : ℝ) ^ (-D') := Real.rpow_pos_of_pos hN0 _
  calc ((N : ℝ) ^ 5 + 2) * D * ((N : ℝ) ^ (-D') * ((N : ℝ) ^ 7)⁻¹)
      = (N : ℝ) ^ (-D') * (((N : ℝ) ^ 5 + 2) * D / (N : ℝ) ^ 7) := by ring
    _ ≤ (N : ℝ) ^ (-D') * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hpos.le
        rw [div_le_one (by positivity)]
        exact hN7
    _ = (N : ℝ) ^ (-D') := mul_one _

/-- One grid step against the good bound: `√D (2/N⁵)(N² + (25/16)(1 + N)) ≤ c_β/(4N²)` for
`N ≥ 40 √D / c_β`. -/
private lemma Boot_stepN (N : ℕ) (hN : 1 ≤ N) (D : ℕ) (cβ : ℝ) (hcβ0 : 0 < cβ)
    (hNst2 : 40 * Real.sqrt D / cβ ≤ N) :
    Real.sqrt D * (2 / (N : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 25 / 16 * (1 + N))) ≤
      cβ * (1 / (4 * (N : ℝ) ^ 2)) := by
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (N : ℝ) ^ 2 + 25 / 16 * (1 + N) ≤ 5 * (N : ℝ) ^ 2 := by nlinarith
  have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  calc Real.sqrt D * (2 / (N : ℝ) ^ 5 * ((N : ℝ) ^ 2 + 25 / 16 * (1 + N)))
      ≤ Real.sqrt D * (2 / (N : ℝ) ^ 5 * (5 * (N : ℝ) ^ 2)) := by gcongr
    _ = 10 * Real.sqrt D / (N : ℝ) ^ 3 := by field_simp; ring
    _ ≤ cβ * (1 / (4 * (N : ℝ) ^ 2)) := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hcβ0] at hNst2
        have : cβ * (1 / (4 * (N : ℝ) ^ 2)) * (N : ℝ) ^ 3 = cβ * N / 4 := by
          field_simp
        rw [this]
        linarith

/-! ### The block traces on one event -/

set_option maxHeartbeats 1600000 in
/-- The block traces in the bootstrap domain: under the hypotheses of the bootstrap step, with
the averaged fluctuation bounds `1(‖R_x̃‖ ≤ 5/2) |⟨B R_x̃ H̲G⟩| ≺ (1 + |z|)^{2K_n} r̄` and
`|⟨B H̲G⟩| ≺ (1 + |z|)^{2K_a} r̄` (`r̄ = (1 + φ)⁶ Ψ_φ²`) in sup form on
`Z_N = {z ∈ bootDom τ ℓ N, |z| ≤ N^{τ/K}}`, the block traces `x = blockTr(G - M)` of a Hermitian
array satisfy `|x|_∞ ≤ N^{τ''} min(r̄/d, √r̄)` and `|x|_∞ ≤ 1/5` outside an event of probability
`≤ N^{-D'}`, for `0 < τ'' ≤ τ/32`, uniformly in `z ∈ bootDom τ ℓ N`. -/
private lemma Boot_core (D : ℕ) (δA τ : ℝ) (C θ : ℕ → ℝ)
    (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ)
    (hseq : LLSeq D δA C θ μ A) (hτ : 0 < τ) (ℓ : ℕ → ℝ)
    (hℓ : ∀ N : ℕ, (N : ℝ) ^ (-1 + τ) ≤ ℓ N) (K Kn Ka : ℝ) (hK : 8 ≤ K) (hKn : 1 ≤ Kn)
    (hKa : 1 ≤ Ka) (φ : ℕ → ℂ → ℝ)
    (hφ : ∀ N, ∀ z ∈ bootDom τ ℓ N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ (τ / K))
    (hmono : ∀ (N : ℕ) (E η η' : ℝ), ((E : ℂ) + (η : ℂ) * Complex.I) ∈ bootDom τ ℓ N → η ≤ η' →
      η' ≤ 2 → φ N ((E : ℂ) + (η' : ℂ) * Complex.I) ≤ φ N ((E : ℂ) + (η : ℂ) * Complex.I))
    (Zf : ℕ → Set ℂ) (hZf : ∀ N z, z ∈ Zf N ↔ z ∈ bootDom τ ℓ N ∧ ‖z‖ ≤ (N : ℝ) ^ (τ / K))
    (ξn ζn ξa ζa : ∀ N, ({z // z ∈ Zf N} × {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1}) →
      (Idx D N → Idx D N → ℂ) → ℝ)
    (hξn : ∀ N w h, ξn N w h =
      if opNorm (resX (lam D N (A N)) w.1.1 (sigTheta D (θ N) *ᵥ
          blockTr D N (res (Matrix.of h + lam D N (A N)) w.1.1))) ≤ 5 / 2 then
        ‖ntr (w.2.1 * resX (lam D N (A N)) w.1.1 (sigTheta D (θ N) *ᵥ
          blockTr D N (res (Matrix.of h + lam D N (A N)) w.1.1)) *
            hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1)‖
      else 0)
    (hζn : ∀ N w h, ζn N w h = (1 + ‖w.1.1‖) ^ (2 * Kn) * (1 + φ N w.1.1) ^ 6 *
      psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1) ^ 2)
    (hξa : ∀ N w h, ξa N w h =
      ‖ntr (w.2.1 * hgUnder D N (θ N) (Matrix.of h) (lam D N (A N)) w.1.1)‖)
    (hζa : ∀ N w h, ζa N w h = (1 + ‖w.1.1‖) ^ (2 * Ka) * (1 + φ N w.1.1) ^ 6 *
      psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1) ^ 2)
    (hnet : PrecS μ ξn ζn) (havg : PrecS μ ξa ζa) :
    ∀ τ'' : ℝ, 0 < τ'' → τ'' ≤ τ / 32 → ∀ D' : ℝ, 0 < D' → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ z ∈ bootDom τ ℓ N,
        μ N {h | (Matrix.of h).IsHermitian ∧
          ¬ (‖blockTr D N (res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z)‖ ≤
            (N : ℝ) ^ τ'' * min ((1 + φ N z) ^ 6 * psiPhi (lam D N (A N)) N z (φ N z) ^ 2 /
              Real.sqrt (kappa (lam D N (A N)) z.re + z.im))
              ((1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z)) ∧
            ‖blockTr D N (res (Matrix.of h + lam D N (A N)) z - MExt (lam D N (A N)) z)‖ ≤
              1 / 5)} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro τ'' hτ'' hτ''32 D' hD'
  have hD1 : 1 ≤ D := hseq.one_le_D
  have hδA : 0 < δA := hseq.pos
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  set ε₁ := τ'' / 2 with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  set Z := τ⁻¹ + 2 with hZdef
  have hZ : 0 < Z := by positivity
  have hτs : 0 < Z⁻¹ := inv_pos.mpr hZ
  obtain ⟨Cs, Cu, C₁, cB, cq, dmax, hCs, hCu, hC₁, hcB, hcq, hdmax, Ns, hstab⟩ :=
    Boot_stab_inputs D hD1 δA Z⁻¹ hδA hτs
  obtain ⟨cL, K₁, KL, KA, KB, r₀, ε₀, hcL, hK₁, hKL, hKA, hKB, hr₀, hε₀, hLB, hBA, hKr, hdS⟩ :=
    stab_dichotomy D hD1 Cs Cu C₁ cB cq (5 * Real.sqrt D) hCs hCu hC₁ hcB hcq (by positivity)
  set Cn := (1 + Z) ^ (2 * Kn) with hCn
  set Ca := (1 + Z) ^ (2 * Ka) with hCa
  have hCn0 : 0 < Cn := Real.rpow_pos_of_pos (by linarith) _
  have hCa0 : 0 < Ca := Real.rpow_pos_of_pos (by linarith) _
  set cβ := min (KL / dmax) (KB / Real.sqrt r₀) with hcβ
  have hcβ0 : 0 < cβ := lt_min (by positivity) (div_pos hKB (Real.sqrt_pos.mpr hr₀))
  set Cst := Real.sqrt D * D * Cn + 5 / 3 * Real.sqrt D * D * Ca / cβ + 1 with hCst
  have hCst1 : 1 ≤ Cst := by
    have h1 : 0 ≤ Real.sqrt D * D * Cn := by positivity
    have h2 : 0 ≤ 5 / 3 * Real.sqrt D * D * Ca / cβ := by positivity
    linarith
  set Cout := (KL + KA) * (1 + Real.sqrt cL + (Real.sqrt cL)⁻¹) * Cst with hCout
  -- the thresholds in `N`
  obtain ⟨Nn, hNn⟩ := hnet ε₁ hε₁0 (D' + 7) (by linarith)
  obtain ⟨Na, hNa⟩ := havg ε₁ hε₁0 (D' + 7) (by linarith)
  obtain ⟨NZ, hNZ⟩ := Boot_rpow_large (show 0 < τ / K by positivity) Z
  obtain ⟨Nε, hNε⟩ := Boot_rpow_neg_small hδA
    (show (0 : ℝ) < min 1 (ε₀ / (104 * (D : ℝ) ^ 4)) by positivity)
  obtain ⟨Nsm, hNsm⟩ := Boot_rpow_large (show 0 < τ / 16 by positivity) (2400 * Cst / r₀)
  obtain ⟨Nst, hNst⟩ := exists_nat_ge (40 * Real.sqrt D / cβ)
  obtain ⟨Nout, hNout⟩ := Boot_rpow_large hε₁0 Cout
  refine ⟨max (max (max Nn Na) (max Ns NZ)) (max (max Nε Nsm) (max (max Nst Nout) (D + 2))),
    fun N hN z hzB => ?_⟩
  have hNn' : Nn ≤ N := le_trans (by simp) hN
  have hNa' : Na ≤ N := le_trans (by simp) hN
  have hNs' : Ns ≤ N := le_trans (by simp) hN
  have hNZ' : NZ ≤ N := le_trans (by simp) hN
  have hNε' : Nε ≤ N := le_trans (by simp) hN
  have hNsm' : Nsm ≤ N := le_trans (by simp) hN
  have hNst' : Nst ≤ N := le_trans (by simp) hN
  have hNout' : Nout ≤ N := le_trans (by simp) hN
  have hND : D + 2 ≤ N := le_trans (by simp) hN
  obtain ⟨hN1, hstabN⟩ := hstab N hNs'
  obtain ⟨hℓΛ, hstabA⟩ := hstabN (A N) (hseq.small N)
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have : Nonempty (Idx D N) := ⟨(⟨0, hD1⟩, ⟨0, hN1⟩)⟩
  have hΛ := lam_isHermitian D N (A N)
  obtain ⟨hθ0, hθ1⟩ := hseq.theta N
  set Λ := lam D N (A N) with hΛdef
  -- the vertical line through `z`
  set E := z.re with hE
  set η := z.im with hη
  obtain ⟨hzE, hzℓ, hz2⟩ := hzB
  have hℓN : (N : ℝ)⁻¹ ≤ ℓ N := by
    refine le_trans ?_ (hℓ N)
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  have hηN : (N : ℝ)⁻¹ ≤ η := hℓN.trans hzℓ
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hηN
  set n : ℕ := N ^ 5 with hn
  have hnr : (n : ℝ) = (N : ℝ) ^ 5 := by rw [hn]; push_cast; ring
  have hn0 : (0 : ℝ) < n := by rw [hnr]; positivity
  set ηg : ℕ → ℝ := fun g => 2 - (g : ℝ) * (2 - η) / n with hηgdef
  have hηg0 : ηg 0 = 2 := by simp [hηgdef]
  have hηgn : ηg n = η := by simp only [hηgdef]; field_simp; ring
  have hηgr : ∀ g ≤ n, η ≤ ηg g ∧ ηg g ≤ 2 := by
    intro g hg
    have hg' : (g : ℝ) ≤ n := by exact_mod_cast hg
    have h1 : (g : ℝ) * (2 - η) / n ≤ 2 - η := by
      rw [div_le_iff₀ hn0, mul_comm (2 - η)]
      exact mul_le_mul_of_nonneg_right hg' (by linarith)
    have h2 : 0 ≤ (g : ℝ) * (2 - η) / n := by
      have : (0 : ℝ) ≤ g := Nat.cast_nonneg _
      have : 0 ≤ 2 - η := by linarith
      positivity
    simp only [hηgdef]
    constructor <;> linarith
  have hstepη : ∀ g < n, ηg (g + 1) ≤ ηg g ∧ ηg g - ηg (g + 1) ≤ 2 / (N : ℝ) ^ 5 := by
    intro g _
    have e : ηg g - ηg (g + 1) = (2 - η) / n := by simp only [hηgdef]; push_cast; ring
    have h1 : 0 ≤ (2 - η) / n := div_nonneg (by linarith) hn0.le
    refine ⟨by linarith, ?_⟩
    rw [e, hnr]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  set zg : ℕ → ℂ := fun g => (E : ℂ) + (ηg g : ℂ) * Complex.I with hzg
  have hzgre : ∀ g, (zg g).re = E := fun g => by simp [hzg]
  have hzgim : ∀ g, (zg g).im = ηg g := fun g => by simp [hzg]
  have hzgn : zg n = z := by
    simp only [hzg, hηgn, hE, hη]
    exact Complex.re_add_im z
  have hzgB : ∀ g ≤ n, zg g ∈ bootDom τ ℓ N := by
    intro g hg
    refine ⟨by rw [hzgre]; exact hzE, by rw [hzgim]; linarith [(hηgr g hg).1], by
      rw [hzgim]; exact (hηgr g hg).2⟩
  have hzgZ : ∀ g ≤ n, ‖zg g‖ ≤ Z := by
    intro g hg
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hzgre, hzgim, abs_of_pos (lt_of_lt_of_le hη0 (hηgr g hg).1)]
    linarith [(hηgr g hg).2]
  have hzgZf : ∀ g ≤ n, zg g ∈ Zf N := fun g hg =>
    (hZf N (zg g)).mpr ⟨hzgB g hg, (hzgZ g hg).trans (hNZ N hNZ')⟩
  have hzgpos : ∀ g ≤ n, 0 < (zg g).im := fun g hg => by
    rw [hzgim]; exact lt_of_lt_of_le hη0 (hηgr g hg).1
  set φv : ℕ → ℝ := fun g => φ N (zg g) with hφv
  have hφ0 : ∀ g ≤ n, 0 ≤ φv g := fun g hg =>
    le_trans (by positivity) (hφ N (zg g) (hzgB g hg)).1
  have hy : ∀ g ≤ n, 0 ≤ (mExt Λ (zg g)).im ∧ (mExt Λ (zg g)).im ≤ 1 := by
    intro g hg
    have hz := hzgpos g hg
    refine ⟨by rw [(Boot_MExt_eq Λ _ hz).1]; exact (mSol_spec Λ hΛ _ hz).1.le, ?_⟩
    exact (Complex.im_le_norm _).trans (Boot_M_le Λ hΛ hℓΛ _ hz).2.le
  -- the event: the averaged bounds at the grid points and at the top
  have hBa : ∀ b : Fin D, opNorm ((4 / 5 : ℂ) • (Ea D N b * MExt Λ (zg 0))) ≤ 1 := by
    intro b
    have h1 : opNorm ((4 / 5 : ℂ) • (Ea D N b * MExt Λ (zg 0))) =
        4 / 5 * opNorm (Ea D N b * MExt Λ (zg 0)) := by
      unfold opNorm
      rw [map_smul, norm_smul]
      norm_num
    have h2 := Boot_opNorm_mul_le (Boot_opNorm_Ea D N b)
      (Boot_M_le Λ hΛ hℓΛ _ (hzgpos 0 (Nat.zero_le _))).1
    rw [h1]
    linarith
  set wn : Fin (n + 1) → Fin D →
      ({z // z ∈ Zf N} × {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1}) :=
    fun g b => (⟨zg g, hzgZf g (Nat.lt_succ_iff.mp g.2)⟩, ⟨Ea D N b, Boot_opNorm_Ea D N b⟩)
    with hwn
  set wa : Fin D → ({z // z ∈ Zf N} × {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1}) :=
    fun b => (⟨zg 0, hzgZf 0 (Nat.zero_le _)⟩, ⟨(4 / 5 : ℂ) • (Ea D N b * MExt Λ (zg 0)), hBa b⟩)
    with hwa
  set S : Option (Fin (n + 1)) × Fin D → Set (Idx D N → Idx D N → ℂ) := fun p =>
    p.1.elim {ω | (N : ℝ) ^ ε₁ * ζa N (wa p.2) ω < ξa N (wa p.2) ω}
      (fun g => {ω | (N : ℝ) ^ ε₁ * ζn N (wn g p.2) ω < ξn N (wn g p.2) ω}) with hS
  have hSμ : ∀ p, μ N (S p) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D' + 7))) := by
    rintro ⟨_ | g, b⟩
    · exact hNa N hNa' (wa b)
    · exact hNn N hNn' (wn g b)
  have hbad : μ N (⋃ p, S p) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => hSμ p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcard : (Fintype.card (Option (Fin (n + 1)) × Fin D) : ℝ) = ((N : ℝ) ^ 5 + 2) * D := by
      simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
      push_cast
      rw [hnr]
      ring
    rw [hcard]
    exact Boot_card_bound N D (by omega) (by omega) D'
  refine le_trans (measure_mono ?_) hbad
  rintro h ⟨hH, hnot⟩
  by_contra hb
  apply hnot
  simp only [Set.mem_iUnion, not_exists] at hb
  set H := Matrix.of h with hHdef
  -- the bounds on the event
  set ρ : ℕ → ℝ := fun g => (N : ℝ) ^ ε₁ * ((1 + ‖zg g‖) ^ (2 * Kn) * (1 + φv g) ^ 6 *
    psiPhi Λ N (zg g) (φv g) ^ 2) with hρdef
  set ρa := 5 / 4 * ((N : ℝ) ^ ε₁ * ((1 + ‖zg 0‖) ^ (2 * Ka) * (1 + φv 0) ^ 6 *
    psiPhi Λ N (zg 0) (φv 0) ^ 2)) with hρadef
  have herr : ∀ g ≤ n, ∀ b : Fin D,
      (if opNorm (resX Λ (zg g) (sigTheta D (θ N) *ᵥ blockTr D N (res (H + Λ) (zg g)))) ≤
          5 / 2 then
        ‖ntr (Ea D N b * resX Λ (zg g) (sigTheta D (θ N) *ᵥ blockTr D N (res (H + Λ) (zg g))) *
          hgUnder D N (θ N) H Λ (zg g))‖ else 0) ≤ ρ g := by
    intro g hg b
    have h1 := hb (some ⟨g, Nat.lt_succ_of_le hg⟩, b)
    simp only [hS, Option.elim, Set.mem_ofPred_eq, not_lt] at h1
    rw [hξn, hζn] at h1
    exact h1
  have htop : ∀ b : Fin D, ‖ntr (Ea D N b * MExt Λ (zg 0) * hgUnder D N (θ N) H Λ (zg 0))‖ ≤ ρa := by
    intro b
    have h1 := hb (none, b)
    simp only [hS, Option.elim, Set.mem_ofPred_eq, not_lt] at h1
    rw [hξa, hζa] at h1
    have e : ntr ((4 / 5 : ℂ) • (Ea D N b * MExt Λ (zg 0)) * hgUnder D N (θ N) H Λ (zg 0)) =
        (4 / 5 : ℂ) * ntr (Ea D N b * MExt Λ (zg 0) * hgUnder D N (θ N) H Λ (zg 0)) := by
      rw [Matrix.smul_mul]
      simp only [ntr, Matrix.trace_smul, smul_eq_mul]
      ring
    change ‖ntr ((4 / 5 : ℂ) • (Ea D N b * MExt Λ (zg 0)) * hgUnder D N (θ N) H Λ (zg 0))‖ ≤ _
      at h1
    rw [e, norm_mul] at h1
    have h45 : ‖(4 / 5 : ℂ)‖ = 4 / 5 := by norm_num
    rw [h45] at h1
    rw [hρadef]
    linarith
  -- the constants of the line
  set c := Cst * (N : ℝ) ^ ε₁ with hcdef
  have hNε1 : 1 ≤ (N : ℝ) ^ ε₁ := Real.one_le_rpow hNr1 hε₁0.le
  have hc1 : 1 ≤ c := by rw [hcdef]; exact one_le_mul_of_one_le_of_one_le hCst1 hNε1
  set a := 1 - θ N + θ N * (hsNorm (A N) ^ 2 / N) with hadef
  have hzgn' : ∀ g ≤ n, ‖zg g‖ ≤ Z⁻¹⁻¹ := fun g hg => by rw [inv_inv]; exact hzgZ g hg
  have hεq : 26 * opNorm Λ ^ 2 ≤ ε₀ := by
    have h1 := Boot_opNorm_lam D N hN1 (A N)
    have h2 := (hseq.small N).trans (hNε N hNε')
    have hx0 : 0 ≤ opNorm (A N) := Boot_opNorm_nonneg _
    have hm1 : min 1 (ε₀ / (104 * (D : ℝ) ^ 4)) ≤ 1 := min_le_left _ _
    have hm2 : min 1 (ε₀ / (104 * (D : ℝ) ^ 4)) ≤ ε₀ / (104 * (D : ℝ) ^ 4) := min_le_right _ _
    set x := min 1 (ε₀ / (104 * (D : ℝ) ^ 4))
    have hΛx : opNorm Λ ≤ 2 * (D : ℝ) ^ 2 * x := h1.trans (by gcongr)
    have hΛ0 : 0 ≤ opNorm Λ := Boot_opNorm_nonneg _
    have hx00 : 0 ≤ x := hx0.trans h2
    calc 26 * opNorm Λ ^ 2 ≤ 26 * (2 * (D : ℝ) ^ 2 * x) ^ 2 := by gcongr
      _ = 104 * (D : ℝ) ^ 4 * x * x := by ring
      _ ≤ 104 * (D : ℝ) ^ 4 * (ε₀ / (104 * (D : ℝ) ^ 4)) * 1 := by gcongr
      _ = ε₀ := by field_simp
  -- the size of `r̄` on the line
  set u := (N : ℝ) ^ (τ / 16) with hudef
  have hu1 : 1 ≤ u := Real.one_le_rpow hNr1 (by positivity)
  have hu2 : (N : ℝ) ^ (τ / 8) = u ^ 2 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  have hu8 : (u ^ 2) ^ 8 = (N : ℝ) ^ τ := by
    rw [← hu2, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  have hNτ : ∀ g ≤ n, (N : ℝ) ^ τ ≤ N * (zg g).im := by
    intro g hg
    rw [hzgim]
    have h1 : (N : ℝ) ^ τ = N * (N : ℝ) ^ (-1 + τ) := by
      rw [show τ = 1 + (-1 + τ) by ring, Real.rpow_add hN0, Real.rpow_one]
      ring_nf
    rw [h1]
    exact mul_le_mul_of_nonneg_left ((hℓ N).trans (hzℓ.trans (hηgr g hg).1)) hN0.le
  have hφu : ∀ g ≤ n, φv g ≤ u ^ 2 := by
    intro g hg
    rw [← hu2]
    refine (hφ N (zg g) (hzgB g hg)).2.trans ?_
    exact Real.rpow_le_rpow_of_exponent_le hNr1
      (div_le_div_of_nonneg_left hτ.le (by norm_num) hK)
  have hrb : ∀ g ≤ n, (1 + φv g) ^ 6 * psiPhi Λ N (zg g) (φv g) ^ 2 ≤ 384 / u ^ 2 := by
    intro g hg
    simp only [psiPhi]
    exact Boot_rbar_le _ _ _ (u ^ 2) (one_le_pow₀ hu1) (by rw [hu8]; exact hNτ g hg)
      (hy g hg).1 (hy g hg).2 (hφ0 g hg) (hφu g hg)
  have hNεu : (N : ℝ) ^ ε₁ ≤ u :=
    Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  have hsmall : ∀ g ≤ n, c * ((1 + φv g) ^ 6 * psiPhi Λ N (zg g) (φv g) ^ 2) ≤ 4 / 25 * r₀ := by
    intro g hg
    have h1 := hrb g hg
    have h2 : 2400 * Cst / r₀ ≤ u := hNsm N hNsm'
    have hu0 : 0 < u := by linarith
    have hrb0 : 0 ≤ (1 + φv g) ^ 6 * psiPhi Λ N (zg g) (φv g) ^ 2 := by
      have : 0 ≤ 1 + φv g := by linarith [hφ0 g hg]
      positivity
    calc c * ((1 + φv g) ^ 6 * psiPhi Λ N (zg g) (φv g) ^ 2) ≤ Cst * u * (384 / u ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hNεu (by linarith)) h1 hrb0 (by positivity)
      _ = 384 * Cst / u := by field_simp
      _ ≤ 384 * Cst / (2400 * Cst / r₀) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h2
      _ = 4 / 25 * r₀ := by field_simp; ring
  -- the line
  obtain ⟨hv, hβ⟩ := Boot_line D N hD1 hN1 (θ N) hθ0 hθ1 (A N) hℓΛ H hH E n ηg
    (fun g hg => ⟨hηN.trans (hηgr g hg).1, (hηgr g hg).2⟩) hηg0 hstepη φv hφ0
    (fun g hg => hmono N E (ηg (g + 1)) (ηg g) (hzgB (g + 1) hg) (hstepη g hg).1
      (hηgr g hg.le).2)
    cL K₁ KL KA KB r₀ dmax a c ρa ρ hcL hK₁ hKL hLB hBA hKr hc1
    (fun g hg => by
      have := (hstabA (θ N) hθ0 hθ1 (zg g) (hzgn' g hg) (hzgpos g hg)).2.2.1
      rwa [hzgre, hzgim] at this)
    hsmall
    (fun g hg x hx1 hxb => by
      obtain ⟨hcq', hm3, -, μv, hμ1, hμ2, hμ3, hμ4, hμ5⟩ :=
        hstabA (θ N) hθ0 hθ1 (zg g) (hzgn' g hg) (hzgpos g hg)
      rw [hzgre, hzgim] at hμ2 hμ3 hμ4
      have hκ0 : 0 ≤ kappa Λ E := le_min (abs_nonneg _) (abs_nonneg _)
      have hd0 : 0 < Real.sqrt (kappa Λ E + ηg g) :=
        Real.sqrt_pos.mpr (by linarith [lt_of_lt_of_le hη0 (hηgr g hg).1])
      have hrbpos : 0 < c * ((1 + φv g) ^ 6 * psiPhi Λ N (zg g) (φv g) ^ 2) := by
        refine mul_pos (by linarith)
          (lt_of_lt_of_le (show (0 : ℝ) < 1 / (4 * (N : ℝ) ^ 2) by positivity) ?_)
        · have := Boot_rbar_ge N hN1 (ηg g) (mExt Λ (zg g)).im (φv g) (lt_of_lt_of_le hη0 (hηgr g hg).1)
            (hηgr g hg).2 (hφ0 g hg)
          simp only [psiPhi, hzgim]
          exact this
      exact hdS (θ N) hθ0 hθ1 _ μv hμ1 _ a hd0
        (by rw [hadef]; exact le_add_of_nonneg_right (mul_nonneg hθ0 (by positivity)))
        hμ2 hμ3 hμ4 hμ5 (qTensor Λ (zg g)) (mExt Λ (zg g) ^ 3) (26 * opNorm Λ ^ 2) hcq' hm3 hεq
        (fun a' b' c' => qTensor_sub_le D N hN1 (A N) hℓΛ (zg g) (hzgpos g hg) a' b' c')
        _ x hrbpos (by linarith [hsmall g hg]) hx1 hxb)
    herr
    (fun g hg => by
      have h1 : (1 + ‖zg g‖) ^ (2 * Kn) ≤ Cn :=
        Real.rpow_le_rpow (by positivity) (by linarith [hzgZ g hg]) (by linarith)
      have h0 : 0 ≤ (1 + φv g) ^ 6 * psiPhi Λ N (zg g) (φv g) ^ 2 := by
        have : 0 ≤ 1 + φv g := by linarith [hφ0 g hg]
        positivity
      have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
      have h2 : Real.sqrt D * D * Cn ≤ Cst := by
        have : 0 ≤ 5 / 3 * Real.sqrt D * D * Ca / cβ := by positivity
        linarith
      have e : Real.sqrt D * (D * ρ g) = Real.sqrt D * D * (1 + ‖zg g‖) ^ (2 * Kn) *
          ((N : ℝ) ^ ε₁ * ((1 + φv g) ^ 6 * psiPhi Λ N (zg g) (φv g) ^ 2)) := by
        simp only [hρdef]; ring
      rw [e, hcdef, mul_assoc Cst]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc Real.sqrt D * D * (1 + ‖zg g‖) ^ (2 * Kn) ≤ Real.sqrt D * D * Cn :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ Cst := h2)
    htop
    (by
      have h1 : (1 + ‖zg 0‖) ^ (2 * Ka) ≤ Ca :=
        Real.rpow_le_rpow (by positivity) (by linarith [hzgZ 0 (Nat.zero_le _)]) (by linarith)
      have h0 : 0 ≤ (1 + φv 0) ^ 6 * psiPhi Λ N (zg 0) (φv 0) ^ 2 := by
        have : 0 ≤ 1 + φv 0 := by linarith [hφ0 0 (Nat.zero_le _)]
        positivity
      have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
      have h2 : 5 / 3 * Real.sqrt D * D * Ca ≤ cβ * Cst := by
        have e1 : cβ * (5 / 3 * Real.sqrt D * D * Ca / cβ) = 5 / 3 * Real.sqrt D * D * Ca := by
          field_simp
        have h3 : 5 / 3 * Real.sqrt D * D * Ca / cβ ≤ Cst := by
          have : 0 ≤ Real.sqrt D * D * Cn := by positivity
          rw [hCst]; linarith
        calc 5 / 3 * Real.sqrt D * D * Ca = cβ * (5 / 3 * Real.sqrt D * D * Ca / cβ) := e1.symm
          _ ≤ cβ * Cst := mul_le_mul_of_nonneg_left h3 hcβ0.le
      have e : Real.sqrt D * (4 / 3 * (D * ρa)) = 5 / 3 * Real.sqrt D * D *
          (1 + ‖zg 0‖) ^ (2 * Ka) *
          ((N : ℝ) ^ ε₁ * ((1 + φv 0) ^ 6 * psiPhi Λ N (zg 0) (φv 0) ^ 2)) := by
        simp only [hρadef]; ring
      have h3 : 5 / 3 * Real.sqrt D * D * (1 + ‖zg 0‖) ^ (2 * Ka) ≤ cβ * Cst :=
        le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
      calc Real.sqrt D * (4 / 3 * (D * ρa)) = 5 / 3 * Real.sqrt D * D *
            (1 + ‖zg 0‖) ^ (2 * Ka) *
            ((N : ℝ) ^ ε₁ * ((1 + φv 0) ^ 6 * psiPhi Λ N (zg 0) (φv 0) ^ 2)) := e
        _ ≤ cβ * Cst * ((N : ℝ) ^ ε₁ * ((1 + φv 0) ^ 6 * psiPhi Λ N (zg 0) (φv 0) ^ 2)) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = cβ * (c * ((1 + φv 0) ^ 6 * psiPhi Λ N (zg 0) (φv 0) ^ 2)) := by
            rw [hcdef]; ring)
    (Boot_stepN N hN1 D cβ hcβ0 (le_trans hNst (by exact_mod_cast hNst')))
  -- the conclusion at `z = z_n`
  have hrn : (1 + φv n) ^ 6 * psiPhi Λ N (zg n) (φv n) ^ 2 =
      (1 + φ N z) ^ 6 * psiPhi Λ N z (φ N z) ^ 2 := by
    simp only [hφv, hzgn]
  have hxn : vnorm (blockTr D N (res (H + Λ) (zg n) - MExt Λ (zg n))) =
      vnorm (blockTr D N (res (H + Λ) z - MExt Λ z)) := by rw [hzgn]
  have hdn : Real.sqrt (kappa Λ E + ηg n) = Real.sqrt (kappa Λ z.re + z.im) := by rw [hηgn]
  change vnorm (blockTr D N (res (H + Λ) (zg n) - MExt Λ (zg n))) ≤ _ at hv
  rw [hxn, hrn, hdn] at hv
  rw [hrn, hdn] at hβ
  have hΨ0 : 0 ≤ psiPhi Λ N z (φ N z) := by
    unfold psiPhi
    have : 0 < z.im := hη0
    positivity
  have hφz : 0 ≤ φ N z := by rw [← hzgn]; exact hφ0 n le_rfl
  have hrz : 0 < (1 + φ N z) ^ 6 * psiPhi Λ N z (φ N z) ^ 2 := by
    rw [← hrn]
    refine lt_of_lt_of_le (show (0 : ℝ) < 1 / (4 * (N : ℝ) ^ 2) by positivity) ?_
    have := Boot_rbar_ge N hN1 (ηg n) (mExt Λ (zg n)).im (φv n) (lt_of_lt_of_le hη0 (hηgr n le_rfl).1)
      (hηgr n le_rfl).2 (hφ0 n le_rfl)
    simp only [psiPhi, hzgim]
    exact this
  have hκ0z : 0 ≤ kappa Λ z.re := le_min (abs_nonneg _) (abs_nonneg _)
  have hκz : 0 < Real.sqrt (kappa Λ z.re + z.im) := Real.sqrt_pos.mpr (by linarith)
  have hup := (Boot_stabBound_upper cL K₁ KL KA KB c _ _ a hcL hKL hLB hBA hc1 hrz hκz).2
  have hsq : Real.sqrt ((1 + φ N z) ^ 6 * psiPhi Λ N z (φ N z) ^ 2) =
      (1 + φ N z) ^ 3 * psiPhi Λ N z (φ N z) := by
    rw [show (1 + φ N z) ^ 6 * psiPhi Λ N z (φ N z) ^ 2 =
      ((1 + φ N z) ^ 3 * psiPhi Λ N z (φ N z)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq] at hup
  have hCout : (KL + KA) * (1 + Real.sqrt cL + (Real.sqrt cL)⁻¹) * c ≤ (N : ℝ) ^ τ'' := by
    have h1 : (N : ℝ) ^ τ'' = (N : ℝ) ^ ε₁ * (N : ℝ) ^ ε₁ := by
      rw [← Real.rpow_add hN0]; congr 1; rw [hε₁]; ring
    rw [h1, hcdef, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hNout N hNout') (by positivity)
  have hmin0 : 0 ≤ min ((1 + φ N z) ^ 6 * psiPhi Λ N z (φ N z) ^ 2 /
      Real.sqrt (kappa Λ z.re + z.im)) ((1 + φ N z) ^ 3 * psiPhi Λ N z (φ N z)) :=
    le_min (by positivity) (by positivity)
  have hxs := Boot_sup_le_vnorm (blockTr D N (res (H + Λ) z - MExt Λ z))
  refine ⟨?_, by linarith⟩
  calc ‖blockTr D N (res (H + Λ) z - MExt Λ z)‖ ≤ _ := hxs.trans (hv.trans hup)
    _ ≤ _ := mul_le_mul_of_nonneg_right hCout hmin0

/-- Two events of probability `≤ N^{-(D'+1)}`: `2 N^{-(D'+1)} ≤ N^{-D'}` for `N ≥ 2`. -/
private lemma Boot_two_le (N : ℕ) (hN : 2 ≤ N) (D' : ℝ) :
    ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D' + 1))) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [← ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (N : ℝ) ^ (-(D' + 1)) = (N : ℝ) ^ (-D') * (N : ℝ)⁻¹ := by
    rw [show -(D' + 1) = -D' + -(1 : ℝ) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
  rw [e]
  have hp : 0 < (N : ℝ) ^ (-D') := Real.rpow_pos_of_pos hN0 _
  have : (N : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hN0 (by norm_num)]; linarith
  nlinarith

/-- A point of `bootDom τ ℓ N` with `ℓ_N ≥ 0` has `|z| ≤ τ⁻¹ + 2` and `Im z ≥ ℓ_N`. -/
private lemma Boot_norm_le (τ : ℝ) (ℓ : ℕ → ℝ) (N : ℕ) (hℓ : 0 ≤ ℓ N) (z : ℂ)
    (hz : z ∈ bootDom τ ℓ N) : ‖z‖ ≤ τ⁻¹ + 2 := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  rw [abs_of_nonneg (hℓ.trans h2)]
  linarith

/-- The isotropic entries from the block traces (deterministic): if `|x|_∞ ≤ X`, `|x|_∞ ≤ 1/5`
and `1(‖R_x̃‖ ≤ 5/2) |u^* R_x̃ H̲G v| ≤ Y` for unit `u, v`, then `|u^* (G - M) v| ≤ (25/8) X + Y`. -/
private lemma Boot_iso_det (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (s t : Idx D N → ℂ) (hs : ∑ i, ‖s i‖ ^ 2 = 1) (ht : ∑ i, ‖t i‖ ^ 2 = 1) (X Y : ℝ)
    (hx : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ X)
    (hx5 : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 1 / 5)
    (hY : (if opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ
          blockTr D N (res (H + lam D N A) z))) ≤ 5 / 2 then
        ‖star s ⬝ᵥ ((resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) *
          hgUnder D N θ H (lam D N A) z) *ᵥ t)‖ else 0) ≤ Y) :
    ‖star s ⬝ᵥ ((res (H + lam D N A) z - MExt (lam D N A) z) *ᵥ t)‖ ≤ 25 / 8 * X + Y := by
  obtain ⟨hR, hRM, hdec⟩ := Boot_decomp D N hD hN θ hθ0 hθ1 A hℓ H hH z hz (by linarith)
  simp only [hR, ↓reduceIte] at hY
  rw [hdec, Matrix.sub_mulVec, dotProduct_sub]
  refine (norm_sub_le _ _).trans ?_
  have h1 := Boot_form_le (resX (lam D N A) z (sigTheta D θ *ᵥ
    blockTr D N (res (H + lam D N A) z)) - MExt (lam D N A) z) s t hs.le ht.le
  have h2 : 25 / 8 * ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 25 / 8 * X :=
    mul_le_mul_of_nonneg_left hx (by norm_num)
  linarith

/-- The averages from the block traces (deterministic): if `|x|_∞ ≤ X`, `|x|_∞ ≤ 1/5` and
`1(‖R_x̃‖ ≤ 5/2) |⟨B R_x̃ H̲G⟩| ≤ Y` for `‖B‖ ≤ 1`, then `|⟨(G - M) B⟩| ≤ (25/8) X + Y`. -/
private lemma Boot_avg_det (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (B : Matrix (Idx D N) (Idx D N) ℂ) (hB : opNorm B ≤ 1) (X Y : ℝ)
    (hx : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ X)
    (hx5 : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 1 / 5)
    (hY : (if opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ
          blockTr D N (res (H + lam D N A) z))) ≤ 5 / 2 then
        ‖ntr (B * resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) *
          hgUnder D N θ H (lam D N A) z)‖ else 0) ≤ Y) :
    ‖ntr ((res (H + lam D N A) z - MExt (lam D N A) z) * B)‖ ≤ 25 / 8 * X + Y := by
  obtain ⟨hR, hRM, hdec⟩ := Boot_decomp D N hD hN θ hθ0 hθ1 A hℓ H hH z hz (by linarith)
  simp only [hR, ↓reduceIte] at hY
  set R := resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z))
  set W := hgUnder D N θ H (lam D N A) z
  rw [hdec, Matrix.sub_mul, Boot_ntr_sub]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖ntr ((R - MExt (lam D N A) z) * B)‖ ≤
      25 / 8 * ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ :=
    (Boot_ntr_le _).trans ((Boot_opNorm_mul_le hRM hB).trans (by rw [mul_one]))
  have h2 : ntr (R * W * B) = ntr (B * R * W) := by
    rw [Boot_ntr_comm, Matrix.mul_assoc]
  have h3 : 25 / 8 * ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 25 / 8 * X :=
    mul_le_mul_of_nonneg_left hx (by norm_num)
  rw [h2]
  linarith

set_option maxHeartbeats 1000000 in
/-- One step of the bootstrap in the setting of Lemma 2.9 [lem_loc]: there is `K ≥ 8` such that,
for a sequence of members (`LLSeq`), `0 < τ ≤ 1/4`, a lower cut-off `ℓ_N ≥ N^{-1+τ}`, and an
a priori bound `|(G - M)_{st}| ≺ φ_N(z)` on `bootDom τ ℓ` with deterministic `N⁻¹ ≤ φ_N ≤ N^{τ/K}`
non-increasing in `η` along vertical lines, with `r̄ = (1 + φ)⁶ Ψ_φ²` and `d = √(κ + η)`:
the block traces `x_a = D⟨E_a (G - M)⟩` satisfy `|x|_∞ ≺ min(r̄/d, √r̄)`,
`|(G - M)_{uv}| ≺ (1 + φ)³ Ψ_φ`, and `|⟨(G - M) B⟩| ≺ r̄ + min(r̄/d, √r̄)` for deterministic
`‖B‖ ≤ 1`, all in sup form over `z ∈ bootDom τ ℓ`. -/
theorem bootstrap_stage : ∃ K : ℝ, 8 ≤ K ∧
    ∀ (D : ℕ) (δA τ : ℝ) (C : ℕ → ℝ) (θ : ℕ → ℝ)
      (μ : ∀ N, Measure (Idx D N → Idx D N → ℂ)) (A : ∀ N, Matrix (Fin N) (Fin N) ℂ),
      LLSeq D δA C θ μ A → 0 < τ → τ ≤ 1 / 4 →
    ∀ ℓ : ℕ → ℝ, (∀ N : ℕ, (N : ℝ) ^ (-1 + τ) ≤ ℓ N) →
    ∀ φ : ℕ → ℂ → ℝ,
      (∀ N, ∀ z ∈ bootDom τ ℓ N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ (τ / K)) →
      (∀ (N : ℕ) (E η η' : ℝ), ((E : ℂ) + (η : ℂ) * Complex.I) ∈ bootDom τ ℓ N → η ≤ η' →
        η' ≤ 2 → φ N ((E : ℂ) + (η' : ℂ) * Complex.I) ≤ φ N ((E : ℂ) + (η : ℂ) * Complex.I)) →
      aprioriLL D μ A (bootDom τ ℓ) φ →
    PrecS μ (U := fun N => {z // z ∈ bootDom τ ℓ N})
        (fun N w h => ‖blockTr D N (res (Matrix.of h + lam D N (A N)) w.1 -
          MExt (lam D N (A N)) w.1)‖)
        (fun N w _ => min ((1 + φ N w.1) ^ 6 * psiPhi (lam D N (A N)) N w.1 (φ N w.1) ^ 2 /
            Real.sqrt (kappa (lam D N (A N)) w.1.re + w.1.im))
          ((1 + φ N w.1) ^ 3 * psiPhi (lam D N (A N)) N w.1 (φ N w.1))) ∧
      aprioriLL D μ A (bootDom τ ℓ)
        (fun N z => (1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z)) ∧
      PrecS μ (U := fun N => {z // z ∈ bootDom τ ℓ N} ×
          {B : Matrix (Idx D N) (Idx D N) ℂ // opNorm B ≤ 1})
        (fun N w h => ‖ntr ((res (Matrix.of h + lam D N (A N)) w.1.1 -
          MExt (lam D N (A N)) w.1.1) * w.2.1)‖)
        (fun N w _ => (1 + φ N w.1.1) ^ 6 * psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1) ^ 2 +
          min ((1 + φ N w.1.1) ^ 6 * psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1) ^ 2 /
              Real.sqrt (kappa (lam D N (A N)) w.1.1.re + w.1.1.im))
            ((1 + φ N w.1.1) ^ 3 * psiPhi (lam D N (A N)) N w.1.1 (φ N w.1.1))) := by
  obtain ⟨Kn, hKn1, hKn⟩ := fluct_net'
  obtain ⟨Ka, hKa1, hKa⟩ := fluct_avg_prec'
  refine ⟨max 8 (max Kn Ka), le_max_left _ _, ?_⟩
  intro D δA τ C θ μ A hseq hτ hτ4 ℓ hℓ φ hφ hmono hLL
  set K := max 8 (max Kn Ka) with hKdef
  have hK8 : 8 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  set δ₀ := τ / K with hδ₀
  have hδ₀0 : 0 ≤ δ₀ := by positivity
  have hKnδ : Kn * δ₀ ≤ τ := by
    have h1 : Kn ≤ K := (le_max_left _ _).trans (le_max_right _ _)
    calc Kn * δ₀ ≤ K * δ₀ := mul_le_mul_of_nonneg_right h1 hδ₀0
      _ = τ := by rw [hδ₀]; field_simp
  have hKaδ : Ka * δ₀ ≤ τ := by
    have h1 : Ka ≤ K := (le_max_right _ _).trans (le_max_right _ _)
    calc Ka * δ₀ ≤ K * δ₀ := mul_le_mul_of_nonneg_right h1 hδ₀0
      _ = τ := by rw [hδ₀]; field_simp
  set Zf : ℕ → Set ℂ := fun N => {z | z ∈ bootDom τ ℓ N ∧ ‖z‖ ≤ (N : ℝ) ^ δ₀} with hZfdef
  have hZf1 : ∀ N, ∀ z ∈ Zf N, ‖z‖ ≤ (N : ℝ) ^ δ₀ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im :=
    fun N z hz => ⟨hz.2, (hℓ N).trans hz.1.2.1⟩
  have hφf : ∀ N, ∀ z ∈ Zf N, ((N : ℝ))⁻¹ ≤ φ N z ∧ φ N z ≤ (N : ℝ) ^ δ₀ :=
    fun N z hz => hφ N z hz.1
  have hLLf : aprioriLL D μ A Zf φ := by
    intro τ' hτ' D' hD'
    obtain ⟨N₀, hN₀⟩ := hLL τ' hτ' D' hD'
    exact ⟨N₀, fun N hN w => hN₀ N hN (⟨w.1.1, w.1.2.1⟩, w.2)⟩
  obtain ⟨net1, net2⟩ :=
    hKn D δA τ δ₀ C θ μ A hseq hτ hδ₀0 hKnδ Zf hZf1 φ hφf hLLf (5 / 2) (by norm_num)
  have avg := hKa D δA τ δ₀ C θ μ A hseq hτ hδ₀0 hKaδ Zf hZf1 φ hφf hLLf
  have core := Boot_core D δA τ C θ μ A hseq hτ ℓ hℓ K Kn Ka hK8 hKn1 hKa1 φ hφ hmono Zf
    (fun N z => Iff.rfl) _ _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) net2 avg
  have hherm : ∀ N, μ N {h | ¬ (Matrix.of h).IsHermitian} = 0 := fun N =>
    ae_iff.mp (hseq.mem N).herm
  have hℓ0 : ∀ N : ℕ, 0 ≤ ℓ N := fun N => (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (hℓ N)
  set Z := τ⁻¹ + 2 with hZdef
  have hZ : 0 < Z := by positivity
  obtain ⟨NZ, hNZ⟩ := Boot_rpow_large (show 0 < δ₀ by positivity) Z
  have hZf : ∀ N, NZ ≤ N → ∀ z ∈ bootDom τ ℓ N, z ∈ Zf N := fun N hN z hz =>
    ⟨hz, (Boot_norm_le τ ℓ N (hℓ0 N) z hz).trans (hNZ N hN)⟩
  -- the controls are nonnegative
  have hctl : ∀ N, ∀ z ∈ bootDom τ ℓ N,
      0 ≤ (1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z) ∧
      0 ≤ (1 + φ N z) ^ 6 * psiPhi (lam D N (A N)) N z (φ N z) ^ 2 ∧
      0 ≤ min ((1 + φ N z) ^ 6 * psiPhi (lam D N (A N)) N z (φ N z) ^ 2 /
        Real.sqrt (kappa (lam D N (A N)) z.re + z.im))
        ((1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z)) := by
    intro N z hz
    have hφ0 : 0 ≤ φ N z := (inv_nonneg.mpr (Nat.cast_nonneg _)).trans (hφ N z hz).1
    have hη : 0 ≤ z.im := (hℓ0 N).trans hz.2.1
    have hΨ : 0 ≤ psiPhi (lam D N (A N)) N z (φ N z) := by unfold psiPhi; positivity
    refine ⟨by positivity, by positivity, le_min (by positivity) (by positivity)⟩
  have hD1 : 1 ≤ D := hseq.one_le_D
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  obtain ⟨Nl, hNl⟩ := Boot_rpow_neg_small hseq.pos (show (0 : ℝ) < 1 / (20 * (D : ℝ) ^ 2) by
    positivity)
  have hℓΛ : ∀ N, Nl ≤ N → 1 ≤ N → opNorm (lam D N (A N)) ≤ 1 / 10 := by
    intro N hN hN1
    refine (Boot_opNorm_lam D N hN1 (A N)).trans ?_
    have h1 := (hseq.small N).trans (hNl N hN)
    calc 2 * (D : ℝ) ^ 2 * opNorm (A N) ≤ 2 * (D : ℝ) ^ 2 * (1 / (20 * (D : ℝ) ^ 2)) := by gcongr
      _ = 1 / 10 := by field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · -- the block traces
    intro τ' hτ' D' hD'
    obtain ⟨N₀, hN₀⟩ := core (min τ' (τ / 32)) (lt_min hτ' (by positivity)) (min_le_right _ _)
      D' hD'
    refine ⟨max N₀ 1, fun N hN w => ?_⟩
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_of_max_le_right hN)
    have hc := hN₀ N (le_of_max_le_left hN) w.1 w.2
    refine le_trans (measure_mono ?_) ((measure_union_le _ _).trans
      (le_trans (add_le_add hc (le_of_eq (hherm N))) (by rw [add_zero])))
    intro h hh
    by_cases hH : (Matrix.of h).IsHermitian
    · left
      refine ⟨hH, fun ⟨h1, _⟩ => ?_⟩
      have hmin := (hctl N w.1 w.2).2.2
      have h2 : (N : ℝ) ^ min τ' (τ / 32) ≤ (N : ℝ) ^ τ' :=
        Real.rpow_le_rpow_of_exponent_le hNr1 (min_le_left _ _)
      have h3 := mul_le_mul_of_nonneg_right h2 hmin
      simp only [Set.mem_ofPred_eq] at hh
      linarith
    · right; exact hH
  · -- the isotropic entries
    intro τ' hτ' D' hD'
    set τ'' := min (τ' / 2) (τ / 32) with hτ''
    have hτ''0 : 0 < τ'' := lt_min (by positivity) (by positivity)
    obtain ⟨N₀, hN₀⟩ := core τ'' hτ''0 (min_le_right _ _) (D' + 1) (by linarith)
    obtain ⟨N₁, hN₁⟩ := net1 τ'' hτ''0 (D' + 1) (by linarith)
    obtain ⟨N₂, hN₂⟩ := Boot_rpow_large (show 0 < τ' / 2 by positivity)
      (25 / 8 + (1 + Z) ^ Kn)
    refine ⟨max (max N₀ N₁) (max (max N₂ NZ) (max Nl 2)), fun N hN w => ?_⟩
    have hN0' : N₀ ≤ N := le_trans (by simp) hN
    have hN1' : N₁ ≤ N := le_trans (by simp) hN
    have hN2' : N₂ ≤ N := le_trans (by simp) hN
    have hNZ' : NZ ≤ N := le_trans (by simp) hN
    have hNl' : Nl ≤ N := le_trans (by simp) hN
    have hN2 : 2 ≤ N := le_trans (by simp) hN
    have hN1 : 1 ≤ N := by omega
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    obtain ⟨⟨z, hz⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩ := w
    have hzZf := hZf N hNZ' z hz
    have hc := hN₀ N hN0' z hz
    have hn := hN₁ N hN1' (⟨z, hzZf⟩, ⟨s, hs⟩, ⟨t, ht⟩)
    have hzim : 0 < z.im :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) ((hℓ N).trans hz.2.1)
    refine le_trans (measure_mono ?_) (((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans (add_le_add hc hn)) (le_of_eq (hherm N)))).trans
        (by rw [add_zero]; exact Boot_two_le N hN2 D'))
    intro h hh
    simp only [Set.mem_ofPred_eq] at hh
    by_cases hH : (Matrix.of h).IsHermitian
    · left
      by_contra hb
      obtain ⟨hx1, hx2⟩ := Classical.byContradiction fun hab => hb (Or.inl ⟨hH, hab⟩)
      have hnb : h ∉ _ := fun hlt => hb (Or.inr hlt)
      simp only [Set.mem_ofPred_eq, not_lt] at hnb
      obtain ⟨hθ0, hθ1⟩ := hseq.theta N
      obtain ⟨hctl3, hctl6, hmin⟩ := hctl N z hz
      have hzn : ‖z‖ ≤ Z := Boot_norm_le τ ℓ N (hℓ0 N) z hz
      have hCn : (1 + ‖z‖) ^ Kn ≤ (1 + Z) ^ Kn :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      have hNτ : (N : ℝ) ^ τ'' * (25 / 8 + (1 + Z) ^ Kn) ≤ (N : ℝ) ^ τ' := by
        have e : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
          rw [← Real.rpow_add (by linarith)]; ring_nf
        rw [e]
        exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hNr1 (min_le_left _ _)) (hN₂ N hN2')
          (by positivity) (by positivity)
      have hdet := Boot_iso_det D N hD1 hN1 (θ N) hθ0 hθ1 (A N) (hℓΛ N hNl' hN1) (Matrix.of h) hH
        z hzim s t hs ht _ _ hx1 hx2 hnb
      have h4 : min ((1 + φ N z) ^ 6 * psiPhi (lam D N (A N)) N z (φ N z) ^ 2 /
          Real.sqrt (kappa (lam D N (A N)) z.re + z.im))
          ((1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z)) ≤
          (1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z) := min_le_right _ _
      have hNτ0 : 0 ≤ (N : ℝ) ^ τ'' := Real.rpow_nonneg (by linarith) _
      have h5 : (N : ℝ) ^ τ'' * ((1 + ‖z‖) ^ Kn * (1 + φ N z) ^ 3 *
          psiPhi (lam D N (A N)) N z (φ N z)) ≤
          (N : ℝ) ^ τ'' * ((1 + Z) ^ Kn * ((1 + φ N z) ^ 3 *
          psiPhi (lam D N (A N)) N z (φ N z))) := by
        rw [mul_assoc ((1 + ‖z‖) ^ Kn)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCn hctl3) hNτ0
      have h6 : 25 / 8 * ((N : ℝ) ^ τ'' * min ((1 + φ N z) ^ 6 *
          psiPhi (lam D N (A N)) N z (φ N z) ^ 2 /
          Real.sqrt (kappa (lam D N (A N)) z.re + z.im))
          ((1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z))) ≤
          25 / 8 * ((N : ℝ) ^ τ'' * ((1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hNτ0) (by norm_num)
      have h7 := mul_le_mul_of_nonneg_right hNτ hctl3
      nlinarith
    · right; exact hH
  · -- the averages
    intro τ' hτ' D' hD'
    set τ'' := min (τ' / 2) (τ / 32) with hτ''
    have hτ''0 : 0 < τ'' := lt_min (by positivity) (by positivity)
    obtain ⟨N₀, hN₀⟩ := core τ'' hτ''0 (min_le_right _ _) (D' + 1) (by linarith)
    obtain ⟨N₁, hN₁⟩ := net2 τ'' hτ''0 (D' + 1) (by linarith)
    obtain ⟨N₂, hN₂⟩ := Boot_rpow_large (show 0 < τ' / 2 by positivity)
      (25 / 8 + (1 + Z) ^ (2 * Kn))
    refine ⟨max (max N₀ N₁) (max (max N₂ NZ) (max Nl 2)), fun N hN w => ?_⟩
    have hN0' : N₀ ≤ N := le_trans (by simp) hN
    have hN1' : N₁ ≤ N := le_trans (by simp) hN
    have hN2' : N₂ ≤ N := le_trans (by simp) hN
    have hNZ' : NZ ≤ N := le_trans (by simp) hN
    have hNl' : Nl ≤ N := le_trans (by simp) hN
    have hN2 : 2 ≤ N := le_trans (by simp) hN
    have hN1 : 1 ≤ N := by omega
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    obtain ⟨⟨z, hz⟩, ⟨B, hB⟩⟩ := w
    have hzZf := hZf N hNZ' z hz
    have hc := hN₀ N hN0' z hz
    have hn := hN₁ N hN1' (⟨z, hzZf⟩, ⟨B, hB⟩)
    have hzim : 0 < z.im :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) ((hℓ N).trans hz.2.1)
    refine le_trans (measure_mono ?_) (((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans (add_le_add hc hn)) (le_of_eq (hherm N)))).trans
        (by rw [add_zero]; exact Boot_two_le N hN2 D'))
    intro h hh
    simp only [Set.mem_ofPred_eq] at hh
    by_cases hH : (Matrix.of h).IsHermitian
    · left
      by_contra hb
      obtain ⟨hx1, hx2⟩ := Classical.byContradiction fun hab => hb (Or.inl ⟨hH, hab⟩)
      have hnb : h ∉ _ := fun hlt => hb (Or.inr hlt)
      simp only [Set.mem_ofPred_eq, not_lt] at hnb
      obtain ⟨hθ0, hθ1⟩ := hseq.theta N
      obtain ⟨hctl3, hctl6, hmin⟩ := hctl N z hz
      have hzn : ‖z‖ ≤ Z := Boot_norm_le τ ℓ N (hℓ0 N) z hz
      have hCn : (1 + ‖z‖) ^ (2 * Kn) ≤ (1 + Z) ^ (2 * Kn) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      have hCn0 : 0 ≤ (1 + Z) ^ (2 * Kn) := Real.rpow_nonneg (by linarith) _
      have hNτ : (N : ℝ) ^ τ'' * (25 / 8 + (1 + Z) ^ (2 * Kn)) ≤ (N : ℝ) ^ τ' := by
        have e : (N : ℝ) ^ τ' = (N : ℝ) ^ (τ' / 2) * (N : ℝ) ^ (τ' / 2) := by
          rw [← Real.rpow_add (by linarith)]; ring_nf
        rw [e]
        exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hNr1 (min_le_left _ _)) (hN₂ N hN2')
          (by positivity) (by positivity)
      have hdet := Boot_avg_det D N hD1 hN1 (θ N) hθ0 hθ1 (A N) (hℓΛ N hNl' hN1) (Matrix.of h) hH
        z hzim B hB _ _ hx1 hx2 hnb
      have hNτ0 : 0 ≤ (N : ℝ) ^ τ'' := Real.rpow_nonneg (by linarith) _
      set r := (1 + φ N z) ^ 6 * psiPhi (lam D N (A N)) N z (φ N z) ^ 2 with hr
      set m := min (r / Real.sqrt (kappa (lam D N (A N)) z.re + z.im))
        ((1 + φ N z) ^ 3 * psiPhi (lam D N (A N)) N z (φ N z)) with hm
      have h5 : (N : ℝ) ^ τ'' * ((1 + ‖z‖) ^ (2 * Kn) * (1 + φ N z) ^ 6 *
          psiPhi (lam D N (A N)) N z (φ N z) ^ 2) ≤ (N : ℝ) ^ τ'' * ((1 + Z) ^ (2 * Kn) * r) := by
        rw [mul_assoc ((1 + ‖z‖) ^ (2 * Kn))]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCn hctl6) hNτ0
      have h7 := mul_le_mul_of_nonneg_right hNτ (add_nonneg hctl6 hmin)
      have h8 : 25 / 8 * ((N : ℝ) ^ τ'' * m) + (N : ℝ) ^ τ'' * ((1 + Z) ^ (2 * Kn) * r) ≤
          (N : ℝ) ^ τ'' * (25 / 8 + (1 + Z) ^ (2 * Kn)) * (r + m) := by
        have : 0 ≤ (N : ℝ) ^ τ'' * (25 / 8 * r + (1 + Z) ^ (2 * Kn) * m) := by positivity
        nlinarith
      linarith
    · right; exact hH

end RBMTransitionEdge

end
