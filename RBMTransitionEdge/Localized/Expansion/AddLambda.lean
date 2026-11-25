module

public import RBMTransitionEdge.Det.Taylor

@[expose] public section

/-!
# The package form of (A.7) for packages without resolvent

(5.90) [eq:addoneLambda] by (5.89) [further_expansion_first_order_expansion] in the proof of
Lemma 5.5 [claim_estimate_remainder_terms]: an entry of a product of deterministic matrices
around `Λ - δ`, with labels in one block, is bounded by `‖Λ e_x‖ ‖Λ e_y‖ + |δ|`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

section AddLambdaTools

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `opNorm` is the `L²` operator norm of matrices. -/
private lemma AddL_op_eq (A : Matrix ι ι ℂ) : opNorm A = ‖A‖ := rfl

/-- `‖1‖ ≤ 1`. -/
private lemma AddL_op_one : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-- `‖0‖ = 0`. -/
private lemma AddL_op_zero : opNorm (0 : Matrix ι ι ℂ) = 0 := by
  unfold opNorm
  rw [map_zero, norm_zero]

/-- `‖A B‖ ≤ ‖A‖ ‖B‖`. -/
private lemma AddL_op_mul (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [AddL_op_eq] using norm_mul_le A B

/-- `‖A + B‖ ≤ ‖A‖ + ‖B‖`. -/
private lemma AddL_op_add (A B : Matrix ι ι ℂ) : opNorm (A + B) ≤ opNorm A + opNorm B := by
  simpa only [AddL_op_eq] using norm_add_le A B

/-- `‖c A‖ = |c| ‖A‖`. -/
private lemma AddL_op_smul (c : ℂ) (A : Matrix ι ι ℂ) : opNorm (c • A) = ‖c‖ * opNorm A := by
  simpa only [AddL_op_eq] using norm_smul c A

/-- `‖A‖ ≥ 0`. -/
private lemma AddL_op_nonneg (A : Matrix ι ι ℂ) : 0 ≤ opNorm A := norm_nonneg _

/-- `|A_{ij}| ≤ ‖A‖`. -/
private lemma AddL_entry_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [h1, mul_one] at h
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  have h3 : ((EuclideanSpace.equiv ι ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)).ofLp i = A i j := by
    simp
  rw [h3] at h2
  exact h2.trans h

omit [Fintype ι] in
/-- `|(1)_{xy}| ≤ 1`. -/
private lemma AddL_one_le (x y : ι) : ‖(1 : Matrix ι ι ℂ) x y‖ ≤ 1 := by
  by_cases h : x = y <;> simp [Matrix.one_apply, h]

/-- For Hermitian `Λ`, `|(Λ X Λ)_{xy}| ≤ ‖Λ e_x‖ ‖X‖ ‖Λ e_y‖`. -/
private lemma AddL_sandwich {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (X : Matrix ι ι ℂ)
    (x y : ι) :
    ‖(Λ * X * Λ) x y‖ ≤
      Real.sqrt (∑ i, ‖Λ i x‖ ^ 2) * opNorm X * Real.sqrt (∑ i, ‖Λ i y‖ ^ 2) := by
  set v : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm fun j => Λ j y
  set u : ι → ℂ := X *ᵥ fun j => Λ j y
  have hw := Matrix.l2_opNorm_mulVec X v
  have hv : ‖v‖ = Real.sqrt (∑ i, ‖Λ i y‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    rfl
  have hu : ‖(EuclideanSpace.equiv ι ℂ).symm (X *ᵥ v.ofLp)‖ = Real.sqrt (∑ i, ‖u i‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    rfl
  rw [hu, hv] at hw
  have he : (Λ * X * Λ) x y = ∑ i, Λ x i * u i := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    rfl
  have hx : ∀ i, ‖Λ x i‖ = ‖Λ i x‖ := fun i => by
    rw [← hΛ.apply x i, norm_star]
  rw [he]
  calc ‖∑ i, Λ x i * u i‖ ≤ ∑ i, ‖Λ i x‖ * ‖u i‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, hx]
    _ ≤ Real.sqrt (∑ i, ‖Λ i x‖ ^ 2) * Real.sqrt (∑ i, ‖u i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ i, ‖Λ i x‖ ^ 2) * (opNorm X * Real.sqrt (∑ i, ‖Λ i y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- A factor `F` with `F = -α + α Λ F = -α + α F Λ`, `|α| ≤ 2` and `‖F‖ ≤ 2`: the form
(5.89) [further_expansion_first_order_expansion] of `M` and `M^*`. -/
private def AddL_good (Λ F : Matrix ι ι ℂ) : Prop :=
  ∃ α : ℂ, ‖α‖ ≤ 2 ∧ opNorm F ≤ 2 ∧ F = -α • (1 : Matrix ι ι ℂ) + α • (Λ * F) ∧
    F = -α • (1 : Matrix ι ι ℂ) + α • (F * Λ)

/-- A two-sided inverse `F` of `Λ - ζ` with `|ζ| ≥ 1/2` and `‖F‖ ≤ 2` has the form
(5.89) [further_expansion_first_order_expansion]. -/
private lemma AddL_good_of (Λ F : Matrix ι ι ℂ) (ζ : ℂ) (hζ : 1 / 2 ≤ ‖ζ‖) (hF : opNorm F ≤ 2)
    (h : (Λ - ζ • (1 : Matrix ι ι ℂ)) * F = 1) : AddL_good Λ F := by
  have h' : F * (Λ - ζ • (1 : Matrix ι ι ℂ)) = 1 := mul_eq_one_comm.mp h
  have hζ0 : ζ ≠ 0 := fun e => by rw [e, norm_zero] at hζ; norm_num at hζ
  have hα : ‖ζ⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc ‖ζ‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hζ
      _ = 2 := by norm_num
  have e1 : ζ • F = Λ * F - 1 := by
    rw [← h, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    abel
  have e2 : ζ • F = F * Λ - 1 := by
    rw [← h', Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
    abel
  have key : ∀ G : Matrix ι ι ℂ, ζ • F = G - 1 → F = -ζ⁻¹ • (1 : Matrix ι ι ℂ) + ζ⁻¹ • G := by
    intro G hG
    calc F = ζ⁻¹ • (ζ • F) := by rw [smul_smul, inv_mul_cancel₀ hζ0, one_smul]
      _ = -ζ⁻¹ • (1 : Matrix ι ι ℂ) + ζ⁻¹ • G := by rw [hG, smul_sub, neg_smul]; abel
  exact ⟨ζ⁻¹, hα, hF, key _ e1, key _ e2⟩

omit [DecidableEq ι] in
/-- A row of `B₁` agrees with a row of `R`: then so do the rows of `B₁ Y` and `R Y`. -/
private lemma AddL_row {A B : Matrix ι ι ℂ} (x : ι) (h : ∀ j, A x j = B x j)
    (Y : Matrix ι ι ℂ) (y : ι) : (A * Y) x y = (B * Y) x y := by
  simp only [Matrix.mul_apply, h]

omit [DecidableEq ι] in
/-- A column of `B₂` agrees with a column of `R`: then so do the columns of `Y B₂` and `Y R`. -/
private lemma AddL_col {A B : Matrix ι ι ℂ} (y : ι) (h : ∀ k, A k y = B k y)
    (Y : Matrix ι ι ℂ) (x : ι) : (Y * A) x y = (Y * B) x y := by
  simp only [Matrix.mul_apply, h]

/-- The expansion of `(p + Λ W)(Λ - δ)(q + V Λ)` into its seven terms. -/
private lemma AddL_expand (p q δ : ℂ) (Λ W V : Matrix ι ι ℂ) :
    (p • (1 : Matrix ι ι ℂ) + Λ * W) * (Λ - δ • (1 : Matrix ι ι ℂ)) *
        (q • (1 : Matrix ι ι ℂ) + V * Λ) =
      (p * q) • (Λ - δ • (1 : Matrix ι ι ℂ)) + p • (Λ * V * Λ) - (p * δ) • (V * Λ) +
        q • (Λ * W * Λ) - (q * δ) • (Λ * W) + Λ * (W * Λ * V) * Λ -
        δ • (Λ * (W * V) * Λ) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    smul_smul, smul_sub, smul_add]
  module

end AddLambdaTools

section AddLambdaProducts

open scoped Matrix.Norms.L2Operator

/-- `‖E_a‖ ≤ 1`. -/
private lemma AddL_op_Ea {D N : ℕ} (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  rw [AddL_op_eq, Ea, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun p => ?_
  by_cases hp : p.1 = a <;> simp [hp]

/-- `(E_a B)_{xj} = 1(x ∈ I_a) B_{xj}`. -/
private lemma AddL_Ea_mul {D N : ℕ} (a : Fin D) (B : Matrix (Idx D N) (Idx D N) ℂ)
    (x j : Idx D N) : (Ea D N a * B) x j = (if x.1 = a then 1 else 0) * B x j := by
  rw [Ea, Matrix.diagonal_mul]

/-- `(E_a)_{iy} = 1(y ∈ I_a) 1(i = y)`. -/
private lemma AddL_Ea_apply {D N : ℕ} (a : Fin D) (i y : Idx D N) :
    Ea D N a i y = (if y.1 = a then 1 else 0) * (1 : Matrix (Idx D N) (Idx D N) ℂ) i y := by
  by_cases h : i = y
  · subst h
    simp [Ea]
  · simp [Ea, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

/-- The left factor of (5.90) [eq:addoneLambda] by (5.89)
[further_expansion_first_order_expansion]: row `x` of `B₁ = Π F_i E_{a_i}` is
`p e_xᵀ + e_xᵀ Λ W` with `|p|`, `‖W‖` and `‖B₁‖` bounded in terms of the length. -/
private lemma AddL_left (n : ℕ) : ∃ Kp Kw Kb : ℝ, 0 ≤ Kp ∧ 0 ≤ Kw ∧ 0 ≤ Kb ∧
    ∀ {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (F : Fin n → Matrix (Idx D N) (Idx D N) ℂ)
      (a : Fin n → Fin D), (∀ i, AddL_good Λ (F i)) →
      opNorm (List.ofFn fun i => F i * Ea D N (a i)).prod ≤ Kb ∧
      ∀ x : Idx D N, ∃ (p : ℂ) (W : Matrix (Idx D N) (Idx D N) ℂ), ‖p‖ ≤ Kp ∧ opNorm W ≤ Kw ∧
        ∀ j, (List.ofFn fun i => F i * Ea D N (a i)).prod x j =
          p * (1 : Matrix (Idx D N) (Idx D N) ℂ) x j + (Λ * W) x j := by
  induction n with
  | zero =>
    refine ⟨1, 0, 1, by norm_num, le_rfl, by norm_num, fun Λ F a _ => ⟨?_, fun x => ?_⟩⟩
    · simpa using AddL_op_one
    · exact ⟨1, 0, by simp, by rw [AddL_op_zero], fun j => by simp⟩
  | succ n ih =>
    obtain ⟨Kp, Kw, Kb, hKp, hKw, hKb, h⟩ := ih
    refine ⟨2 * Kp, 2 * Kw + 4 * Kb, 2 * Kb, by positivity, by positivity, by positivity,
      fun {D N} Λ F a hF => ?_⟩
    obtain ⟨hB, hrow⟩ := h Λ (fun i => F i.succ) (fun i => a i.succ) (fun i => hF i.succ)
    rw [List.ofFn_succ, List.prod_cons]
    set B' := (List.ofFn fun i : Fin n => F i.succ * Ea D N (a i.succ)).prod
    obtain ⟨α, hα, hF0, hL, -⟩ := hF 0
    have hE := AddL_op_Ea (N := N) (a 0)
    have hFEB : opNorm (F 0 * Ea D N (a 0) * B') ≤ 2 * Kb := by
      refine (AddL_op_mul _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (AddL_op_mul _ _) (AddL_op_nonneg _)).trans ?_
      have h1 : opNorm (F 0) * opNorm (Ea D N (a 0)) ≤ 2 := by
        nlinarith [AddL_op_nonneg (F 0), AddL_op_nonneg (Ea D N (a 0))]
      nlinarith [AddL_op_nonneg (F 0) , AddL_op_nonneg (Ea D N (a 0)), AddL_op_nonneg B',
        mul_nonneg (AddL_op_nonneg (F 0)) (AddL_op_nonneg (Ea D N (a 0)))]
    refine ⟨hFEB, fun x => ?_⟩
    obtain ⟨p, W, hp, hW, hx⟩ := hrow x
    set ε : ℂ := if x.1 = a 0 then 1 else 0 with hε
    have hε1 : ‖ε‖ ≤ 1 := by rw [hε]; split <;> simp
    refine ⟨-α * ε * p, (-α * ε) • W + α • (F 0 * Ea D N (a 0) * B'), ?_, ?_, fun j => ?_⟩
    · rw [norm_mul, norm_mul, norm_neg]
      have := mul_le_mul hα hε1 (norm_nonneg _) (by norm_num)
      nlinarith [norm_nonneg α, norm_nonneg ε, norm_nonneg p, mul_nonneg (norm_nonneg α)
        (norm_nonneg ε)]
    · refine (AddL_op_add _ _).trans ?_
      rw [AddL_op_smul, AddL_op_smul, norm_mul, norm_neg]
      have h1 : ‖α‖ * ‖ε‖ ≤ 2 := by nlinarith [norm_nonneg α, norm_nonneg ε]
      nlinarith [norm_nonneg α, norm_nonneg ε, AddL_op_nonneg W, mul_nonneg (norm_nonneg α)
        (norm_nonneg ε), AddL_op_nonneg (F 0 * Ea D N (a 0) * B')]
    · have hEB : (Ea D N (a 0) * B') x j = ε * B' x j := AddL_Ea_mul (a 0) B' x j
      have e1 : (F 0 * Ea D N (a 0) * B') x j =
          -α * (ε * B' x j) + α * (Λ * (F 0 * Ea D N (a 0) * B')) x j := by
        conv_lhs => rw [hL]
        rw [← hEB]
        simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc,
          Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [e1, hx j]
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul]
      ring

/-- The right factor of (5.90) [eq:addoneLambda] by (5.89)
[further_expansion_first_order_expansion]: column `y` of `B₂ = Π E_{b_j} F_j` is
`q e_y + W Λ e_y` with `|q|` and `‖W‖` bounded in terms of the length. -/
private lemma AddL_right (n : ℕ) : ∃ Kq Kw : ℝ, 0 ≤ Kq ∧ 0 ≤ Kw ∧
    ∀ {D N : ℕ} (Λ : Matrix (Idx D N) (Idx D N) ℂ) (F : Fin n → Matrix (Idx D N) (Idx D N) ℂ)
      (b : Fin n → Fin D), (∀ i, AddL_good Λ (F i)) →
      ∀ y : Idx D N, ∃ (q : ℂ) (W : Matrix (Idx D N) (Idx D N) ℂ), ‖q‖ ≤ Kq ∧ opNorm W ≤ Kw ∧
        ∀ i, (List.ofFn fun j => Ea D N (b j) * F j).prod i y =
          q * (1 : Matrix (Idx D N) (Idx D N) ℂ) i y + (W * Λ) i y := by
  induction n with
  | zero =>
    exact ⟨1, 0, by norm_num, le_rfl, fun Λ F b _ y =>
      ⟨1, 0, by simp, by rw [AddL_op_zero], fun i => by simp⟩⟩
  | succ n ih =>
    obtain ⟨Kq, Kw, hKq, hKw, h⟩ := ih
    refine ⟨2 * Kq, 4 * Kq + 2 * Kw, by positivity, by positivity,
      fun {D N} Λ F b hF y => ?_⟩
    obtain ⟨q, W, hq, hW, hy⟩ := h Λ (fun i => F i.succ) (fun i => b i.succ)
      (fun i => hF i.succ) y
    rw [List.ofFn_succ, List.prod_cons]
    set B' := (List.ofFn fun i : Fin n => Ea D N (b i.succ) * F i.succ).prod
    obtain ⟨α, hα, hF0, -, hR⟩ := hF 0
    set X := Ea D N (b 0) * F 0 with hXdef
    have hE := AddL_op_Ea (N := N) (b 0)
    have hX : opNorm X ≤ 2 := by
      refine (AddL_op_mul _ _).trans ?_
      nlinarith [AddL_op_nonneg (F 0), AddL_op_nonneg (Ea D N (b 0))]
    set ε : ℂ := if y.1 = b 0 then 1 else 0 with hε
    have hε1 : ‖ε‖ ≤ 1 := by rw [hε]; split <;> simp
    refine ⟨-α * q * ε, (α * q) • X + X * W, ?_, ?_, fun i => ?_⟩
    · rw [norm_mul, norm_mul, norm_neg]
      nlinarith [norm_nonneg α, norm_nonneg ε, norm_nonneg q, mul_nonneg (norm_nonneg α)
        (norm_nonneg q), mul_le_mul hα hq (norm_nonneg _) (by norm_num)]
    · refine (AddL_op_add _ _).trans ?_
      rw [AddL_op_smul, norm_mul]
      have h1 := AddL_op_mul X W
      nlinarith [norm_nonneg α, norm_nonneg q, AddL_op_nonneg W, AddL_op_nonneg X,
        mul_nonneg (norm_nonneg α) (norm_nonneg q), mul_le_mul hα hq (norm_nonneg _) (by norm_num),
        mul_le_mul hX hW (AddL_op_nonneg _) (by norm_num)]
    · have hcol : ∀ k, B' k y = (q • (1 : Matrix (Idx D N) (Idx D N) ℂ) + W * Λ) k y := by
        intro k
        rw [hy k]
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      have hXe : X i y = -α * (ε * (1 : Matrix (Idx D N) (Idx D N) ℂ) i y) + α * (X * Λ) i y := by
        rw [hXdef]
        conv_lhs => rw [hR]
        simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc, AddL_Ea_apply (b 0) i y]
        rw [← hε]
      calc (X * B') i y = (X * (q • (1 : Matrix (Idx D N) (Idx D N) ℂ) + W * Λ)) i y :=
            AddL_col y hcol X i
        _ = q * X i y + (X * W * Λ) i y := by
            simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.add_apply,
              Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc]
        _ = _ := by
            rw [hXe]
            simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.add_apply, Matrix.smul_apply,
              smul_eq_mul, Matrix.mul_assoc]
            ring

end AddLambdaProducts

set_option maxHeartbeats 1000000 in
/-- (5.90) [eq:addoneLambda], the package form of (A.7) [add_one_more_Lambda] by (5.89)
[further_expansion_first_order_expansion]: for `Λ` with vanishing diagonal blocks, products
`B₁ = Π M^{s_i} E_{a_i}`, `B₂ = Π E_{b_j} M^{t_j}` at one `z` and labels in one block,
`|(B₁ (Λ - δ) B₂)_{xy}| ≤ C (‖Λ e_x‖ ‖Λ e_y‖ + |δ|)`. -/
theorem pkg_add_lambda (τ : ℝ) (hτ : 0 < τ) (n₁ n₂ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ), 1 ≤ N →
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → (∀ x y : Idx D N, x.1 = y.1 → Λ x y = 0) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im → ∀ δ : ℝ,
      ∀ (s : Fin n₁ → Bool) (a : Fin n₁ → Fin D) (t : Fin n₂ → Bool) (b : Fin n₂ → Fin D)
        (x y : Idx D N), x.1 = y.1 →
        ‖((List.ofFn fun i : Fin n₁ =>
              (if s i then (MSol Λ z)ᴴ else MSol Λ z) * Ea D N (a i)).prod *
            (Λ - (δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
            (List.ofFn fun j : Fin n₂ =>
              Ea D N (b j) * (if t j then (MSol Λ z)ᴴ else MSol Λ z)).prod) x y‖ ≤
          C * (Real.sqrt (∑ i, ‖Λ i x‖ ^ 2) * Real.sqrt (∑ i, ‖Λ i y‖ ^ 2) + |δ|) := by
  obtain ⟨Kp, Kw, Kb, hKp, hKw, -, hLeft⟩ := AddL_left n₁
  obtain ⟨Kq, Kv, hKq, hKv, hRight⟩ := AddL_right n₂
  refine ⟨Kp * Kq + Kp * Kv + Kq * Kw + Kw * Kv + 1, by positivity, ?_⟩
  intro D N Λ _ hΛ hℓ hLam z _ hz δ s a t b x y hxy
  have : Nonempty (Idx D N) := ⟨x⟩
  obtain ⟨-, -, hspec⟩ := mSol_spec Λ hΛ z hz
  obtain ⟨hζ, -, hM⟩ := mSol_apriori Λ hΛ hℓ z hz
  have hℓ0 : 0 ≤ opNorm Λ := AddL_op_nonneg Λ
  set M := MSol Λ z
  set ζ := z + mSol Λ z
  have hζ2 : 1 / 2 ≤ ‖ζ‖ := by linarith
  have hM2 : opNorm M ≤ 2 := by
    refine hM.le.trans ?_
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hgM : AddL_good Λ M := AddL_good_of Λ M ζ hζ2 hM2 hspec
  have hgMH : AddL_good Λ Mᴴ := by
    have h' : M * (Λ - ζ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) = 1 := mul_eq_one_comm.mp hspec
    have h2 : (Λ - star ζ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * Mᴴ = 1 := by
      have := congrArg Matrix.conjTranspose h'
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, hΛ.eq] at this
      exact this
    refine AddL_good_of Λ Mᴴ (star ζ) (by rwa [norm_star]) ?_ h2
    rw [AddL_op_eq, Matrix.l2_opNorm_conjTranspose]
    exact hM2
  have hgood : ∀ c : Bool, AddL_good Λ (if c then Mᴴ else M) := fun c => by
    cases c
    · exact hgM
    · exact hgMH
  obtain ⟨-, hrow⟩ := hLeft Λ (fun i => if s i then Mᴴ else M) a (fun i => hgood (s i))
  obtain ⟨p, W, hp, hW, hx⟩ := hrow x
  obtain ⟨q, V, hq, hV, hy⟩ := hRight Λ (fun j => if t j then Mᴴ else M) b
    (fun j => hgood (t j)) y
  set B₁ := (List.ofFn fun i : Fin n₁ => (if s i then Mᴴ else M) * Ea D N (a i)).prod
  set B₂ := (List.ofFn fun j : Fin n₂ => Ea D N (b j) * (if t j then Mᴴ else M)).prod
  have h1 : ∀ j, B₁ x j =
      (p • (1 : Matrix (Idx D N) (Idx D N) ℂ) + Λ * W) x j := fun j => by
    rw [hx j]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have h2 : ∀ k, B₂ k y =
      (q • (1 : Matrix (Idx D N) (Idx D N) ℂ) + V * Λ) k y := fun k => by
    rw [hy k]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [AddL_col y h2, Matrix.mul_assoc, AddL_row x h1, ← Matrix.mul_assoc,
    AddL_expand p q (δ : ℂ) Λ W V]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hLam x y hxy]
  set cx := Real.sqrt (∑ i, ‖Λ i x‖ ^ 2)
  set cy := Real.sqrt (∑ i, ‖Λ i y‖ ^ 2)
  have hcx : 0 ≤ cx := Real.sqrt_nonneg _
  have hcy : 0 ≤ cy := Real.sqrt_nonneg _
  have hd : 0 ≤ |δ| := abs_nonneg δ
  have hδn : ‖(δ : ℂ)‖ = |δ| := Complex.norm_real δ
  have hA : 0 ≤ cx * cy := mul_nonneg hcx hcy
  have e1 : ‖(p * q) * (0 - (δ : ℂ) * (1 : Matrix (Idx D N) (Idx D N) ℂ) x y)‖ ≤
      Kp * Kq * |δ| := by
    rw [zero_sub, norm_mul, norm_neg, norm_mul, norm_mul, hδn]
    have h3 : |δ| * ‖(1 : Matrix (Idx D N) (Idx D N) ℂ) x y‖ ≤ |δ| :=
      mul_le_of_le_one_right hd (AddL_one_le x y)
    exact mul_le_mul (mul_le_mul hp hq (norm_nonneg _) hKp) h3 (by positivity)
      (mul_nonneg hKp hKq)
  have e2 : ‖p * (Λ * V * Λ) x y‖ ≤ Kp * Kv * (cx * cy) := by
    rw [norm_mul]
    have hs := AddL_sandwich hΛ V x y
    have : cx * opNorm V * cy ≤ Kv * (cx * cy) := by nlinarith [AddL_op_nonneg V]
    have h0 : ‖(Λ * V * Λ) x y‖ ≤ Kv * (cx * cy) := hs.trans this
    nlinarith [norm_nonneg p, norm_nonneg ((Λ * V * Λ) x y), mul_le_mul hp h0 (norm_nonneg _) hKp]
  have e3 : ‖(p * (δ : ℂ)) * (V * Λ) x y‖ ≤ Kp * Kv * |δ| := by
    rw [norm_mul, norm_mul, hδn]
    have h0 : ‖(V * Λ) x y‖ ≤ Kv := by
      refine (AddL_entry_le _ x y).trans ((AddL_op_mul _ _).trans ?_)
      nlinarith [AddL_op_nonneg V]
    nlinarith [norm_nonneg p, norm_nonneg ((V * Λ) x y), mul_le_mul hp h0 (norm_nonneg _) hKp]
  have e4 : ‖q * (Λ * W * Λ) x y‖ ≤ Kq * Kw * (cx * cy) := by
    rw [norm_mul]
    have hs := AddL_sandwich hΛ W x y
    have : cx * opNorm W * cy ≤ Kw * (cx * cy) := by nlinarith [AddL_op_nonneg W]
    have h0 : ‖(Λ * W * Λ) x y‖ ≤ Kw * (cx * cy) := hs.trans this
    nlinarith [norm_nonneg q, norm_nonneg ((Λ * W * Λ) x y), mul_le_mul hq h0 (norm_nonneg _) hKq]
  have e5 : ‖(q * (δ : ℂ)) * (Λ * W) x y‖ ≤ Kq * Kw * |δ| := by
    rw [norm_mul, norm_mul, hδn]
    have h0 : ‖(Λ * W) x y‖ ≤ Kw := by
      refine (AddL_entry_le _ x y).trans ((AddL_op_mul _ _).trans ?_)
      nlinarith [AddL_op_nonneg W]
    nlinarith [norm_nonneg q, norm_nonneg ((Λ * W) x y), mul_le_mul hq h0 (norm_nonneg _) hKq]
  have e6 : ‖(Λ * (W * Λ * V) * Λ) x y‖ ≤ Kw * Kv * (cx * cy) := by
    have hs := AddL_sandwich hΛ (W * Λ * V) x y
    have hn : opNorm (W * Λ * V) ≤ Kw * Kv := by
      refine (AddL_op_mul _ _).trans ?_
      have := AddL_op_mul W Λ
      have h3 : opNorm (W * Λ) ≤ Kw := this.trans (by nlinarith [AddL_op_nonneg W])
      exact mul_le_mul h3 hV (AddL_op_nonneg _) hKw
    have : cx * opNorm (W * Λ * V) * cy ≤ Kw * Kv * (cx * cy) := by
      nlinarith [AddL_op_nonneg (W * Λ * V)]
    exact hs.trans this
  have e7 : ‖(δ : ℂ) * (Λ * (W * V) * Λ) x y‖ ≤ Kw * Kv * |δ| := by
    rw [norm_mul, hδn]
    have hWV : opNorm (W * V) ≤ Kw * Kv :=
      (AddL_op_mul W V).trans (mul_le_mul hW hV (AddL_op_nonneg _) hKw)
    have hΛWV : opNorm (Λ * (W * V)) ≤ Kw * Kv := by
      refine (AddL_op_mul _ _).trans ?_
      nlinarith [AddL_op_nonneg (W * V), mul_nonneg hKw hKv]
    have h0 : ‖(Λ * (W * V) * Λ) x y‖ ≤ Kw * Kv := by
      refine (AddL_entry_le _ x y).trans ((AddL_op_mul _ _).trans ?_)
      nlinarith [AddL_op_nonneg (Λ * (W * V)), mul_nonneg hKw hKv]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right h0 hd
  have tri : ‖(p * q) * (0 - (δ : ℂ) * (1 : Matrix (Idx D N) (Idx D N) ℂ) x y) +
      p * (Λ * V * Λ) x y - (p * (δ : ℂ)) * (V * Λ) x y + q * (Λ * W * Λ) x y -
      (q * (δ : ℂ)) * (Λ * W) x y + (Λ * (W * Λ * V) * Λ) x y -
      (δ : ℂ) * (Λ * (W * V) * Λ) x y‖ ≤
      ‖(p * q) * (0 - (δ : ℂ) * (1 : Matrix (Idx D N) (Idx D N) ℂ) x y)‖ +
      ‖p * (Λ * V * Λ) x y‖ + ‖(p * (δ : ℂ)) * (V * Λ) x y‖ + ‖q * (Λ * W * Λ) x y‖ +
      ‖(q * (δ : ℂ)) * (Λ * W) x y‖ + ‖(Λ * (W * Λ * V) * Λ) x y‖ +
      ‖(δ : ℂ) * (Λ * (W * V) * Λ) x y‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  refine tri.trans ?_
  nlinarith [mul_nonneg (mul_nonneg hKp hKq) hA, mul_nonneg (mul_nonneg hKp hKv) hd,
    mul_nonneg (mul_nonneg hKq hKw) hd, mul_nonneg (mul_nonneg hKw hKv) hd, hA, hd]

end RBMTransitionEdge

end
