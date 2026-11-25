module

public import RBMTransitionEdge.LocalLaw.Class
public import RBMTransitionEdge.LocalLaw.Dyson

@[expose] public section

/-!
# Estimates for the vector equation

The expansion `q_abc = m³δ_abc + O(‖Λ‖²)`, the contraction for `Im z ≥ 2`, and lower bounds on `Im m` from (A.3)
[equation_z_im_m].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The normalized trace on an empty index type vanishes. -/
private lemma DysonBounds_ntr_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (B : Matrix ι ι ℂ) :
    ntr B = 0 := by
  simp [ntr, Matrix.trace]

/-- `|D⟨E_a W⟩| ≤ B` when the diagonal entries of `W` are at most `B` in modulus. -/
private lemma DysonBounds_blk_le (D N : ℕ) (a : Fin D) (W : Matrix (Idx D N) (Idx D N) ℂ)
    (B : ℝ) (hB : 0 ≤ B) (h : ∀ p, ‖W p p‖ ≤ B) : ‖(D : ℂ) * ntr (Ea D N a * W)‖ ≤ B := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : IsEmpty (Idx D 0) := ⟨fun p => p.2.elim0⟩
    simp [DysonBounds_ntr_of_isEmpty, hB]
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


/-- The operator norm is nonnegative. -/
private lemma DysonBounds_opNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    0 ≤ opNorm X := norm_nonneg _

/-- The operator norm of a product of matrices with bounded norms. -/
private lemma DysonBounds_opNorm_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ}
    {x y : ℝ} (hX : opNorm X ≤ x) (hY : opNorm Y ≤ y) : opNorm (X * Y) ≤ x * y :=
  (opNorm_mul_le X Y).trans
    (mul_le_mul hX hY (DysonBounds_opNorm_nonneg Y) ((DysonBounds_opNorm_nonneg X).trans hX))

/-- The operator norm of a difference. -/
private lemma DysonBounds_opNorm_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) : opNorm (X - Y) ≤ opNorm X + opNorm Y := by
  unfold opNorm
  rw [map_sub]
  exact norm_sub_le _ _

open scoped Matrix.Norms.L2Operator in
/-- The block projections are contractions. -/
private lemma DysonBounds_opNorm_Ea (D N : ℕ) (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  unfold opNorm Ea
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
  split_ifs <;> simp

/-- `σ_θ x` entrywise: `θ x_a + (1 - θ) D⁻¹ Σ_b x_b`. -/
private lemma DysonBounds_sig_apply (D : ℕ) (θ : ℝ) (x : Fin D → ℂ) (a : Fin D) :
    (sigTheta D θ *ᵥ x) a =
      (θ : ℂ) * x a + ((1 - θ : ℝ) : ℂ) * ((D : ℂ)⁻¹ * ∑ b, x b) := by
  have hJ : (Matrix.of fun (_ _ : Fin D) => (1 : ℂ)) *ᵥ x = fun _ => ∑ b, x b := by
    ext
    simp [Matrix.mulVec, dotProduct]
  simp only [sigTheta, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hJ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- `‖σ_θ x‖_∞ ≤ ‖x‖_∞` for `θ ∈ [0, 1]`. -/
private lemma DysonBounds_sig_linf (D : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : Fin D → ℂ)
    (a : Fin D) : ‖(sigTheta D θ *ᵥ x) a‖ ≤ ‖x‖ := by
  have hD : 0 < D := a.pos
  have hx : ∀ b, ‖x b‖ ≤ ‖x‖ := fun b => norm_le_pi_norm x b
  rw [DysonBounds_sig_apply]
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

/-- The normalized trace is additive. -/
private lemma DysonBounds_ntr_add {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P + Q) = ntr P + ntr Q := by
  simp [ntr, Matrix.trace_add, mul_add]

/-- The normalized trace commutes with negation. -/
private lemma DysonBounds_ntr_neg {ι : Type*} [Fintype ι] (P : Matrix ι ι ℂ) :
    ntr (-P) = -ntr P := by
  simp [ntr, Matrix.trace_neg]

/-- The normalized trace is homogeneous. -/
private lemma DysonBounds_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (P : Matrix ι ι ℂ) :
    ntr (c • P) = c * ntr P := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

/-- The normalized trace is cyclic. -/
private lemma DysonBounds_ntr_comm {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P * Q) = ntr (Q * P) := by
  simp [ntr, Matrix.trace_mul_comm P Q]

/-- `E_a E_b = δ_{ab} E_a`. -/
private lemma DysonBounds_Ea_mul (D N : ℕ) (a b : Fin D) :
    Ea D N a * Ea D N b = if a = b then Ea D N a else 0 := by
  unfold Ea
  rw [Matrix.diagonal_mul_diagonal]
  by_cases h : a = b
  · subst h
    simp only [↓reduceIte]
    congr 1
    funext p
    split_ifs <;> simp
  · simp only [h, ↓reduceIte]
    rw [← Matrix.diagonal_zero]
    congr 1
    funext p
    by_cases h1 : p.1 = a
    · simp [h1, h]
    · simp [h1]

/-- A product of three block projections vanishes unless the three blocks agree. -/
private lemma DysonBounds_Ea3 (D N : ℕ) (u v w : Fin D) :
    Ea D N u * Ea D N v * Ea D N w = 0 ∨ ∃ t, Ea D N u * Ea D N v * Ea D N w = Ea D N t := by
  rw [DysonBounds_Ea_mul]
  by_cases h : u = v
  · simp only [h, ↓reduceIte]
    rw [DysonBounds_Ea_mul]
    by_cases h2 : v = w
    · right
      exact ⟨v, by simp [h2]⟩
    · left
      simp [h2]
  · left
    simp [h]

/-- `D⟨E_a⟩ = 1`. -/
private lemma DysonBounds_ntr_Ea (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (a : Fin D) :
    (D : ℂ) * ntr (Ea D N a) = 1 := by
  unfold ntr Ea
  rw [Matrix.trace_diagonal]
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have : ∑ p : Idx D N, (if p.1 = a then (1 : ℂ) else 0) = N := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp
  rw [this]
  simp only [Fintype.card_prod, Fintype.card_fin]
  push_cast
  field_simp

/-- `D⟨M E_a⟩ = m` for every block, `D ≥ 1`, `N ≥ 1`, `z ∉ ℝ`. -/
private lemma DysonBounds_blk_M (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N)
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

/-- `|⟨X⟩| ≤ ‖X‖` on a nonempty index type. -/
private lemma DysonBounds_norm_ntr_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
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

/-- The operator norm of the identity is `1`. -/
private lemma DysonBounds_opNorm_one {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    opNorm (1 : Matrix ι ι ℂ) = 1 := by
  unfold opNorm
  rw [map_one, norm_one]

/-- The normalized trace is compatible with subtraction. -/
private lemma DysonBounds_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

/-- `⟨I⟩ = 1` on a nonempty index type. -/
private lemma DysonBounds_ntr_one {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ntr (1 : Matrix ι ι ℂ) = 1 := by
  have : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [ntr, Matrix.trace_one, this]

/-- `E_a E_b E_c = δ_{abc} E_a`. -/
private lemma DysonBounds_Ea3_eq (D N : ℕ) (a b c : Fin D) :
    Ea D N a * Ea D N b * Ea D N c = if a = b ∧ b = c then Ea D N a else 0 := by
  rw [DysonBounds_Ea_mul]
  by_cases h : a = b
  · subst h
    simp only [↓reduceIte, true_and]
    rw [DysonBounds_Ea_mul]
  · simp [h]

/-- The expansion of `E_a M E_b M E_c M` for `M = m I + Δ`. -/
private lemma DysonBounds_expand {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℂ)
    (E1 E2 E3 Δ : Matrix ι ι ℂ) :
    E1 * (m • (1 : Matrix ι ι ℂ) + Δ) * E2 * (m • (1 : Matrix ι ι ℂ) + Δ) * E3 *
        (m • (1 : Matrix ι ι ℂ) + Δ) =
      m ^ 3 • (E1 * E2 * E3) +
      m ^ 2 • (E1 * Δ * (E2 * E3) + E1 * E2 * Δ * E3 + E1 * E2 * E3 * Δ) +
      m • (E1 * (Δ * E2 * Δ * E3) + E1 * (Δ * E2 * E3 * Δ) + E1 * (E2 * Δ * E3 * Δ)) +
      E1 * (Δ * E2 * Δ * E3 * Δ) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
    smul_add, smul_smul, Matrix.mul_assoc]
  module

/-- `|D⟨E_a W⟩| ≤ ‖W‖`. -/
private lemma DysonBounds_blk_opNorm (D N : ℕ) (a : Fin D) (W : Matrix (Idx D N) (Idx D N) ℂ) :
    ‖(D : ℂ) * ntr (Ea D N a * W)‖ ≤ opNorm W :=
  DysonBounds_blk_le D N a W _ (DysonBounds_opNorm_nonneg W)
    (fun p => norm_apply_le_opNorm W p p)

/-- `q_{abc} = m³ δ_{abc} + O(‖Λ‖²)`: for `Λ = lam D N A` with `‖Λ‖ ≤ 1/10` and `Im z > 0`,
`|q_{abc} - m³ δ_{abc}| ≤ 26 ‖Λ‖²`. -/
theorem qTensor_sub_le (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hΛ : opNorm (lam D N A) ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (a b c : Fin D) :
    ‖qTensor (lam D N A) z a b c - (if a = b ∧ b = c then mExt (lam D N A) z ^ 3 else 0)‖ ≤
      26 * opNorm (lam D N A) ^ 2 := by
  have hD : 0 < D := a.pos
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hΛh := lam_isHermitian D N A
  obtain ⟨hw, hm1, hMn⟩ := mSol_apriori (lam D N A) hΛh hΛ z hz
  obtain ⟨hmim, hmtr, hspec⟩ := mSol_spec (lam D N A) hΛh z hz
  have he1 : mExt (lam D N A) z = mSol (lam D N A) z := by simp [mExt, hz]
  have he2 : MExt (lam D N A) z = MSol (lam D N A) z := by simp [MExt, MSol, he1]
  have hblk := DysonBounds_blk_M D N hD hN A z hz.ne'
  simp only [qTensor]
  rw [he1, he2]
  rw [he1, he2] at hblk
  set Λ := lam D N A with hΛdef
  set m := mSol Λ z with hmdef
  set M := MSol Λ z with hMdef
  set ℓ := opNorm Λ with hℓdef
  have hℓ0 : 0 ≤ ℓ := DysonBounds_opNorm_nonneg Λ
  have hMinv : M * (Λ - (z + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) = 1 :=
    mul_eq_one_comm.mp hspec
  have hMΛ : M * Λ - (z + m) • M = 1 := by
    simpa [Matrix.mul_sub, Matrix.mul_smul] using hMinv
  have hwM : (z + m) • M = M * Λ - 1 := by
    rw [← hMΛ]
    abel
  have hwm : (z + m) * m = ntr (M * Λ) - 1 := by
    have := congrArg ntr hwM
    rw [DysonBounds_ntr_smul, DysonBounds_ntr_sub, DysonBounds_ntr_one, ← hmtr] at this
    exact this
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : Matrix (Idx D N) (Idx D N) ℂ, Δ = M - m • 1 := ⟨_, rfl⟩
  have hMΔ : M = m • 1 + Δ := by rw [hΔdef]; abel
  have hΔ : (z + m) • Δ = M * Λ - ntr (M * Λ) • 1 := by
    rw [hΔdef, smul_sub, hwM, smul_smul, hwm, sub_smul, one_smul]
    abel
  -- the norm of Δ
  have hM54 : opNorm M ≤ 5 / 4 := by
    have h1 : (1 - 2 * ℓ)⁻¹ ≤ (4 / 5 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) (by linarith)
    have : opNorm M < (1 - 2 * ℓ)⁻¹ := hMn
    norm_num at h1
    linarith
  have hw910 : 9 / 10 ≤ ‖z + m‖ := by linarith
  have hM0 : 0 ≤ opNorm M := DysonBounds_opNorm_nonneg M
  have hδ0 : 0 ≤ opNorm Δ := DysonBounds_opNorm_nonneg Δ
  have hδ : ‖z + m‖ * opNorm Δ ≤ 2 * (opNorm M * ℓ) := by
    rw [← opNorm_smul, hΔ]
    refine (DysonBounds_opNorm_sub_le _ _).trans ?_
    rw [opNorm_smul, DysonBounds_opNorm_one, mul_one]
    have h1 : opNorm (M * Λ) ≤ opNorm M * ℓ := opNorm_mul_le M Λ
    have h2 : ‖ntr (M * Λ)‖ ≤ opNorm (M * Λ) := DysonBounds_norm_ntr_le _
    linarith
  have hδle : opNorm Δ ≤ 25 / 9 * ℓ := by
    have : opNorm M * ℓ ≤ 5 / 4 * ℓ := by gcongr
    nlinarith
  have hδ518 : opNorm Δ ≤ 5 / 18 := by linarith
  -- block traces of Δ vanish
  have hlin : ∀ x : Fin D, (D : ℂ) * ntr (Ea D N x * Δ) = 0 := by
    intro x
    rw [hΔdef, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, DysonBounds_ntr_sub,
      DysonBounds_ntr_smul, mul_sub, DysonBounds_ntr_comm, hblk x, mul_left_comm,
      DysonBounds_ntr_Ea D N hD hN x, mul_one, sub_self]
  have hlin3 : ∀ u v w : Fin D, (D : ℂ) * ntr (Ea D N u * Ea D N v * Ea D N w * Δ) = 0 := by
    intro u v w
    rcases DysonBounds_Ea3 D N u v w with h | ⟨t, h⟩
    · rw [h, Matrix.zero_mul]
      simp [ntr, Matrix.trace]
    · rw [h]
      exact hlin t
  -- the expansion of `q`
  have hEa := DysonBounds_opNorm_Ea D N a
  have hEb := DysonBounds_opNorm_Ea D N b
  have hEc := DysonBounds_opNorm_Ea D N c
  have hJ := DysonBounds_expand m (Ea D N a) (Ea D N b) (Ea D N c) Δ
  rw [← hMΔ] at hJ
  have l0 : (D : ℂ) * ntr (Ea D N a * Ea D N b * Ea D N c) = if a = b ∧ b = c then 1 else 0 := by
    rw [DysonBounds_Ea3_eq]
    split_ifs with h
    · exact DysonBounds_ntr_Ea D N hD hN a
    · simp [ntr, Matrix.trace]
  have l1 : (D : ℂ) * ntr (Ea D N a * Δ * (Ea D N b * Ea D N c)) = 0 := by
    rw [DysonBounds_ntr_comm]
    have := hlin3 b c a
    simpa only [Matrix.mul_assoc] using this
  have l2 : (D : ℂ) * ntr (Ea D N a * Ea D N b * Δ * Ea D N c) = 0 := by
    rw [DysonBounds_ntr_comm]
    have := hlin3 c a b
    simpa only [Matrix.mul_assoc] using this
  have l3 : (D : ℂ) * ntr (Ea D N a * Ea D N b * Ea D N c * Δ) = 0 := hlin3 a b c
  have hite : m ^ 3 * (if a = b ∧ b = c then (1 : ℂ) else 0) =
      if a = b ∧ b = c then m ^ 3 else 0 := by
    split_ifs <;> simp
  have hq : (D : ℂ) * ntr (Ea D N a * M * Ea D N b * M * Ea D N c * M) -
      (if a = b ∧ b = c then m ^ 3 else 0) =
      m * ((D : ℂ) * ntr (Ea D N a * (Δ * Ea D N b * Δ * Ea D N c)) +
        (D : ℂ) * ntr (Ea D N a * (Δ * Ea D N b * Ea D N c * Δ)) +
        (D : ℂ) * ntr (Ea D N a * (Ea D N b * Δ * Ea D N c * Δ))) +
      (D : ℂ) * ntr (Ea D N a * (Δ * Ea D N b * Δ * Ea D N c * Δ)) := by
    rw [hJ]
    simp only [DysonBounds_ntr_add, DysonBounds_ntr_smul]
    linear_combination (m ^ 3) * l0 + m ^ 2 * (l1 + l2 + l3) + hite
  have hδ1 : opNorm Δ ≤ opNorm Δ := le_rfl
  have n1 : ‖(D : ℂ) * ntr (Ea D N a * (Δ * Ea D N b * Δ * Ea D N c))‖ ≤ opNorm Δ ^ 2 := by
    refine (DysonBounds_blk_opNorm D N a _).trans ?_
    have := DysonBounds_opNorm_mul_le (DysonBounds_opNorm_mul_le
      (DysonBounds_opNorm_mul_le hδ1 hEb) hδ1) hEc
    exact this.trans (le_of_eq (by ring))
  have n2 : ‖(D : ℂ) * ntr (Ea D N a * (Δ * Ea D N b * Ea D N c * Δ))‖ ≤ opNorm Δ ^ 2 := by
    refine (DysonBounds_blk_opNorm D N a _).trans ?_
    have := DysonBounds_opNorm_mul_le (DysonBounds_opNorm_mul_le
      (DysonBounds_opNorm_mul_le hδ1 hEb) hEc) hδ1
    exact this.trans (le_of_eq (by ring))
  have n3 : ‖(D : ℂ) * ntr (Ea D N a * (Ea D N b * Δ * Ea D N c * Δ))‖ ≤ opNorm Δ ^ 2 := by
    refine (DysonBounds_blk_opNorm D N a _).trans ?_
    have := DysonBounds_opNorm_mul_le (DysonBounds_opNorm_mul_le
      (DysonBounds_opNorm_mul_le hEb hδ1) hEc) hδ1
    exact this.trans (le_of_eq (by ring))
  have n4 : ‖(D : ℂ) * ntr (Ea D N a * (Δ * Ea D N b * Δ * Ea D N c * Δ))‖ ≤ opNorm Δ ^ 3 := by
    refine (DysonBounds_blk_opNorm D N a _).trans ?_
    have := DysonBounds_opNorm_mul_le (DysonBounds_opNorm_mul_le (DysonBounds_opNorm_mul_le
      (DysonBounds_opNorm_mul_le hδ1 hEb) hδ1) hEc) hδ1
    exact this.trans (le_of_eq (by ring))
  rw [hq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hs : ‖(D : ℂ) * ntr (Ea D N a * (Δ * Ea D N b * Δ * Ea D N c)) +
      (D : ℂ) * ntr (Ea D N a * (Δ * Ea D N b * Ea D N c * Δ)) +
      (D : ℂ) * ntr (Ea D N a * (Ea D N b * Δ * Ea D N c * Δ))‖ ≤ 3 * opNorm Δ ^ 2 :=
    ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans (by linarith)
  have hm1' : ‖m‖ ≤ 1 := hm1.le
  have h2 : opNorm Δ ^ 2 ≤ (25 / 9 * ℓ) ^ 2 := pow_le_pow_left₀ hδ0 hδle 2
  have h3 : opNorm Δ ^ 3 ≤ opNorm Δ ^ 2 * (5 / 18) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left hδ518 (by positivity)
  calc ‖m‖ * ‖(D : ℂ) * ntr (Ea D N a * (Δ * Ea D N b * Δ * Ea D N c)) +
      (D : ℂ) * ntr (Ea D N a * (Δ * Ea D N b * Ea D N c * Δ)) +
      (D : ℂ) * ntr (Ea D N a * (Ea D N b * Δ * Ea D N c * Δ))‖ +
      ‖(D : ℂ) * ntr (Ea D N a * (Δ * Ea D N b * Δ * Ea D N c * Δ))‖
      ≤ 1 * (3 * opNorm Δ ^ 2) + opNorm Δ ^ 2 * (5 / 18) := by
        exact add_le_add (mul_le_mul hm1' hs (norm_nonneg _) zero_le_one) (n4.trans h3)
    _ ≤ 26 * ℓ ^ 2 := by nlinarith [sq_nonneg ℓ]

/-- `‖M(z)‖ ≤ (Im z)⁻¹` for Hermitian `Λ` and `Im z > 0`. -/
private lemma DysonBounds_opNorm_M {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    opNorm (MExt Λ z) ≤ z.im⁻¹ := by
  have e1 : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  have hm := (mSol_spec Λ hΛ z hz).1
  have hzm : 0 < (z + mExt Λ z).im := by rw [Complex.add_im, e1]; linarith
  have h := opNorm_res_le Λ hΛ (z + mExt Λ z) hzm
  have e2 : MExt Λ z = res Λ (z + mExt Λ z) := rfl
  rw [e2]
  refine h.trans ?_
  rw [Complex.add_im, e1]
  exact inv_anti₀ hz (by linarith)

/-- `Σ_b y_b E_b` is the diagonal matrix whose entry at `p` is `y_a` for the block `a` of `p`. -/
private lemma DysonBounds_sum_Ea (D N : ℕ) (y : Fin D → ℂ) :
    ∑ b, y b • Ea D N b = Matrix.diagonal (fun p : Idx D N => y p.1) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Ea, Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : p = q
  · subst h
    simp
  · simp [h]

open scoped Matrix.Norms.L2Operator in
/-- The operator norm of a diagonal matrix is the sup norm of its diagonal. -/
private lemma DysonBounds_opNorm_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    opNorm (Matrix.diagonal v) = ‖v‖ := by
  unfold opNorm
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]

/-- The contraction for `Im z ≥ 2`: for every Hermitian `H`, `Λ = lam D N A` and `0 ≤ θ ≤ 1`,
the block traces of `G - M` satisfy `max_a |x_a| ≤ (4/3) max_a |r_a|`, `r_a = -D⟨E_a M H̲G⟩`. -/
theorem blockTr_contraction (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (A : Matrix (Fin N) (Fin N) ℂ) (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 2 ≤ z.im) :
    ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤
      4 / 3 * ‖rVec D N θ H (lam D N A) z‖ := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => a.elim0
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hE : IsEmpty (Idx D 0) := ⟨fun p => p.2.elim0⟩
    have hx : blockTr D 0 (res (H + lam D 0 A) z - MExt (lam D 0 A) z) = 0 := by
      funext a
      simp [blockTr, DysonBounds_ntr_of_isEmpty]
    rw [hx, norm_zero]
    positivity
  have : Nonempty (Idx D N) := ⟨(⟨0, hD⟩, ⟨0, hN⟩)⟩
  have hη : 0 < z.im := by linarith
  have hid := hgUnder_identity D N θ A H hH z hη
  rw [sTheta_blockTr] at hid
  have hΛh := lam_isHermitian D N A
  have hMn := DysonBounds_opNorm_M (lam D N A) hΛh z hη
  have hGn := opNorm_res_le (H + lam D N A) (hH.add hΛh) z hη
  set Λ := lam D N A with hΛdef
  set M := MExt Λ z with hMdef
  set G := res (H + Λ) z with hGdef
  set X := G - M with hXdef
  set U := hgUnder D N θ H Λ z with hUdef
  set x := blockTr D N X with hxdef
  set y := sigTheta D θ *ᵥ x with hydef
  set r := rVec D N θ H Λ z with hrdef
  have hη2 : z.im⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hz
  have hη0 : 0 ≤ z.im⁻¹ := inv_nonneg.mpr hη.le
  have hYn : opNorm (∑ b, y b • Ea D N b) ≤ ‖x‖ := by
    rw [DysonBounds_sum_Ea, DysonBounds_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun p =>
      DysonBounds_sig_linf D θ hθ0 hθ1 x p.1
  have key : ∀ a : Fin D, ‖x a‖ ≤ ‖r‖ + 1 / 4 * ‖x‖ := by
    intro a
    have hxa : x a = r a + (D : ℂ) * ntr (Ea D N a * (M * (∑ b, y b • Ea D N b) * G)) := by
      have h1 : x a = (D : ℂ) * ntr (Ea D N a * X) := rfl
      have h2 : r a = -((D : ℂ) * ntr (Ea D N a * M * U)) := rfl
      rw [h1, h2]
      conv_lhs => rw [hid]
      rw [Matrix.mul_add, Matrix.mul_neg, DysonBounds_ntr_add, DysonBounds_ntr_neg, mul_add,
        mul_neg, ← Matrix.mul_assoc (Ea D N a) M U]
    rw [hxa]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add (norm_le_pi_norm r a) ?_
    refine (DysonBounds_blk_opNorm D N a _).trans ?_
    have h3 := DysonBounds_opNorm_mul_le (DysonBounds_opNorm_mul_le hMn hYn) hGn
    refine h3.trans ?_
    have h4 : z.im⁻¹ * ‖x‖ * z.im⁻¹ = ‖x‖ * (z.im⁻¹ * z.im⁻¹) := by ring
    rw [h4]
    have h5 : z.im⁻¹ * z.im⁻¹ ≤ 1 / 4 := by nlinarith
    nlinarith [norm_nonneg x]
  have hx := (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ‖r‖ + 1 / 4 * ‖x‖)).mpr key
  linarith

open scoped Matrix.Norms.L2Operator in
/-- The operator norm is invariant under the conjugate transpose. -/
private lemma DysonBounds_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) : opNorm Xᴴ = opNorm X := by
  unfold opNorm
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_toEuclideanCLM,
    Matrix.l2_opNorm_conjTranspose]

/-- If `B M = 1` and `‖B‖ ≤ K` then `n ≤ K² ‖M‖_HS²`: the Hilbert–Schmidt form of
`⟨M M^*⟩ ≥ ‖B‖⁻²`. -/
private lemma DysonBounds_inv_hs {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B M : Matrix ι ι ℂ) (hBM : B * M = 1) (K : ℝ) (hK : opNorm B ≤ K) :
    (Fintype.card ι : ℝ) ≤ K ^ 2 * ∑ j, ∑ k, ‖M j k‖ ^ 2 := by
  have hB0 : 0 ≤ opNorm B := DysonBounds_opNorm_nonneg B
  have hrow : ∀ j, ∑ k, ‖B j k‖ ^ 2 ≤ K ^ 2 := by
    intro j
    have h1 : (B * Bᴴ) j j = ((∑ k, ‖B j k‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    have h2 : ‖(B * Bᴴ) j j‖ ≤ opNorm (B * Bᴴ) := norm_apply_le_opNorm _ j j
    have h3 : opNorm (B * Bᴴ) ≤ opNorm B * opNorm Bᴴ := opNorm_mul_le _ _
    rw [DysonBounds_opNorm_conjTranspose] at h3
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h2
    nlinarith
  have hcol : ∀ j, 1 ≤ K ^ 2 * ∑ k, ‖M k j‖ ^ 2 := by
    intro j
    have h1 : (B * M) j j = 1 := by rw [hBM]; simp
    rw [Matrix.mul_apply] at h1
    have h2 : (1 : ℝ) ≤ ∑ k, ‖B j k‖ * ‖M k j‖ := by
      calc (1 : ℝ) = ‖∑ k, B j k * M k j‖ := by rw [h1]; simp
        _ ≤ ∑ k, ‖B j k * M k j‖ := norm_sum_le _ _
        _ = _ := by simp
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖B j k‖) (fun k => ‖M k j‖)
    have h4 : 0 ≤ ∑ k, ‖M k j‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
    have h5 : 0 ≤ ∑ k, ‖B j k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
    nlinarith [hrow j]
  calc (Fintype.card ι : ℝ) = ∑ _j : ι, (1 : ℝ) := by simp
    _ ≤ ∑ j, K ^ 2 * ∑ k, ‖M k j‖ ^ 2 := Finset.sum_le_sum fun j _ => hcol j
    _ = K ^ 2 * ∑ j, ∑ k, ‖M k j‖ ^ 2 := by rw [← Finset.mul_sum]
    _ = K ^ 2 * ∑ j, ∑ k, ‖M j k‖ ^ 2 := by rw [Finset.sum_comm]

/-- `⟨M M^*⟩ = n⁻¹ ‖M‖_HS²`. -/
private lemma DysonBounds_ntr_mul_conjTranspose {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) :
    ntr (M * Mᴴ) = (((Fintype.card ι : ℝ)⁻¹ * ∑ j, ∑ k, ‖M j k‖ ^ 2 : ℝ) : ℂ) := by
  unfold ntr Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- `star s ⬝ᵥ (M^* s) = conj (star s ⬝ᵥ (M s))`. -/
private lemma DysonBounds_dot_conj {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ)
    (s : ι → ℂ) : star s ⬝ᵥ (Mᴴ *ᵥ s) = star (star s ⬝ᵥ (M *ᵥ s)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply, star_sum,
    star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `|s^* X s| ≤ ‖X‖ |s|²`. -/
private lemma DysonBounds_bilin_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (s : ι → ℂ) : ‖star s ⬝ᵥ (X *ᵥ s)‖ ≤ opNorm X * ∑ i, ‖s i‖ ^ 2 := by
  have e : star s ⬝ᵥ (X *ᵥ s) =
      inner ℂ (WithLp.toLp 2 s) (Matrix.toEuclideanLin X (WithLp.toLp 2 s)) := by
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
  have hs' : ‖(WithLp.toLp 2 s : EuclideanSpace ℂ ι)‖ ^ 2 = ∑ i, ‖s i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  have h1 : Matrix.toEuclideanLin X (WithLp.toLp 2 s) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) X (WithLp.toLp 2 s) := rfl
  rw [e, h1, ← hs']
  calc ‖inner ℂ (WithLp.toLp 2 s) (Matrix.toEuclideanCLM (𝕜 := ℂ) X (WithLp.toLp 2 s))‖
      ≤ ‖(WithLp.toLp 2 s : EuclideanSpace ℂ ι)‖ *
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X (WithLp.toLp 2 s)‖ := norm_inner_le_norm _ _
    _ ≤ ‖(WithLp.toLp 2 s : EuclideanSpace ℂ ι)‖ *
          (‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ * ‖(WithLp.toLp 2 s : EuclideanSpace ℂ ι)‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = opNorm X * ‖(WithLp.toLp 2 s : EuclideanSpace ℂ ι)‖ ^ 2 := by rw [opNorm]; ring

/-- A priori facts behind the Ward bounds (2.32) [eq_Ward], for `‖Λ‖ ≤ 1/10`, `Im z > 0` and
`|z| ≤ τ⁻¹`: `η ≤ (11/10 + τ⁻¹)² Im m`, from `⟨M M^*⟩ = Im m / (Im m + η)` of (A.3)
[equation_z_im_m], and `Im(s^* M s) ≤ (25/16)(η + Im m)|s|²` for every `s`. -/
theorem im_mSol_lower {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (τ : ℝ) (hτ : 0 < τ) (z : ℂ) (hz : 0 < z.im)
    (hzτ : ‖z‖ ≤ τ⁻¹) :
    z.im ≤ (11 / 10 + τ⁻¹) ^ 2 * (mSol Λ z).im ∧
      ∀ s : ι → ℂ, (star s ⬝ᵥ (MSol Λ z *ᵥ s)).im ≤
        25 / 16 * (z.im + (mSol Λ z).im) * ∑ i, ‖s i‖ ^ 2 := by
  obtain ⟨hw, hm1, hMn⟩ := mSol_apriori Λ hΛ hℓ z hz
  obtain ⟨hmim, hmtr, hspec⟩ := mSol_spec Λ hΛ z hz
  obtain ⟨hA3a, hA3b⟩ := equation_z_im_m Λ hΛ z hz
  set m := mSol Λ z with hmdef
  set M := MSol Λ z with hMdef
  set ℓ := opNorm Λ with hℓdef
  have hℓ0 : 0 ≤ ℓ := DysonBounds_opNorm_nonneg Λ
  have hM54 : opNorm M ≤ 5 / 4 := by
    have h1 : (1 - 2 * ℓ)⁻¹ ≤ (4 / 5 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) (by linarith)
    have : opNorm M < (1 - 2 * ℓ)⁻¹ := hMn
    norm_num at h1
    linarith
  refine ⟨?_, ?_⟩
  · set K : ℝ := 11 / 10 + τ⁻¹ with hK
    have hBK : opNorm (Λ - (z + m) • (1 : Matrix ι ι ℂ)) ≤ K := by
      refine (DysonBounds_opNorm_sub_le _ _).trans ?_
      rw [opNorm_smul, DysonBounds_opNorm_one, mul_one]
      have : ‖z + m‖ ≤ ‖z‖ + ‖m‖ := norm_add_le _ _
      linarith
    have hhs := DysonBounds_inv_hs _ M hspec K hBK
    have hn := DysonBounds_ntr_mul_conjTranspose M
    rw [hA3a] at hn
    have hr : m.im / (m.im + z.im) =
        (Fintype.card ι : ℝ)⁻¹ * ∑ j, ∑ k, ‖M j k‖ ^ 2 := by exact_mod_cast hn
    have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hden : 0 < m.im + z.im := by linarith
    have hr1 : 1 ≤ K ^ 2 * (m.im / (m.im + z.im)) := by
      rw [hr, ← mul_assoc, mul_comm (K ^ 2), mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hc,
        one_mul]
      exact hhs
    rw [← mul_div_assoc, le_div_iff₀ hden, one_mul] at hr1
    linarith
  · intro s
    set q := star s ⬝ᵥ (M *ᵥ s) with hq
    set R := star s ⬝ᵥ ((M * Mᴴ) *ᵥ s) with hR
    have h1 : star s ⬝ᵥ ((M - Mᴴ) *ᵥ s) =
        (2 * Complex.I * ((z.im + m.im : ℝ) : ℂ)) * R := by
      rw [hA3b, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have h2 : star s ⬝ᵥ ((M - Mᴴ) *ᵥ s) = q - star q := by
      rw [Matrix.sub_mulVec, dotProduct_sub, DysonBounds_dot_conj]
    have h3 : q - star q = ((2 * q.im : ℝ) : ℂ) * Complex.I := Complex.sub_conj q
    have h4 : (q.im : ℂ) = ((z.im + m.im : ℝ) : ℂ) * R := by
      have h5 : ((2 * q.im : ℝ) : ℂ) * Complex.I =
          (2 * Complex.I * ((z.im + m.im : ℝ) : ℂ)) * R := by rw [← h3, ← h2, h1]
      apply mul_left_cancel₀ (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      push_cast at h5 ⊢
      linear_combination h5
    have h6 : |q.im| = (z.im + m.im) * ‖R‖ := by
      have := congrArg norm h4
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ z.im + m.im by linarith)] at this
      exact this
    have h7 : ‖R‖ ≤ 25 / 16 * ∑ i, ‖s i‖ ^ 2 := by
      refine (DysonBounds_bilin_le (M * Mᴴ) s).trans ?_
      have h8 : opNorm (M * Mᴴ) ≤ 25 / 16 := by
        have := DysonBounds_opNorm_mul_le hM54 (le_of_eq (DysonBounds_opNorm_conjTranspose M)
          |>.trans hM54)
        exact this.trans (le_of_eq (by norm_num))
      gcongr
    calc q.im ≤ |q.im| := le_abs_self _
      _ = (z.im + m.im) * ‖R‖ := h6
      _ ≤ (z.im + m.im) * (25 / 16 * ∑ i, ‖s i‖ ^ 2) := by
          gcongr
      _ = 25 / 16 * (z.im + m.im) * ∑ i, ‖s i‖ ^ 2 := by ring

end RBMTransitionEdge

end
