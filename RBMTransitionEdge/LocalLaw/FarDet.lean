module

public import RBMTransitionEdge.LocalLaw.BootstrapDet

@[expose] public section

/-!
# Deterministic inputs far from the spectrum

Bounds on `Λ`, the block traces, `M`, `R_y` and the equation for the block traces for
`4 ≤ |Re z|`, used in the far region of Lemma 2.9 [lem_loc].
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

section Lam

set_option linter.unusedSectionVars false

/-- The Euclidean norm of a vector. -/
private def FarDet_vn {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖

private lemma FarDet_vn_nonneg {ι : Type*} [Fintype ι] (x : ι → ℂ) : 0 ≤ FarDet_vn x :=
  norm_nonneg _

private lemma FarDet_vn_sq {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    FarDet_vn x ^ 2 = ∑ p, ‖x p‖ ^ 2 := by
  unfold FarDet_vn
  rw [EuclideanSpace.norm_sq_eq]

private lemma FarDet_vn_zero {ι : Type*} [Fintype ι] : FarDet_vn (0 : ι → ℂ) = 0 := by
  simp [FarDet_vn]

private lemma FarDet_vn_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (x : ι → ℂ) : FarDet_vn (A *ᵥ x) ≤ opNorm A * FarDet_vn x := by
  unfold FarDet_vn opNorm
  have h := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 x)
  rwa [Matrix.toEuclideanCLM_toLp] at h

private lemma FarDet_opNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    0 ≤ opNorm A := norm_nonneg _

private lemma FarDet_opNorm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) A)

/-- `opNorm` bound from the quadratic bound on vectors. -/
private lemma FarDet_opNorm_le {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x : ι → ℂ, FarDet_vn (A *ᵥ x) ≤ c * FarDet_vn x) : opNorm A ≤ c := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have := h x.ofLp
  unfold FarDet_vn at this
  have hx : x = WithLp.toLp 2 x.ofLp := rfl
  rw [hx, Matrix.toEuclideanCLM_toLp]
  simpa using this


private lemma FarDet_fwd_functional {D : ℕ} {a b b' : Fin D} (h : fwd D a b) (h' : fwd D a b') :
    b = b' := by
  unfold fwd at h h'
  apply Fin.ext
  omega

private lemma FarDet_fwd_injective {D : ℕ} {a a' b : Fin D} (h : fwd D a b) (h' : fwd D a' b) :
    a = a' := by
  unfold fwd at h h'
  apply Fin.ext
  omega

/-- The block-upper part of `lam D N A`. -/
private def FarDet_S1 (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  fun p q => if fwd D p.1 q.1 then A p.2 q.2 else 0

private lemma FarDet_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = FarDet_S1 D N A + (FarDet_S1 D N A)ᴴ := by
  ext p q
  by_cases h : fwd D q.1 p.1 <;> simp [lam, FarDet_S1, Matrix.conjTranspose_apply, h]

/-- A sum over `b` with at most one nonzero term. -/
private lemma FarDet_sum_ite_sq {D N : ℕ} (a : Fin D) (f : Fin D → Fin N → ℂ) :
    FarDet_vn (∑ b, (if fwd D a b then f b else 0)) ^ 2 =
      ∑ b, (if fwd D a b then FarDet_vn (f b) ^ 2 else 0) := by
  by_cases h : ∃ b₀, fwd D a b₀
  · obtain ⟨b₀, hb₀⟩ := h
    rw [Finset.sum_eq_single b₀, Finset.sum_eq_single b₀]
    · simp [hb₀]
    · intro b _ hb
      have : ¬ fwd D a b := fun h' => hb (FarDet_fwd_functional h' hb₀)
      simp [this]
    · simp
    · intro b _ hb
      have : ¬ fwd D a b := fun h' => hb (FarDet_fwd_functional h' hb₀)
      simp [this]
    · simp
  · have h' : ∀ b, ¬ fwd D a b := fun b hb => h ⟨b, hb⟩
    simp [h', FarDet_vn_zero]

private lemma FarDet_sum_ite_le {D : ℕ} (b : Fin D) (g : ℝ) (hg : 0 ≤ g) :
    ∑ a, (if fwd D a b then g else 0) ≤ g := by
  by_cases h : ∃ a₀, fwd D a₀ b
  · obtain ⟨a₀, ha₀⟩ := h
    rw [Finset.sum_eq_single a₀]
    · simp [ha₀]
    · intro a _ ha
      have : ¬ fwd D a b := fun h' => ha (FarDet_fwd_injective h' ha₀)
      simp [this]
    · simp
  · have h' : ∀ a, ¬ fwd D a b := fun a ha => h ⟨a, ha⟩
    simp [h', hg]

private lemma FarDet_S1_norm (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (FarDet_S1 D N A) ≤ opNorm A := by
  refine FarDet_opNorm_le (FarDet_opNorm_nonneg A) fun x => ?_
  set xb : Fin D → Fin N → ℂ := fun b j => x (b, j) with hxb
  have h1 : ∀ (a : Fin D) (i : Fin N), (FarDet_S1 D N A *ᵥ x) (a, i) =
      ∑ b, (if fwd D a b then (A *ᵥ xb b) i else 0) := by
    intro a i
    simp only [Matrix.mulVec, dotProduct, FarDet_S1, Fintype.sum_prod_type, hxb]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · simp
    · simp
  have h2 : ∀ a : Fin D, ∑ i, ‖(FarDet_S1 D N A *ᵥ x) (a, i)‖ ^ 2 =
      ∑ b, (if fwd D a b then FarDet_vn (A *ᵥ xb b) ^ 2 else 0) := by
    intro a
    have := FarDet_sum_ite_sq a (fun b => A *ᵥ xb b)
    rw [← this, FarDet_vn_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 a i, Finset.sum_apply]
    congr 2
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have h3 : FarDet_vn (FarDet_S1 D N A *ᵥ x) ^ 2 ≤ (opNorm A * FarDet_vn x) ^ 2 := by
    rw [FarDet_vn_sq, Fintype.sum_prod_type]
    simp only [h2]
    rw [Finset.sum_comm]
    calc ∑ b, ∑ a, (if fwd D a b then FarDet_vn (A *ᵥ xb b) ^ 2 else 0)
        ≤ ∑ b, FarDet_vn (A *ᵥ xb b) ^ 2 :=
          Finset.sum_le_sum fun b _ => FarDet_sum_ite_le b _ (sq_nonneg _)
      _ ≤ ∑ b, (opNorm A * FarDet_vn (xb b)) ^ 2 :=
          Finset.sum_le_sum fun b _ =>
            pow_le_pow_left₀ (FarDet_vn_nonneg _) (FarDet_vn_mulVec_le _ _) 2
      _ = (opNorm A) ^ 2 * ∑ b, FarDet_vn (xb b) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => mul_pow _ _ _
      _ = (opNorm A * FarDet_vn x) ^ 2 := by
          rw [mul_pow, FarDet_vn_sq x, Fintype.sum_prod_type]
          congr 1
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [FarDet_vn_sq]
  exact (abs_le_of_sq_le_sq h3 (mul_nonneg (FarDet_opNorm_nonneg A)
    (FarDet_vn_nonneg _))).trans' (le_abs_self _)

end Lam

/-- The interaction `Λ` of (1.3) [matrix_H] has `‖Λ‖ ≤ 2‖A‖`: it is `0` for `D = 1`, the block
matrix `[[0, A], [A*, 0]]` for `D = 2`, and `S ⊗ A + S* ⊗ A*` with the cyclic shift `S` for
`D ≥ 3`. -/
theorem opNorm_lam_le (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * opNorm A := by
  rw [FarDet_lam_eq]
  refine (opNorm_add_le _ _).trans ?_
  rw [FarDet_opNorm_conjTranspose]
  have := FarDet_S1_norm D N A
  linarith

/-- The normalized trace on an empty index type vanishes. -/
private lemma FarDet_ntr_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (B : Matrix ι ι ℂ) :
    ntr B = 0 := by
  simp [ntr, Matrix.trace]

/-- On an empty index type every operator norm vanishes. -/
private lemma FarDet_opNorm_of_isEmpty {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (X : Matrix ι ι ℂ) : opNorm X = 0 := by
  have h : X = 0 := by
    ext p
    exact (IsEmpty.false p).elim
  rw [h]
  unfold opNorm
  rw [map_zero, norm_zero]

/-- The normalized trace of a difference is the difference of the normalized traces. -/
private lemma FarDet_ntr_sub {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P - Q) = ntr P - ntr Q := by
  simp [ntr, Matrix.trace_sub, mul_sub]

/-- The normalized trace of a finite sum is the sum of the normalized traces. -/
private lemma FarDet_ntr_sum {ι κ : Type*} [Fintype ι] (s : Finset κ)
    (P : κ → Matrix ι ι ℂ) : ntr (∑ b ∈ s, P b) = ∑ b ∈ s, ntr (P b) := by
  simp [ntr, Matrix.trace_sum, Finset.mul_sum]

/-- The normalized trace is cyclic: `⟨P Q⟩ = ⟨Q P⟩`. -/
private lemma FarDet_ntr_comm {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) :
    ntr (P * Q) = ntr (Q * P) := by
  simp [ntr, Matrix.trace_mul_comm P Q]

/-- `|D⟨E_a W⟩| ≤ B` when the diagonal entries of `W` are at most `B` in modulus. -/
private lemma FarDet_blk_le (D N : ℕ) (a : Fin D) (W : Matrix (Idx D N) (Idx D N) ℂ)
    (B : ℝ) (hB : 0 ≤ B) (h : ∀ p, ‖W p p‖ ≤ B) : ‖(D : ℂ) * ntr (Ea D N a * W)‖ ≤ B := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : IsEmpty (Idx D 0) := ⟨fun p => p.2.elim0⟩
    simp [FarDet_ntr_of_isEmpty, hB]
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
private lemma FarDet_blk_opNorm (D N : ℕ) (a : Fin D) (W : Matrix (Idx D N) (Idx D N) ℂ) :
    ‖(D : ℂ) * ntr (Ea D N a * W)‖ ≤ opNorm W :=
  FarDet_blk_le D N a W _ (FarDet_opNorm_nonneg W) (fun p => norm_apply_le_opNorm W p p)

/-- The block projections sum to the identity. -/
private lemma FarDet_sum_Ea_one (D N : ℕ) : ∑ a : Fin D, Ea D N a = 1 := by
  ext p q
  simp [Ea, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]

/-- The block traces are additive. -/
private lemma FarDet_blockTr_sub (D N : ℕ) (P Q : Matrix (Idx D N) (Idx D N) ℂ) :
    blockTr D N (P - Q) = blockTr D N P - blockTr D N Q := by
  funext a
  simp only [blockTr, Pi.sub_apply, Matrix.mul_sub, FarDet_ntr_sub]
  ring

/-- For `D ≥ 1`, `⟨B⟩ = D⁻¹ Σ_a D⟨E_a B⟩`. -/
private lemma FarDet_ntr_eq_blockTr (D N : ℕ) (hD : 1 ≤ D) (B : Matrix (Idx D N) (Idx D N) ℂ) :
    ntr B = (D : ℂ)⁻¹ * ∑ a, blockTr D N B a := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  unfold blockTr
  rw [← Finset.mul_sum, ← FarDet_ntr_sum, ← Finset.sum_mul, FarDet_sum_Ea_one, Matrix.one_mul]
  field_simp

/-- `|⟨B⟩| ≤ |D⟨E_a B⟩|_∞` for `D ≥ 1`. -/
private lemma FarDet_norm_ntr_le_blockTr (D N : ℕ) (hD : 1 ≤ D)
    (B : Matrix (Idx D N) (Idx D N) ℂ) : ‖ntr B‖ ≤ ‖blockTr D N B‖ := by
  rw [FarDet_ntr_eq_blockTr D N hD B, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ a, blockTr D N B a‖ ≤ D * ‖blockTr D N B‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖blockTr D N B a‖ ≤ ∑ _a : Fin D, ‖blockTr D N B‖ :=
          Finset.sum_le_sum fun a _ => norm_le_pi_norm (blockTr D N B) a
      _ = D * ‖blockTr D N B‖ := by simp
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  calc (D : ℝ)⁻¹ * ‖∑ a, blockTr D N B a‖ ≤ (D : ℝ)⁻¹ * (D * ‖blockTr D N B‖) := by gcongr
    _ = ‖blockTr D N B‖ := by field_simp

/-- The block traces have sup norm at most the operator norm: `|D⟨E_a B⟩| ≤ ‖B‖` for every
block `a`. -/
theorem blockTr_norm_le (D N : ℕ) (B : Matrix (Idx D N) (Idx D N) ℂ) :
    ‖blockTr D N B‖ ≤ opNorm B := by
  refine (pi_norm_le_iff_of_nonneg (FarDet_opNorm_nonneg B)).mpr fun a => ?_
  exact FarDet_blk_opNorm D N a B

/-- `|⟨R⟩| ≤ ‖R‖`. -/
private lemma FarDet_norm_ntr_le {ι : Type*} [Fintype ι] [DecidableEq ι] (R : Matrix ι ι ℂ) :
    ‖ntr R‖ ≤ opNorm R := by
  rcases isEmpty_or_nonempty ι with h | h
  · rw [FarDet_ntr_of_isEmpty, norm_zero]
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

/-- The operator norm of a difference. -/
private lemma FarDet_opNorm_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) : opNorm (X - Y) ≤ opNorm X + opNorm Y := by
  unfold opNorm
  rw [map_sub]
  exact norm_sub_le _ _

/-- `‖I‖ ≤ 1`. -/
private lemma FarDet_opNorm_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] :
    opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-- (2.17) [def_G0] far from the spectrum: for Hermitian `Λ` with `‖Λ‖ ≤ 1/10`, `Im z > 0` and
`|Re z| ≥ 4`, `M(z)` is a true inverse, `‖M(z)‖ ≤ 10/29` (since `|z + m| ≥ 3`), and
`Im m(z) ≤ Im z / 7` (from `⟨M M^*⟩ = Im m/(Im m + η)` of (A.3) [equation_z_im_m]). -/
theorem MExt_far {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (hE : 4 ≤ |z.re|) :
    (Λ - (z + mExt Λ z) • (1 : Matrix ι ι ℂ)) * MExt Λ z = 1 ∧
      opNorm (MExt Λ z) ≤ 10 / 29 ∧ (mExt Λ z).im ≤ z.im / 7 := by
  obtain ⟨-, hKM, hpos⟩ := MExt_spec Λ hΛ z hz.ne'
  obtain ⟨-, hm1, -⟩ := mSol_apriori Λ hΛ hℓ z hz
  have hm : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  have hMM : MExt Λ z = MSol Λ z := by simp [MExt, MSol, hm]
  have hw : 3 < ‖z + mExt Λ z‖ := by
    rw [hm]
    have h1 : |(mSol Λ z).re| ≤ ‖mSol Λ z‖ := Complex.abs_re_le_norm _
    have h2 : |(z + mSol Λ z).re| ≤ ‖z + mSol Λ z‖ := Complex.abs_re_le_norm _
    rw [Complex.add_re] at h2
    have h3 : |z.re| - |(mSol Λ z).re| ≤ |z.re + (mSol Λ z).re| := by
      rcases abs_cases z.re with ⟨h, _⟩ | ⟨h, _⟩ <;>
        rcases abs_cases (mSol Λ z).re with ⟨h', _⟩ | ⟨h', _⟩ <;>
        rcases abs_cases (z.re + (mSol Λ z).re) with ⟨h'', _⟩ | ⟨h'', _⟩ <;> linarith
    linarith
  have hM : opNorm (MExt Λ z) ≤ 10 / 29 := by
    have h1 : (z + mExt Λ z) • MExt Λ z = Λ * MExt Λ z - 1 := by
      have h0 := hKM
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h0
      rw [← h0]
      abel
    have h2 : ‖z + mExt Λ z‖ * opNorm (MExt Λ z) ≤ opNorm Λ * opNorm (MExt Λ z) + 1 := by
      rw [← opNorm_smul, h1]
      refine (FarDet_opNorm_sub_le _ _).trans ?_
      have := opNorm_mul_le Λ (MExt Λ z)
      have := FarDet_opNorm_one_le (ι := ι)
      linarith
    have hM0 := FarDet_opNorm_nonneg (MExt Λ z)
    nlinarith [mul_nonneg (show 0 ≤ ‖z + mExt Λ z‖ - opNorm Λ - 29 / 10 by linarith) hM0]
  refine ⟨hKM, hM, ?_⟩
  have hnt := (equation_z_im_m Λ hΛ z hz).1
  rw [← hMM, ← hm] at hnt
  have ha : 0 < (mExt Λ z).im := (mul_pos_iff_of_pos_right hz).mp hpos
  have hb : (mExt Λ z).im / ((mExt Λ z).im + z.im) ≤ (10 / 29) ^ 2 := by
    have h1 : ‖ntr (MExt Λ z * (MExt Λ z)ᴴ)‖ ≤ opNorm (MExt Λ z * (MExt Λ z)ᴴ) :=
      FarDet_norm_ntr_le _
    have h2 := opNorm_mul_le (MExt Λ z) (MExt Λ z)ᴴ
    rw [FarDet_opNorm_conjTranspose] at h2
    rw [hnt, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    have hM0 := FarDet_opNorm_nonneg (MExt Λ z)
    nlinarith
  rw [div_le_iff₀ (by positivity)] at hb
  linarith

/-- `Σ_b y_b E_b` is the diagonal matrix with entry `y_a` at every index of the block `a`. -/
private lemma FarDet_sum_Ea (D N : ℕ) (y : Fin D → ℂ) :
    ∑ b, y b • Ea D N b = Matrix.diagonal (fun p : Idx D N => y p.1) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Ea, Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : p = q
  · subst h
    simp
  · simp [h]

open scoped Matrix.Norms.L2Operator in
/-- The operator norm of a diagonal matrix is the sup norm of its diagonal. -/
private lemma FarDet_opNorm_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    opNorm (Matrix.diagonal v) = ‖v‖ := by
  unfold opNorm
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]

/-- A matrix `Y` bounded below by `c > 0` in the Euclidean norm satisfies `Y Y⁻¹ = 1` and
`‖Y⁻¹‖ ≤ c⁻¹`. -/
private lemma FarDet_inv {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) (c : ℝ)
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

/-- The operator norm of a product of matrices with bounded norms. -/
private lemma FarDet_opNorm_mul_le_of_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : Matrix ι ι ℂ} {x y : ℝ} (hX : opNorm X ≤ x) (hY : opNorm Y ≤ y) :
    opNorm (X * Y) ≤ x * y :=
  (opNorm_mul_le X Y).trans
    (mul_le_mul hX hY (FarDet_opNorm_nonneg Y) ((FarDet_opNorm_nonneg X).trans hX))

/-- `(σ_θ x)_a = θ x_a + (1 - θ) D⁻¹ Σ_b x_b`. -/
private lemma FarDet_sig_apply (D : ℕ) (θ : ℝ) (x : Fin D → ℂ) (a : Fin D) :
    (sigTheta D θ *ᵥ x) a =
      (θ : ℂ) * x a + ((1 - θ : ℝ) : ℂ) * ((D : ℂ)⁻¹ * ∑ b, x b) := by
  have hJ : (Matrix.of fun (_ _ : Fin D) => (1 : ℂ)) *ᵥ x = fun _ => ∑ b, x b := by
    ext
    simp [Matrix.mulVec, dotProduct]
  simp only [sigTheta, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hJ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- `|(σ_θ x)_a| ≤ |x|_∞` for `θ ∈ [0, 1]`. -/
private lemma FarDet_sig_linf (D : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : Fin D → ℂ)
    (a : Fin D) : ‖(sigTheta D θ *ᵥ x) a‖ ≤ ‖x‖ := by
  have hD : 0 < D := a.pos
  have hx : ∀ b, ‖x b‖ ≤ ‖x‖ := fun b => norm_le_pi_norm x b
  rw [FarDet_sig_apply]
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
private lemma FarDet_sig_one (D : ℕ) (hD : 1 ≤ D) (θ : ℝ) (m : ℂ) :
    (sigTheta D θ *ᵥ fun _ => m) = fun _ => m := by
  funext a
  rw [FarDet_sig_apply]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  push_cast
  field_simp
  ring

/-- The resolvent of the self-consistent equation far from the spectrum: for Hermitian `Λ` with
`‖Λ‖ ≤ 1/10`, `Im z > 0`, `|Re z| ≥ 4`, `θ ∈ [0, 1]` and `|x|_∞ ≤ 1`, with `y = σ_θ(m 1 + x)`,
`R_y` is a true inverse, `‖R_y‖ ≤ 10/19` and `‖R_y - M‖ ≤ (100/551) |x|_∞`. -/
theorem resX_far {D N : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (z : ℂ) (hz : 0 < z.im) (hE : 4 ≤ |z.re|) (x : Fin D → ℂ) (hx : ‖x‖ ≤ 1) :
    (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) -
        ∑ b, (sigTheta D θ *ᵥ fun a => mExt Λ z + x a) b • Ea D N b) *
        resX Λ z (sigTheta D θ *ᵥ fun a => mExt Λ z + x a) = 1 ∧
      opNorm (resX Λ z (sigTheta D θ *ᵥ fun a => mExt Λ z + x a)) ≤ 10 / 19 ∧
      opNorm (resX Λ z (sigTheta D θ *ᵥ fun a => mExt Λ z + x a) - MExt Λ z) ≤
        100 / 551 * ‖x‖ := by
  rcases isEmpty_or_nonempty (Idx D N) with hemp | hne
  · refine ⟨?_, ?_, ?_⟩
    · ext p
      exact (IsEmpty.false p).elim
    · rw [FarDet_opNorm_of_isEmpty]
      norm_num
    · rw [FarDet_opNorm_of_isEmpty]
      positivity
  obtain ⟨hKM, hMn, -⟩ := MExt_far Λ hΛ hℓ z hz hE
  have hD : 1 ≤ D := by
    obtain ⟨⟨a, i⟩⟩ := hne
    exact a.pos
  have hy : (sigTheta D θ *ᵥ fun a => mExt Λ z + x a) =
      fun a => mExt Λ z + (sigTheta D θ *ᵥ x) a := by
    have h1 : (fun a => mExt Λ z + x a) = (fun _ => mExt Λ z) + x := rfl
    rw [h1, Matrix.mulVec_add, FarDet_sig_one D hD]
    rfl
  rw [hy]
  have hd0 : ∀ a, ‖(sigTheta D θ *ᵥ x) a‖ ≤ ‖x‖ := FarDet_sig_linf D θ hθ0 hθ1 x
  generalize sigTheta D θ *ᵥ x = d at hd0 ⊢
  generalize hMM : MExt Λ z = M at hMn hKM ⊢
  generalize hmm : mExt Λ z = m at hKM ⊢
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  set K : Matrix (Idx D N) (Idx D N) ℂ := Λ - (z + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)
    with hKdef
  set Δ : Matrix (Idx D N) (Idx D N) ℂ := ∑ b, d b • Ea D N b with hΔdef
  have hMK : M * K = 1 := mul_eq_one_comm.mp hKM
  have hT : Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - ∑ b, (m + d b) • Ea D N b =
      K - Δ := by
    simp only [add_smul, Finset.sum_add_distrib, ← Finset.smul_sum, FarDet_sum_Ea_one, hKdef,
      hΔdef]
    abel
  have hRx : resX Λ z (fun a => m + d a) = (K - Δ)⁻¹ := by
    unfold resX
    congr 1
  have hΔn : opNorm Δ ≤ ‖x‖ := by
    rw [hΔdef, FarDet_sum_Ea, FarDet_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hx0).mpr fun p => hd0 p.1
  have hlow : ∀ v : EuclideanSpace ℂ (Idx D N), (19 / 10 : ℝ) * ‖v‖ ≤
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
        10 / 29 * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) K v‖ :=
      mul_le_mul_of_nonneg_right hMn (norm_nonneg _)
    have h5 : opNorm Δ * ‖v‖ ≤ 1 * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hΔn.trans hx) (norm_nonneg _)
    linarith
  obtain ⟨hinv, hRn'⟩ := FarDet_inv _ (19 / 10) (by norm_num) hlow
  have hRn : opNorm (K - Δ)⁻¹ ≤ 10 / 19 := by
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
  refine ⟨?_, ?_, ?_⟩
  · change (Λ - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) - ∑ b, (m + d b) • Ea D N b) *
      resX Λ z (fun a => m + d a) = 1
    rw [hT, hRx]
    exact hinv
  · rw [hRx]
    exact hRn
  · rw [hRx]
    have : R - M = R * Δ * M := by
      conv_lhs => rw [e1]
      rw [add_sub_cancel_left]
    rw [this]
    have h2 := FarDet_opNorm_mul_le_of_le (FarDet_opNorm_mul_le_of_le hRn hΔn) hMn
    refine h2.trans (le_of_eq ?_)
    ring

/-- `|x^* T y| ≤ ‖T‖` for `|x|, |y| ≤ 1`. -/
private lemma FarDet_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
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

/-- `D⟨M E_a⟩ = m` for every block, for `D ≥ 1`, `N ≥ 1` and `z ∉ ℝ`: the diagonal blocks of
(2.17) [def_G0] have the normalized trace (2.16) [self_m]. -/
private lemma FarDet_blk_M (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N)
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

/-- The linear regime of the equation for the block traces far from the spectrum: for
`Λ = lam D N A` with `‖Λ‖ ≤ 1/10`, Hermitian `H`, `G = (H + Λ - z)⁻¹`, `Im z > 0`, `|Re z| ≥ 4`,
`θ ∈ [0, 1]`, `x = blockTr(G - M)` with `|x|_∞ ≤ 1` and `x̃ = σ_θ g`, `g_a = D⟨E_a G⟩`: `R_x̃` is
a true inverse with `‖R_x̃‖ ≤ 10/19`; `|x|_∞ ≤ (551/451) |blockTr(R_x̃ H̲G)|_∞`;
`|(G - M)_{uv}| ≤ (100/551) |x|_∞ + |(R_x̃ H̲G)_{uv}|` for unit `u, v`; and `|⟨G - M⟩| ≤ |x|_∞`. -/
theorem blockTr_far (D N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : opNorm (lam D N A) ≤ 1 / 10)
    (H : Matrix (Idx D N) (Idx D N) ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (hE : 4 ≤ |z.re|) (hx : ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤ 1) :
    (lam D N A - z • (1 : Matrix (Idx D N) (Idx D N) ℂ) -
        ∑ b, (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) b • Ea D N b) *
        resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) = 1 ∧
      opNorm (resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z))) ≤
        10 / 19 ∧
      ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤
        551 / 451 * ‖blockTr D N (resX (lam D N A) z (sigTheta D θ *ᵥ
          blockTr D N (res (H + lam D N A) z)) * hgUnder D N θ H (lam D N A) z)‖ ∧
      (∀ u v : Idx D N → ℂ, ∑ i, ‖u i‖ ^ 2 = 1 → ∑ i, ‖v i‖ ^ 2 = 1 →
        ‖star u ⬝ᵥ ((res (H + lam D N A) z - MExt (lam D N A) z) *ᵥ v)‖ ≤
          100 / 551 * ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ +
            ‖star u ⬝ᵥ ((resX (lam D N A) z (sigTheta D θ *ᵥ
              blockTr D N (res (H + lam D N A) z)) * hgUnder D N θ H (lam D N A) z) *ᵥ v)‖) ∧
      ‖ntr (res (H + lam D N A) z - MExt (lam D N A) z)‖ ≤
        ‖blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)‖ := by
  rcases isEmpty_or_nonempty (Idx D N) with hemp | hne
  · have hb : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, blockTr D N B = 0 := fun B => by
      funext a
      simp [blockTr, FarDet_ntr_of_isEmpty]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext p
      exact (IsEmpty.false p).elim
    · rw [FarDet_opNorm_of_isEmpty]
      norm_num
    · rw [hb, hb]
      norm_num
    · intro u v hu hv
      exfalso
      simp at hu
    · rw [FarDet_ntr_of_isEmpty, hb]
      simp
  have hD : 1 ≤ D := by
    obtain ⟨⟨a, i⟩⟩ := hne
    exact a.pos
  have hN : 1 ≤ N := by
    obtain ⟨⟨a, i⟩⟩ := hne
    exact i.pos
  have hΛh := lam_isHermitian D N A
  have hgM : (fun a => mExt (lam D N A) z +
      blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z) a) =
        blockTr D N (res (H + lam D N A) z) := by
    funext a
    have hM : blockTr D N (MExt (lam D N A) z) a = mExt (lam D N A) z := by
      unfold blockTr
      rw [FarDet_ntr_comm]
      exact FarDet_blk_M D N hD hN A z hz.ne' a
    rw [FarDet_blockTr_sub, Pi.sub_apply, hM]
    ring
  obtain ⟨h1, h2, h3⟩ := resX_far θ hθ0 hθ1 (lam D N A) hΛh hA z hz hE
    (blockTr D N (res (H + lam D N A) z - MExt (lam D N A) z)) hx
  rw [hgM] at h1 h2 h3
  have hG := res_eq_resX_sub D N θ A H hH z hz h1
  generalize hRdef : resX (lam D N A) z (sigTheta D θ *ᵥ blockTr D N (res (H + lam D N A) z)) =
    R at h1 h2 h3 hG ⊢
  generalize hUdef : hgUnder D N θ H (lam D N A) z = U at hG ⊢
  have hX : res (H + lam D N A) z - MExt (lam D N A) z =
      (R - MExt (lam D N A) z) - R * U := by
    rw [hG]
    abel
  rw [hX] at h3 hx ⊢
  generalize MExt (lam D N A) z = M at h3 hx ⊢
  have hsub : blockTr D N ((R - M) - R * U) = blockTr D N (R - M) - blockTr D N (R * U) :=
    FarDet_blockTr_sub D N _ _
  have hb1 : ‖blockTr D N (R - M)‖ ≤ opNorm (R - M) := blockTr_norm_le D N _
  refine ⟨h1, h2, ?_, ?_, FarDet_norm_ntr_le_blockTr D N hD _⟩
  · have := norm_sub_le (blockTr D N (R - M)) (blockTr D N (R * U))
    rw [hsub] at h3 ⊢
    linarith
  · intro u v hu hv
    rw [Matrix.sub_mulVec, dotProduct_sub]
    have hf := FarDet_form_le (R - M) u v hu.le hv.le
    have := norm_sub_le (star u ⬝ᵥ ((R - M) *ᵥ v)) (star u ⬝ᵥ ((R * U) *ᵥ v))
    linarith

/-- The size of a spectral parameter far from the spectrum: `4 ≤ |Re z| ≤ N^{δ₁}` and
`|Im z| ≤ 2` give `|z| ≤ N^{2δ₁}` and `1 + |z| ≤ (3/2) N^{δ₁}`. -/
theorem farZ_norm_le (δ₁ : ℝ) (N : ℕ) (z : ℂ) (h4 : 4 ≤ |z.re|) (hE : |z.re| ≤ (N : ℝ) ^ δ₁)
    (hη : |z.im| ≤ 2) :
    ‖z‖ ≤ (N : ℝ) ^ (2 * δ₁) ∧ 1 + ‖z‖ ≤ 3 / 2 * (N : ℝ) ^ δ₁ := by
  set t : ℝ := (N : ℝ) ^ δ₁ with ht
  have ht4 : 4 ≤ t := h4.trans hE
  have hpow : (N : ℝ) ^ (2 * δ₁) = t ^ 2 := by
    rw [mul_comm, Real.rpow_mul (Nat.cast_nonneg N), Real.rpow_two]
  have hsq : ‖z‖ ^ 2 ≤ t ^ 2 + 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : |z.re| ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hE 2
    have h2 : |z.im| ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hη 2
    rw [sq_abs] at h1 h2
    nlinarith
  have hz54 : ‖z‖ ≤ 5 / 4 * t := by
    by_contra hcon
    have hcon := not_le.mp hcon
    have := mul_self_lt_mul_self (by positivity : 0 ≤ 5 / 4 * t) hcon
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [hpow]
    nlinarith
  · linarith

end RBMTransitionEdge

end
