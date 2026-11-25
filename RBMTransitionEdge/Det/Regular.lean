module

public import RBMTransitionEdge.Det.Shift

@[expose] public section

/-!
# Regularity estimates in the localized regime

Lemma 5.1 [lem_regular_estimate_localized_eigenvector] and Lemma 5.3
[lem_regular_estimate_localized_eigenvalue]: under (2.8) [eq:condA2], the shifts `Δ_ev` and `Δ(t)`
are `O(⟨Λ²⟩)`, and the shifted averages `⟨𝔐₀ Λ̃ 𝔐₁ E_a⟩` are `Im m · O(⟨Λ²⟩)`.
-/

open MeasureTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

attribute [local irreducible] mSol

section RgSpec

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `U diag(d) U^*` for a unitary `U`. -/
private def Rg_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (diagonal d)

private lemma Rg_cd_mul (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    Rg_cd U d * Rg_cd U e = Rg_cd U (fun j => d j * e j) := by
  rw [Rg_cd, Rg_cd, Rg_cd, ← map_mul, diagonal_mul_diagonal]

private lemma Rg_cd_one (U : Matrix.unitaryGroup ι ℂ) : Rg_cd U (fun _ => 1) = 1 := by
  rw [Rg_cd, diagonal_one, map_one]

private lemma Rg_cd_smul (U : Matrix.unitaryGroup ι ℂ) (c : ℂ) (d : ι → ℂ) :
    c • Rg_cd U d = Rg_cd U (fun j => c * d j) := by
  rw [Rg_cd, Rg_cd, ← map_smul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

private lemma Rg_cd_sub (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    Rg_cd U d - Rg_cd U e = Rg_cd U (fun j => d j - e j) := by
  rw [Rg_cd, Rg_cd, Rg_cd, ← map_sub, diagonal_sub]

private lemma Rg_cd_sub_smul_one (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (c : ℂ) :
    Rg_cd U d - c • (1 : Matrix ι ι ℂ) = Rg_cd U (fun j => d j - c) := by
  rw [← Rg_cd_one U, Rg_cd_smul, Rg_cd_sub]
  simp

private lemma Rg_cd_conjTranspose (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    (Rg_cd U d)ᴴ = Rg_cd U (fun j => star (d j)) := by
  rw [← star_eq_conjTranspose, Rg_cd, Rg_cd, ← map_star, star_eq_conjTranspose,
    diagonal_conjTranspose]
  rfl

private lemma Rg_ntr_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    ntr (Rg_cd U d) = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, d j := by
  rw [ntr, Rg_cd, Unitary.conjStarAlgAut_apply, trace_mul_comm, ← mul_assoc,
    Unitary.star_mul_self_of_mem U.property, one_mul, trace_diagonal]

private lemma Rg_cd_inv (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (h : ∀ j, d j ≠ 0) :
    (Rg_cd U d)⁻¹ = Rg_cd U (fun j => (d j)⁻¹) := by
  apply inv_eq_right_inv
  rw [Rg_cd_mul]
  simp only [mul_inv_cancel₀ (h _)]
  exact Rg_cd_one U

private lemma Rg_cd_real_smul (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (s : ℝ) :
    (s : ℂ) • Rg_cd U (fun j => (μ j : ℂ)) = Rg_cd U (fun j => ((s * μ j : ℝ) : ℂ)) := by
  rw [Rg_cd_smul]
  congr 1
  funext j
  push_cast
  ring

/-- Every eigenvalue of a Hermitian matrix is bounded by the operator norm. -/
private lemma Rg_eig_le {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (j : ι) :
    |hΛ.eigenvalues j| ≤ opNorm Λ := by
  have hv : ‖hΛ.eigenvectorBasis j‖ = 1 := hΛ.eigenvectorBasis.norm_eq_one j
  have hT : Matrix.toEuclideanCLM (𝕜 := ℂ) Λ (hΛ.eigenvectorBasis j) =
      ((hΛ.eigenvalues j : ℂ)) • hΛ.eigenvectorBasis j := by
    apply WithLp.ofLp_injective
    rw [Matrix.ofLp_toEuclideanCLM, hΛ.mulVec_eigenvectorBasis, WithLp.ofLp_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have := (Matrix.toEuclideanCLM (𝕜 := ℂ) Λ).le_opNorm (hΛ.eigenvectorBasis j)
  rw [hT, norm_smul, hv, mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
  exact this

/-- A Hermitian matrix is `U diag(μ) U^*` with real `μ`, `|μ_j| ≤ ‖Λ‖`. -/
private lemma Rg_decomp {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ),
      Λ = Rg_cd U (fun j => (μ j : ℂ)) ∧ ∀ j, |μ j| ≤ opNorm Λ :=
  ⟨_, _, hΛ.spectral_theorem, Rg_eig_le hΛ⟩

omit [Fintype ι] [DecidableEq ι] in
private lemma Rg_herm_smul {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (t : ℝ) :
    ((t : ℂ) • Λ).IsHermitian :=
  hΛ.smul (by simp [IsSelfAdjoint])

private lemma Rg_opNorm_smul (Λ : Matrix ι ι ℂ) (t : ℝ) :
    opNorm ((t : ℂ) • Λ) = |t| * opNorm Λ := by
  unfold opNorm
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]

private lemma Rg_ne_of_im (x : ℝ) {w : ℂ} (h : 0 < w.im) : (x : ℂ) - w ≠ 0 := by
  intro e
  have := congrArg Complex.im e
  simp at this
  linarith

/-- The spectral form of `m_t(z)` and `M_t(z)` for `Λ = U diag(μ) U^*` and `Im z > 0`:
`m = n⁻¹ Σ_j (tμ_j - w)⁻¹` with `w = z + m`, and `M = U diag((tμ_j - w)⁻¹) U^*`. -/
private lemma Rg_bridge [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (t : ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    0 < (mSol ((t : ℂ) • Rg_cd U (fun j => (μ j : ℂ))) z).im ∧
      mSol ((t : ℂ) • Rg_cd U (fun j => (μ j : ℂ))) z = ((Fintype.card ι : ℂ))⁻¹ *
        ∑ j, (((t * μ j : ℝ) : ℂ) - (z + mSol ((t : ℂ) • Rg_cd U (fun j => (μ j : ℂ))) z))⁻¹ ∧
      MSol ((t : ℂ) • Rg_cd U (fun j => (μ j : ℂ))) z = Rg_cd U (fun j =>
        (((t * μ j : ℝ) : ℂ) - (z + mSol ((t : ℂ) • Rg_cd U (fun j => (μ j : ℂ))) z))⁻¹) := by
  have hH : ((t : ℂ) • Rg_cd U (fun j => (μ j : ℂ))).IsHermitian := by
    rw [Rg_cd_real_smul]
    have : (Rg_cd U (fun j => ((t * μ j : ℝ) : ℂ))) =
        Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (diagonal (fun j => ((t * μ j : ℝ) : ℂ))) := rfl
    rw [this, Unitary.conjStarAlgAut_apply]
    refine (isHermitian_diagonal_of_self_adjoint _ ?_).isSelfAdjoint.conjugate _ |>.isHermitian
    ext j; simp
  obtain ⟨h1, h2, -⟩ := mSol_spec _ hH z hz
  set m := mSol ((t : ℂ) • Rg_cd U (fun j => (μ j : ℂ))) z
  have hw : 0 < (z + m).im := by simp; linarith
  have hM : MSol ((t : ℂ) • Rg_cd U (fun j => (μ j : ℂ))) z =
      Rg_cd U (fun j => (((t * μ j : ℝ) : ℂ) - (z + m))⁻¹) := by
    change ((t : ℂ) • Rg_cd U (fun j => (μ j : ℂ)) - (z + m) • (1 : Matrix ι ι ℂ))⁻¹ = _
    rw [Rg_cd_real_smul, Rg_cd_sub_smul_one, Rg_cd_inv _ _ fun j => Rg_ne_of_im _ hw]
  refine ⟨h1, ?_, hM⟩
  calc m = ntr (MSol ((t : ℂ) • Rg_cd U (fun j => (μ j : ℂ))) z) := h2
    _ = _ := by rw [hM, Rg_ntr_cd]

end RgSpec

/-! ### The block interaction `Λ = lam D N A` -/

section RgLam
open scoped Matrix.Norms.L2Operator

/-- The embedding of the `N`-dimensional space as the `a`-th block. -/
private def Rg_J (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Fin N) ℂ :=
  Matrix.of fun p i => if p = (a, i) then 1 else 0

private lemma Rg_J_conj_mul (D N : ℕ) (a : Fin D) : (Rg_J D N a)ᴴ * Rg_J D N a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Rg_J, Matrix.of_apply, Matrix.one_apply]
  have : ∀ p : Idx D N, star (if p = (a, i) then (1 : ℂ) else 0) * (if p = (a, j) then 1 else 0) =
      if p = (a, i) then (if i = j then 1 else 0) else 0 := by
    intro p
    by_cases h : p = (a, i)
    · subst h
      by_cases hij : i = j <;> simp [hij]
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma Rg_J_norm (D N : ℕ) (hN : 1 ≤ N) (a : Fin D) : ‖Rg_J D N a‖ ≤ 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (Rg_J D N a)
  rw [Rg_J_conj_mul, norm_one] at h1
  have h0 : 0 ≤ ‖Rg_J D N a‖ := norm_nonneg _
  nlinarith

private lemma Rg_block_norm (D N : ℕ) (hN : 1 ≤ N) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖Rg_J D N a * M * (Rg_J D N b)ᴴ‖ ≤ ‖M‖ := by
  have ha := Rg_J_norm D N hN a
  have hb := Rg_J_norm D N hN b
  calc ‖Rg_J D N a * M * (Rg_J D N b)ᴴ‖ ≤ ‖Rg_J D N a * M‖ * ‖(Rg_J D N b)ᴴ‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Rg_J D N a‖ * ‖M‖) * ‖(Rg_J D N b)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
    _ = ‖M‖ := by ring

private lemma Rg_block_apply (D N : ℕ) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ)
    (p q : Idx D N) :
    (Rg_J D N a * M * (Rg_J D N b)ᴴ) p q = if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = a <;> by_cases h2 : q1 = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Rg_J, Prod.ext_iff, h1, h2]

private lemma Rg_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = ∑ a : Fin D, ∑ b : Fin D,
      ((if fwd D a b then Rg_J D N a * A * (Rg_J D N b)ᴴ else 0) +
        (if fwd D b a then Rg_J D N a * Aᴴ * (Rg_J D N b)ᴴ else 0)) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.add_apply]
  have e1 : ∀ a b : Fin D, (if fwd D a b then Rg_J D N a * A * (Rg_J D N b)ᴴ else 0) p q =
      if fwd D a b ∧ p.1 = a ∧ q.1 = b then A p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D a b <;> simp [h, Rg_block_apply]
  have e2 : ∀ a b : Fin D, (if fwd D b a then Rg_J D N a * Aᴴ * (Rg_J D N b)ᴴ else 0) p q =
      if fwd D b a ∧ p.1 = a ∧ q.1 = b then Aᴴ p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D b a <;> simp [h, Rg_block_apply]
  simp only [e1, e2, Finset.sum_add_distrib]
  unfold lam
  congr 1
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D p.1 q.1 <;> simp [h]
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases h : fwd D q.1 p.1 <;> simp [h, Matrix.conjTranspose_apply]

/-- `‖lam D N A‖ ≤ 2D²‖A‖`. -/
private lemma Rg_opNorm_lam (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := by
  change ‖lam D N A‖ ≤ 2 * (D : ℝ) ^ 2 * ‖A‖
  rw [Rg_lam_eq]
  have hb : ∀ a b : Fin D, ‖(if fwd D a b then Rg_J D N a * A * (Rg_J D N b)ᴴ else 0) +
      (if fwd D b a then Rg_J D N a * Aᴴ * (Rg_J D N b)ᴴ else 0)‖ ≤ 2 * ‖A‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D a b then Rg_J D N a * A * (Rg_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact Rg_block_norm D N hN a b A
      · simp
    have h2 : ‖(if fwd D b a then Rg_J D N a * Aᴴ * (Rg_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact (Rg_block_norm D N hN a b Aᴴ).trans (by rw [Matrix.l2_opNorm_conjTranspose])
      · simp
    linarith
  calc ‖∑ a : Fin D, ∑ b : Fin D, _‖ ≤ ∑ a : Fin D, ‖∑ b : Fin D, _‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin D, ∑ b : Fin D, 2 * ‖A‖ := by
        refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun b _ => hb a b)
    _ = 2 * (D : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end RgLam

section RgLam2

private lemma Rg_lam_smul (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    (t : ℂ) • lam D N A = lam D N ((t : ℂ) • A) := by
  ext p q
  simp only [lam, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [mul_add, Complex.conj_ofReal]

private lemma Rg_lam_diag (D N : ℕ) (_hD : 2 ≤ D) (A : Matrix (Fin N) (Fin N) ℂ) (p : Idx D N) :
    lam D N A p p = 0 := by
  have h : ¬ fwd D p.1 p.1 := by
    unfold fwd
    rintro (h | ⟨h3, h1, h0⟩)
    · omega
    · omega
  simp [lam, h]

private lemma Rg_ntr_lam (D N : ℕ) (hD : 2 ≤ D) (A : Matrix (Fin N) (Fin N) ℂ) :
    ntr (lam D N A) = 0 := by
  simp [ntr, Matrix.trace, Rg_lam_diag D N hD]

/-- `⟨Λ²⟩ ≤ 4D ‖A‖²_HS / N` for `Λ = lam D N A`. -/
private lemma Rg_avgSq_lam (D N : ℕ) (_hD : 2 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    avgSq (lam D N A) ≤ 4 * D * hsNorm A ^ 2 / N := by
  have hH := lam_isHermitian D N A
  set Λ := lam D N A
  have hn : (Fintype.card (Idx D N) : ℝ) = D * N := by simp
  have hDN : (0 : ℝ) < D * N := by
    have : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  -- `⟨Λ²⟩ = (DN)⁻¹ Σ_{p,q} |Λ_pq|²`
  have e : avgSq Λ = ((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2 := by
    unfold avgSq ntr
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply]
    have : ∀ p q : Idx D N, Λ p q * Λ q p = ((‖Λ p q‖ ^ 2 : ℝ) : ℂ) := by
      intro p q
      have : Λ q p = star (Λ p q) := by
        have := congrFun (congrFun hH.eq q) p
        simpa [Matrix.conjTranspose_apply] using this.symm
      rw [this, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [this]
    rw [show ((Fintype.card (Idx D N) : ℂ))⁻¹ * ∑ p : Idx D N, ∑ q : Idx D N,
        ((‖Λ p q‖ ^ 2 : ℝ) : ℂ) = ((((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2 : ℝ) : ℂ) by
      push_cast [Fintype.card_prod, Fintype.card_fin]; ring]
    rw [Complex.ofReal_re]
  -- each entry
  have hent : ∀ p q : Idx D N, ‖Λ p q‖ ^ 2 ≤ 2 * (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) := by
    intro p q
    simp only [Λ, lam]
    have h1 : ‖(if fwd D p.1 q.1 then A p.2 q.2 else 0)‖ ≤ ‖A p.2 q.2‖ := by
      split_ifs <;> simp
    have h2 : ‖(if fwd D q.1 p.1 then star (A q.2 p.2) else 0)‖ ≤ ‖A q.2 p.2‖ := by
      split_ifs <;> simp
    set x := (if fwd D p.1 q.1 then A p.2 q.2 else 0)
    set y := (if fwd D q.1 p.1 then star (A q.2 p.2) else 0)
    have hxy := norm_add_le x y
    have h3 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
    have h1' : ‖x‖ ^ 2 ≤ ‖A p.2 q.2‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' : ‖y‖ ^ 2 ≤ ‖A q.2 p.2‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have key : ∀ g : Fin N → Fin N → ℝ, ∑ p : Idx D N, ∑ q : Idx D N, g p.2 q.2 =
      (D : ℝ) ^ 2 * ∑ i, ∑ j, g i j := by
    intro g
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  have hsum : ∑ p : Idx D N, ∑ q : Idx D N, (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) =
      2 * (D : ℝ) ^ 2 * hsNorm A ^ 2 := by
    have hs : hsNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
      unfold hsNorm; rw [Real.sq_sqrt (by positivity)]
    simp only [Finset.sum_add_distrib]
    rw [key (fun i j => ‖A i j‖ ^ 2), key (fun i j => ‖A j i‖ ^ 2), hs,
      Finset.sum_comm (f := fun i j => ‖A j i‖ ^ 2)]
    ring
  rw [e]
  calc ((D : ℝ) * N)⁻¹ * ∑ p, ∑ q, ‖Λ p q‖ ^ 2
      ≤ ((D : ℝ) * N)⁻¹ * ∑ p : Idx D N, ∑ q : Idx D N,
          2 * (‖A p.2 q.2‖ ^ 2 + ‖A q.2 p.2‖ ^ 2) := by
        gcongr with p _ q _; exact hent p q
    _ = 4 * D * hsNorm A ^ 2 / N := by
        simp only [← Finset.mul_sum]
        rw [hsum]
        field_simp
        ring

end RgLam2

section RgClass

/-- `𝔯(k) ≥ 1`, `𝔯(k) ≤ k`, `𝔯(k) ≤ DN + 1 - k`, and `𝔯(k)` is one of the two. -/
private lemma Rg_rk (D N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ D * N) :
    1 ≤ rk D N k ∧ rk D N k ≤ k ∧ rk D N k ≤ ((D * N + 1 - k : ℕ) : ℝ) ∧
      (rk D N k = k ∨ rk D N k = ((D * N + 1 - k : ℕ) : ℝ)) := by
  unfold rk
  refine ⟨by exact_mod_cast (le_min hk (by omega)), by exact_mod_cast min_le_left _ _,
    by exact_mod_cast min_le_right _ _, ?_⟩
  rcases min_choice k (D * N + 1 - k) with h | h
  · left; rw [h]
  · right; rw [h]

end RgClass

/-! ### Scalar estimates for the spectral averages -/

section RgScalar

variable {ι : Type*} [Fintype ι]

/-- The resolvent entry `(ν - w)⁻¹`. -/
private def Rg_g (ν : ℝ) (w : ℂ) : ℂ := ((ν : ℂ) - w)⁻¹

/-- The standing hypotheses of the scalar estimates: eigenvalues `μ_j` with `Σ μ_j = 0`,
`|μ_j| ≤ 1/10`, a scale `|t| ≤ 1` and a point `‖w‖ ≥ 9/10`. -/
private structure Rg_H (μ : ι → ℝ) (t : ℝ) (w : ℂ) : Prop where
  sum : ∑ j, μ j = 0
  bd : ∀ j, |μ j| ≤ 1 / 10
  ht : |t| ≤ 1
  hw : 9 / 10 ≤ ‖w‖

private lemma Rg_H.nu {μ : ι → ℝ} {t : ℝ} {w : ℂ} (H : Rg_H μ t w) (j : ι) :
    |t * μ j| ≤ 1 / 10 := by
  rw [abs_mul]
  have := H.bd j
  have := H.ht
  nlinarith [abs_nonneg t, abs_nonneg (μ j)]

/-- Pointwise bounds: `ν - w ≠ 0`, `‖g‖ ‖w‖ ∈ [9/10, 9/8]` and
`‖g + w⁻¹‖ ‖w‖² ≤ (9/8)|ν|`, for `|ν| ≤ 1/10` and `‖w‖ ≥ 9/10`. -/
private lemma Rg_pt (ν : ℝ) {w : ℂ} (hν : |ν| ≤ 1 / 10) (hw : 9 / 10 ≤ ‖w‖) :
    (ν : ℂ) - w ≠ 0 ∧ ‖Rg_g ν w‖ * ‖w‖ ≤ 9 / 8 ∧ 9 / 10 ≤ ‖Rg_g ν w‖ * ‖w‖ ∧
      ‖Rg_g ν w - (-w)⁻¹‖ * ‖w‖ ^ 2 ≤ 9 / 8 * |ν| := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  have hW : 0 < ‖w‖ := by linarith
  have h1 : ‖w‖ - |ν| ≤ ‖(ν : ℂ) - w‖ := by
    have := norm_sub_norm_le w (ν : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    rw [norm_sub_rev]; linarith
  have h1' : ‖(ν : ℂ) - w‖ ≤ ‖w‖ + |ν| := by
    have := norm_sub_le (ν : ℂ) w
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  have hu : 0 < ‖(ν : ℂ) - w‖ := by linarith
  have hne : (ν : ℂ) - w ≠ 0 := norm_pos_iff.1 hu
  have hg : ‖Rg_g ν w‖ = ‖(ν : ℂ) - w‖⁻¹ := by rw [Rg_g, norm_inv]
  have hgu : ‖Rg_g ν w‖ * ‖(ν : ℂ) - w‖ = 1 := by
    rw [hg]; exact inv_mul_cancel₀ hu.ne'
  have hid : Rg_g ν w - (-w)⁻¹ = (ν : ℂ) * (Rg_g ν w * w⁻¹) := by
    unfold Rg_g
    field_simp
    ring
  have hn : ‖Rg_g ν w - (-w)⁻¹‖ = |ν| * (‖Rg_g ν w‖ * ‖w‖⁻¹) := by
    rw [hid, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hG0 : 0 ≤ ‖Rg_g ν w‖ := norm_nonneg _
  refine ⟨hne, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rw [hn]
    have : ‖Rg_g ν w‖ * ‖w‖ ≤ 9 / 8 := by nlinarith
    calc |ν| * (‖Rg_g ν w‖ * ‖w‖⁻¹) * ‖w‖ ^ 2 = |ν| * (‖Rg_g ν w‖ * ‖w‖) := by
          field_simp
      _ ≤ |ν| * (9 / 8) := by gcongr
      _ = _ := by ring

/-- A bound `‖f j‖ ≤ b j` passes to normalized sums. -/
private lemma Rg_avg_le [Nonempty ι] (f : ι → ℂ) (b : ι → ℝ) (h : ∀ j, ‖f j‖ ≤ b j) :
    ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, f j‖ ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, b j := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  gcongr
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => h j)

end RgScalar

section RgScalar2

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
private lemma Rg_nu_sq {μ : ι → ℝ} {t : ℝ} (ht : |t| ≤ 1) (j : ι) :
    |t * μ j| ≤ |μ j| := by
  rw [abs_mul]
  nlinarith [abs_nonneg t, abs_nonneg (μ j)]

/-- `‖w m + 1‖ ‖w‖² ≤ (9/8) ⟨Λ²⟩` for `m = n⁻¹ Σ g_j`. -/
private lemma Rg_S1 [Nonempty ι] {μ : ι → ℝ} {t : ℝ} {w : ℂ} (H : Rg_H μ t w) {m : ℂ}
    (hm : m = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Rg_g (t * μ j) w) {σ : ℝ}
    (hσ : σ = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) :
    ‖w * m + 1‖ * ‖w‖ ^ 2 ≤ 9 / 8 * σ := by
  have hn : ((Fintype.card ι : ℂ)) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hW : 0 < ‖w‖ := by have := H.hw; linarith
  have key : w * m + 1 = ((Fintype.card ι : ℂ))⁻¹ *
      ∑ j, (((t * μ j : ℝ) : ℂ) * (Rg_g (t * μ j) w - (-w)⁻¹)) := by
    have e1 : ∀ j, w * Rg_g (t * μ j) w + 1 = ((t * μ j : ℝ) : ℂ) * Rg_g (t * μ j) w := by
      intro j
      obtain ⟨hne, -⟩ := Rg_pt (t * μ j) (H.nu j) H.hw
      unfold Rg_g
      field_simp
      ring
    have hs0 : ∑ j, ((t * μ j : ℝ) : ℂ) = 0 := by
      have : ∑ j, (t * μ j : ℝ) = 0 := by rw [← Finset.mul_sum, H.sum, mul_zero]
      exact_mod_cast this
    calc w * m + 1 = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (w * Rg_g (t * μ j) w + 1) := by
          rw [hm, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          field_simp
      _ = _ := by
          congr 1
          have : ∀ j, w * Rg_g (t * μ j) w + 1 = ((t * μ j : ℝ) : ℂ) *
              (Rg_g (t * μ j) w - (-w)⁻¹) + ((t * μ j : ℝ) : ℂ) * (-w)⁻¹ := by
            intro j; rw [e1 j]; ring
          rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, ← Finset.sum_mul,
            hs0, zero_mul, add_zero]
  rw [key]
  have hb := Rg_avg_le (fun j => ((t * μ j : ℝ) : ℂ) * (Rg_g (t * μ j) w - (-w)⁻¹))
    (fun j => 9 / 8 * μ j ^ 2 / ‖w‖ ^ 2) (fun j => by
      obtain ⟨-, -, -, h4⟩ := Rg_pt (t * μ j) (H.nu j) H.hw
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, le_div_iff₀ (by positivity)]
      have h5 := Rg_nu_sq (μ := μ) H.ht j
      have h6 : |t * μ j| ^ 2 ≤ μ j ^ 2 := by
        rw [← sq_abs (μ j)]; exact pow_le_pow_left₀ (abs_nonneg _) h5 2
      calc |t * μ j| * ‖Rg_g (t * μ j) w - (-w)⁻¹‖ * ‖w‖ ^ 2
          = |t * μ j| * (‖Rg_g (t * μ j) w - (-w)⁻¹‖ * ‖w‖ ^ 2) := by ring
        _ ≤ |t * μ j| * (9 / 8 * |t * μ j|) := by gcongr
        _ ≤ _ := by nlinarith)
  have hsum : ((Fintype.card ι : ℝ))⁻¹ * ∑ j, 9 / 8 * μ j ^ 2 / ‖w‖ ^ 2 =
      9 / 8 * σ / ‖w‖ ^ 2 := by
    rw [hσ, ← Finset.sum_div, ← Finset.mul_sum]
    ring
  rw [hsum] at hb
  calc ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((t * μ j : ℝ) : ℂ) * (Rg_g (t * μ j) w - (-w)⁻¹)‖ *
        ‖w‖ ^ 2 ≤ 9 / 8 * σ / ‖w‖ ^ 2 * ‖w‖ ^ 2 := by gcongr
    _ = 9 / 8 * σ := by field_simp

end RgScalar2

section RgScalar3

variable {ι : Type*} [Fintype ι]

/-- `Im (ν - w)⁻¹ = Im w ‖(ν - w)⁻¹‖²`. -/
private lemma Rg_im_g (ν : ℝ) (w : ℂ) : (Rg_g ν w).im = w.im * ‖Rg_g ν w‖ ^ 2 := by
  unfold Rg_g
  rw [norm_inv, inv_pow, Complex.sq_norm, Complex.inv_im]
  simp [div_eq_mul_inv]

/-- The variance identity `x - ‖m‖² = n⁻¹ Σ ‖g_j - c‖² - ‖m - c‖²` with `m = n⁻¹ Σ g_j`,
`x = n⁻¹ Σ ‖g_j‖²`. -/
private lemma Rg_var_id [Nonempty ι] (g : ι → ℂ) {m : ℂ}
    (hm : m = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, g j) {x : ℝ}
    (hx : x = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖g j‖ ^ 2) (c : ℂ) :
    ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖g j - c‖ ^ 2 = x - ‖m‖ ^ 2 + ‖m - c‖ ^ 2 := by
  have hn : ((Fintype.card ι : ℂ)) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn' : ((Fintype.card ι : ℝ)) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ j, g j = (Fintype.card ι : ℂ) * m := by rw [hm]; field_simp
  have e1 : ∑ j, ‖g j - c‖ ^ 2 = (∑ j, ‖g j‖ ^ 2) + (Fintype.card ι : ℝ) * ‖c‖ ^ 2 -
      2 * ((Fintype.card ι : ℝ) * (m * (starRingEnd ℂ) c).re) := by
    simp only [Complex.sq_norm, Complex.normSq_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul, hsum, mul_assoc]
    simp
  have e2 : ‖m - c‖ ^ 2 = ‖m‖ ^ 2 + ‖c‖ ^ 2 - 2 * (m * (starRingEnd ℂ) c).re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  rw [e1, e2, hx]
  field_simp
  ring

/-- `0 ≤ x - ‖m‖²` and `(x - ‖m‖²) ‖w‖⁴ ≤ (81/64) ⟨Λ²⟩`. -/
private lemma Rg_S2 [Nonempty ι] {μ : ι → ℝ} {t : ℝ} {w : ℂ} (H : Rg_H μ t w) {m : ℂ}
    (hm : m = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Rg_g (t * μ j) w) {σ x : ℝ}
    (hσ : σ = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2)
    (hx : x = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2) :
    0 ≤ x - ‖m‖ ^ 2 ∧ (x - ‖m‖ ^ 2) * ‖w‖ ^ 4 ≤ 81 / 64 * σ := by
  have hW : 0 < ‖w‖ := by have := H.hw; linarith
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · have h := Rg_var_id (fun j => Rg_g (t * μ j) w) hm hx m
    simp only [sub_self, norm_zero] at h
    have : 0 ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Rg_g (t * μ j) w - m‖ ^ 2 :=
      mul_nonneg (inv_nonneg.2 hnpos.le) (Finset.sum_nonneg fun j _ => sq_nonneg _)
    linarith
  · have h := Rg_var_id (fun j => Rg_g (t * μ j) w) hm hx (-w)⁻¹
    have hpt : ∀ j, ‖Rg_g (t * μ j) w - (-w)⁻¹‖ ^ 2 ≤ 81 / 64 * μ j ^ 2 / ‖w‖ ^ 4 := by
      intro j
      obtain ⟨-, -, -, h4⟩ := Rg_pt (t * μ j) (H.nu j) H.hw
      rw [le_div_iff₀ (by positivity)]
      have h5 := Rg_nu_sq (μ := μ) H.ht j
      have h6 : |t * μ j| ^ 2 ≤ μ j ^ 2 := by
        rw [← sq_abs (μ j)]; exact pow_le_pow_left₀ (abs_nonneg _) h5 2
      have h7 : (‖Rg_g (t * μ j) w - (-w)⁻¹‖ * ‖w‖ ^ 2) ^ 2 ≤ (9 / 8 * |t * μ j|) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h4 2
      calc ‖Rg_g (t * μ j) w - (-w)⁻¹‖ ^ 2 * ‖w‖ ^ 4
          = (‖Rg_g (t * μ j) w - (-w)⁻¹‖ * ‖w‖ ^ 2) ^ 2 := by ring
        _ ≤ (9 / 8 * |t * μ j|) ^ 2 := h7
        _ = 81 / 64 * |t * μ j| ^ 2 := by ring
        _ ≤ _ := by nlinarith
    have hb : ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Rg_g (t * μ j) w - (-w)⁻¹‖ ^ 2 ≤
        ((Fintype.card ι : ℝ))⁻¹ * ∑ j, 81 / 64 * μ j ^ 2 / ‖w‖ ^ 4 := by
      gcongr with j _
      exact hpt j
    have hsum : ((Fintype.card ι : ℝ))⁻¹ * ∑ j, 81 / 64 * μ j ^ 2 / ‖w‖ ^ 4 =
        81 / 64 * σ / ‖w‖ ^ 4 := by
      rw [hσ, ← Finset.sum_div, ← Finset.mul_sum]
      ring
    rw [hsum] at hb
    have h8 : x - ‖m‖ ^ 2 ≤ 81 / 64 * σ / ‖w‖ ^ 4 := by
      have : 0 ≤ ‖m - (-w)⁻¹‖ ^ 2 := sq_nonneg _
      linarith
    calc (x - ‖m‖ ^ 2) * ‖w‖ ^ 4 ≤ 81 / 64 * σ / ‖w‖ ^ 4 * ‖w‖ ^ 4 := by gcongr
      _ = _ := by field_simp

/-- `81/100 ≤ x ‖w‖²`. -/
private lemma Rg_S3 [Nonempty ι] {μ : ι → ℝ} {t : ℝ} {w : ℂ} (H : Rg_H μ t w) {x : ℝ}
    (hx : x = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2) :
    81 / 100 ≤ x * ‖w‖ ^ 2 := by
  have hW : 0 < ‖w‖ := by have := H.hw; linarith
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hpt : ∀ j, 81 / 100 ≤ ‖Rg_g (t * μ j) w‖ ^ 2 * ‖w‖ ^ 2 := by
    intro j
    obtain ⟨-, -, h3, -⟩ := Rg_pt (t * μ j) (H.nu j) H.hw
    calc 81 / 100 ≤ (‖Rg_g (t * μ j) w‖ * ‖w‖) ^ 2 := by nlinarith
      _ = _ := by ring
  have hS : (Fintype.card ι : ℝ) * (81 / 100) ≤ ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2 * ‖w‖ ^ 2 := by
    calc (Fintype.card ι : ℝ) * (81 / 100) = ∑ _j : ι, (81 / 100 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => hpt j
  have e : x * ‖w‖ ^ 2 = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [hx, ← Finset.sum_mul]; ring
  rw [e]
  calc (81 / 100 : ℝ) = ((Fintype.card ι : ℝ))⁻¹ * ((Fintype.card ι : ℝ) * (81 / 100)) := by
        field_simp
    _ ≤ _ := by gcongr

/-- `Im m = Im w · x` (the identity `⟨M M*⟩ = Im m / (Im m + η)` of (A.3) [equation_z_im_m]). -/
private lemma Rg_S4 [Nonempty ι] {μ : ι → ℝ} {t : ℝ} {w : ℂ} {m : ℂ}
    (hm : m = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Rg_g (t * μ j) w) {x : ℝ}
    (hx : x = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2) :
    m.im = w.im * x := by
  have hn' : ((Fintype.card ι : ℝ)) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hm, hx]
  have : (((Fintype.card ι : ℂ))⁻¹ : ℂ) = (((Fintype.card ι : ℝ))⁻¹ : ℝ) := by push_cast; rfl
  rw [this, Complex.im_ofReal_mul, Complex.im_sum]
  simp only [Rg_im_g]
  rw [← Finset.mul_sum]
  ring

end RgScalar3

section RgScalar4

variable {ι : Type*} [Fintype ι]

private lemma Rg_sigma_bd [Nonempty ι] {μ : ι → ℝ} (hμ : ∀ j, |μ j| ≤ 1 / 10) {σ : ℝ}
    (hσ : σ = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) : 0 ≤ σ ∧ σ ≤ 1 / 100 := by
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h0 : 0 ≤ σ := by
    rw [hσ]
    exact mul_nonneg (inv_nonneg.2 hnpos.le) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  refine ⟨h0, ?_⟩
  have h1 : ∑ j, μ j ^ 2 ≤ (Fintype.card ι : ℝ) * (1 / 100) := by
    calc ∑ j, μ j ^ 2 ≤ ∑ _j : ι, (1 / 100 : ℝ) := Finset.sum_le_sum fun j _ => by
          have := hμ j
          rw [← sq_abs]; nlinarith [abs_nonneg (μ j)]
      _ = _ := by simp
  rw [hσ]
  calc ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 ≤
      ((Fintype.card ι : ℝ))⁻¹ * ((Fintype.card ι : ℝ) * (1 / 100)) := by gcongr
    _ = 1 / 100 := by field_simp

/-- Core scalar estimates for `Δ_ev = Re(w + m⁻¹)`: `|Δ_ev| ≤ (5/2) ⟨Λ²⟩` and
`‖1 + (w - Δ_ev) m‖ ≤ (7/2) Im m ⟨Λ²⟩`, for `m = n⁻¹ Σ g_j` with `Im m > 0`. -/
private lemma Rg_S5 [Nonempty ι] {μ : ι → ℝ} {t : ℝ} {w : ℂ} (H : Rg_H μ t w) {m : ℂ}
    (hm : m = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Rg_g (t * μ j) w) (ham : 0 < m.im) {σ x : ℝ}
    (hσ : σ = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2)
    (hx : x = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2) :
    |(w + m⁻¹).re| ≤ 5 / 2 * σ ∧
      ‖1 + (w - (((w + m⁻¹).re : ℝ) : ℂ)) * m‖ ≤ 7 / 2 * (m.im * σ) := by
  have hW9 := H.hw
  have hW : 0 < ‖w‖ := by linarith
  obtain ⟨hσ0, hσ1⟩ := Rg_sigma_bd H.bd hσ
  have S1 := Rg_S1 H hm hσ
  obtain ⟨S2a, S2b⟩ := Rg_S2 H hm hσ hx
  have S3 := Rg_S3 H hx
  have S4 := Rg_S4 hm hx
  set W := ‖w‖ with hWdef
  set E := ‖w * m + 1‖ with hEdef
  have hE0 : 0 ≤ E := norm_nonneg _
  have hE1 : E ≤ 1 / 2 := by nlinarith
  have hwm : 1 / 2 ≤ W * ‖m‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (w * m + 1)
    rw [norm_one, show (1 : ℂ) - (w * m + 1) = -(w * m) by ring, norm_neg, norm_mul] at h
    linarith
  have hm0 : m ≠ 0 := by
    intro h; rw [h, norm_zero] at hwm; linarith
  have hmn : 0 < ‖m‖ := norm_pos_iff.2 hm0
  have hx0 : 0 < x := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg W]
  -- `s = w + m⁻¹ = (w m + 1) / m`
  set s := w + m⁻¹ with hs
  have hsm : m * s = w * m + 1 := by rw [hs]; field_simp
  have hsn : ‖s‖ * ‖m‖ = E := by rw [← norm_mul, mul_comm, hsm]
  have hs1 : ‖s‖ ≤ 5 / 2 * σ := by
    have h1 : ‖s‖ * (W * ‖m‖) = E * W := by
      calc ‖s‖ * (W * ‖m‖) = (‖s‖ * ‖m‖) * W := by ring
        _ = E * W := by rw [hsn]
    have h2 : ‖s‖ * (1 / 2) ≤ E * W := by
      calc ‖s‖ * (1 / 2) ≤ ‖s‖ * (W * ‖m‖) := by gcongr
        _ = E * W := h1
    have h3 : E * W * W ≤ 9 / 8 * σ := by nlinarith
    have h4 : ‖s‖ * (1 / 2) * W ≤ 9 / 8 * σ := by
      calc ‖s‖ * (1 / 2) * W ≤ E * W * W := by gcongr
        _ ≤ _ := h3
    nlinarith [norm_nonneg s]
  refine ⟨(Complex.abs_re_le_norm s).trans hs1, ?_⟩
  -- the exact identity
  have hid : 1 + (w - ((s.re : ℝ) : ℂ)) * m = m * (((s.im : ℝ) : ℂ) * Complex.I) := by
    have h2 : s - ((s.re : ℝ) : ℂ) = ((s.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    calc 1 + (w - ((s.re : ℝ) : ℂ)) * m = m * s - m * (s.re : ℂ) := by rw [hsm]; ring
      _ = m * (s - s.re) := by ring
      _ = _ := by rw [h2]
  have hQ : ‖1 + (w - ((s.re : ℝ) : ℂ)) * m‖ = ‖m‖ * |s.im| := by
    rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  rw [hQ]
  -- `Im s = Im w - Im m / ‖m‖²`
  have hsim : s.im = w.im + (m⁻¹).im := by rw [hs]; simp
  have hinv : (m⁻¹).im = -(m.im / ‖m‖ ^ 2) := by
    rw [Complex.inv_im, Complex.sq_norm]; ring
  have hq : s.im * (x * ‖m‖ ^ 2) = m.im * (‖m‖ ^ 2 - x) := by
    rw [hsim, hinv]
    have : ‖m‖ ^ 2 ≠ 0 := by positivity
    calc (w.im + -(m.im / ‖m‖ ^ 2)) * (x * ‖m‖ ^ 2) = (w.im * x) * ‖m‖ ^ 2 - m.im * x := by
          field_simp
          ring
      _ = _ := by rw [← S4]; ring
  have hv : |s.im| * (x * ‖m‖ ^ 2) = m.im * (x - ‖m‖ ^ 2) := by
    have hxm : 0 < x * ‖m‖ ^ 2 := by positivity
    calc |s.im| * (x * ‖m‖ ^ 2) = |s.im * (x * ‖m‖ ^ 2)| := by rw [abs_mul, abs_of_pos hxm]
      _ = |m.im * (‖m‖ ^ 2 - x)| := by rw [hq]
      _ = m.im * (x - ‖m‖ ^ 2) := by
        rw [abs_mul, abs_of_pos ham, abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ x - ‖m‖ ^ 2)]
  set P := x * ‖m‖ with hP
  set v := x - ‖m‖ ^ 2 with hvdef
  have hQP : ‖m‖ * |s.im| * P = m.im * v := by
    rw [← hv, hP]; ring
  have hv3 : v * W ^ 3 ≤ 81 / 64 * σ * (10 / 9) := by
    have h1 : v * W ^ 3 * (9 / 10) ≤ v * W ^ 3 * W := by
      gcongr
    have h2 : v * W ^ 3 * W = v * W ^ 4 := by ring
    nlinarith
  have hPW : 81 / 200 ≤ P * W ^ 3 := by
    have : P * W ^ 3 = (x * W ^ 2) * (W * ‖m‖) := by rw [hP]; ring
    rw [this]
    calc (81 / 200 : ℝ) = (81 / 100) * (1 / 2) := by norm_num
      _ ≤ _ := by gcongr
  have hQ0 : 0 ≤ ‖m‖ * |s.im| := by positivity
  have hfin : (‖m‖ * |s.im|) * (81 / 200) ≤ m.im * (81 / 64 * σ * (10 / 9)) := by
    calc (‖m‖ * |s.im|) * (81 / 200) ≤ (‖m‖ * |s.im|) * (P * W ^ 3) := by gcongr
      _ = m.im * (v * W ^ 3) := by
        calc (‖m‖ * |s.im|) * (P * W ^ 3) = (‖m‖ * |s.im| * P) * W ^ 3 := by ring
          _ = _ := by rw [hQP]; ring
      _ ≤ _ := by gcongr
  nlinarith

end RgScalar4

section RgScalar5

variable {ι : Type*} [Fintype ι]

/-- `| |X|² - |Y|² | ≤ |X - Y| (|X| + |Y|)`. -/
private lemma Rg_sq_sub (X Y : ℂ) : |‖X‖ ^ 2 - ‖Y‖ ^ 2| ≤ ‖X - Y‖ * (‖X‖ + ‖Y‖) := by
  have h := abs_norm_sub_norm_le X Y
  rw [show ‖X‖ ^ 2 - ‖Y‖ ^ 2 = (‖X‖ - ‖Y‖) * (‖X‖ + ‖Y‖) by ring, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖X‖ + ‖Y‖)]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- `‖u |u|² - v |v|²‖ ≤ 3 B² ‖u - v‖` for `‖u‖, ‖v‖ ≤ B`. -/
private lemma Rg_cube_sub (u v : ℂ) {B : ℝ} (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) :
    ‖u * ((‖u‖ ^ 2 : ℝ) : ℂ) - v * ((‖v‖ ^ 2 : ℝ) : ℂ)‖ ≤ 3 * B ^ 2 * ‖u - v‖ := by
  have hB : 0 ≤ B := (norm_nonneg u).trans hu
  have e : u * ((‖u‖ ^ 2 : ℝ) : ℂ) - v * ((‖v‖ ^ 2 : ℝ) : ℂ) =
      (u - v) * ((‖u‖ ^ 2 : ℝ) : ℂ) + v * (((‖u‖ ^ 2 - ‖v‖ ^ 2 : ℝ)) : ℂ) := by
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖u‖ ^ 2)]
  have h1 := Rg_sq_sub u v
  have h2 : ‖u‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
  have h3 : ‖u - v‖ * (‖u‖ + ‖v‖) ≤ ‖u - v‖ * (2 * B) := by gcongr; linarith
  have h4 : ‖v‖ * |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ B * (‖u - v‖ * (2 * B)) := by
    gcongr
    exact h1.trans h3
  nlinarith [norm_nonneg (u - v), norm_nonneg u, norm_nonneg v]

/-- `g² = |g|² + 2i (Im g) g`. -/
private lemma Rg_sq_id (g : ℂ) :
    g ^ 2 = ((‖g‖ ^ 2 : ℝ) : ℂ) + 2 * Complex.I * (g.im : ℂ) * g := by
  have h : ‖g‖ ^ 2 = g.re ^ 2 + g.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h]
  apply Complex.ext <;> simp [pow_two] <;> ring

/-- `|r₁| ‖w‖³ ≤ (153/64) ⟨Λ²⟩` for `r₁ = n⁻¹ Σ μ_j |g_j|²`. -/
private lemma Rg_R1 [Nonempty ι] {μ : ι → ℝ} {t : ℝ} {w : ℂ} (H : Rg_H μ t w) {σ r : ℝ}
    (hσ : σ = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2)
    (hr : r = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j * ‖Rg_g (t * μ j) w‖ ^ 2) :
    |r| * ‖w‖ ^ 3 ≤ 153 / 64 * σ := by
  have hW : 0 < ‖w‖ := by have := H.hw; linarith
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw0 : w ≠ 0 := norm_pos_iff.1 hW
  have hg0 : ‖(-w)⁻¹‖ = ‖w‖⁻¹ := by rw [norm_inv, norm_neg]
  have e : r = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j * (‖Rg_g (t * μ j) w‖ ^ 2 - ‖(-w)⁻¹‖ ^ 2) := by
    rw [hr]
    congr 1
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, H.sum, zero_mul, sub_zero]
  have hpt : ∀ j, |μ j * (‖Rg_g (t * μ j) w‖ ^ 2 - ‖(-w)⁻¹‖ ^ 2)| ≤
      153 / 64 * μ j ^ 2 / ‖w‖ ^ 3 := by
    intro j
    obtain ⟨-, h2, -, h4⟩ := Rg_pt (t * μ j) (H.nu j) H.hw
    rw [le_div_iff₀ (by positivity), abs_mul]
    have h1 := Rg_sq_sub (Rg_g (t * μ j) w) ((-w)⁻¹)
    have h5 := Rg_nu_sq (μ := μ) H.ht j
    have hG0 : 0 ≤ ‖Rg_g (t * μ j) w‖ := norm_nonneg _
    have hd0 : 0 ≤ ‖Rg_g (t * μ j) w - (-w)⁻¹‖ := norm_nonneg _
    have hg1 : ‖(-w)⁻¹‖ * ‖w‖ = 1 := by rw [hg0]; field_simp
    have hS : (‖Rg_g (t * μ j) w‖ + ‖(-w)⁻¹‖) * ‖w‖ ≤ 17 / 8 := by nlinarith
    have hA : ‖Rg_g (t * μ j) w - (-w)⁻¹‖ * ‖w‖ ^ 2 * ((‖Rg_g (t * μ j) w‖ + ‖(-w)⁻¹‖) * ‖w‖)
        ≤ (9 / 8 * |t * μ j|) * (17 / 8) := by
      gcongr
    calc |μ j| * |‖Rg_g (t * μ j) w‖ ^ 2 - ‖(-w)⁻¹‖ ^ 2| * ‖w‖ ^ 3
        ≤ |μ j| * (‖Rg_g (t * μ j) w - (-w)⁻¹‖ * (‖Rg_g (t * μ j) w‖ + ‖(-w)⁻¹‖)) * ‖w‖ ^ 3 := by
          gcongr
      _ = |μ j| * (‖Rg_g (t * μ j) w - (-w)⁻¹‖ * ‖w‖ ^ 2 *
            ((‖Rg_g (t * μ j) w‖ + ‖(-w)⁻¹‖) * ‖w‖)) := by ring
      _ ≤ |μ j| * ((9 / 8 * |t * μ j|) * (17 / 8)) := by gcongr
      _ ≤ |μ j| * ((9 / 8 * |μ j|) * (17 / 8)) := by gcongr
      _ = 153 / 64 * μ j ^ 2 := by rw [← sq_abs (μ j)]; ring
  have hb : |r| ≤ 153 / 64 * σ / ‖w‖ ^ 3 := by
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hnpos)]
    calc ((Fintype.card ι : ℝ))⁻¹ * |∑ j, μ j * (‖Rg_g (t * μ j) w‖ ^ 2 - ‖(-w)⁻¹‖ ^ 2)|
        ≤ ((Fintype.card ι : ℝ))⁻¹ * ∑ j, 153 / 64 * μ j ^ 2 / ‖w‖ ^ 3 := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hpt j)
      _ = 153 / 64 * σ / ‖w‖ ^ 3 := by
          rw [hσ, ← Finset.sum_div, ← Finset.mul_sum]; ring
  calc |r| * ‖w‖ ^ 3 ≤ 153 / 64 * σ / ‖w‖ ^ 3 * ‖w‖ ^ 3 := by gcongr
    _ = _ := by field_simp

/-- If `Δ x = r₁` then `|Δ| ‖w‖ ≤ 3 ⟨Λ²⟩` and `|Δ| ≤ 4 ⟨Λ²⟩`. -/
private lemma Rg_R2 [Nonempty ι] {μ : ι → ℝ} {t : ℝ} {w : ℂ} (H : Rg_H μ t w) {σ x r Δ : ℝ}
    (hσ : σ = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2)
    (hx : x = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2)
    (hr : r = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j * ‖Rg_g (t * μ j) w‖ ^ 2) (hΔ : Δ * x = r) :
    |Δ| * ‖w‖ ≤ 3 * σ ∧ |Δ| ≤ 4 * σ := by
  have hW9 := H.hw
  have hW : 0 < ‖w‖ := by linarith
  have R1 := Rg_R1 H hσ hr
  have S3 := Rg_S3 H hx
  have hx0 : 0 < x := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg ‖w‖]
  obtain ⟨hσ0, -⟩ := Rg_sigma_bd H.bd hσ
  have h1 : |Δ| * x = |r| := by rw [← hΔ, abs_mul, abs_of_pos hx0]
  have h2 : |Δ| * (81 / 100) * ‖w‖ ≤ |r| * ‖w‖ ^ 3 := by
    calc |Δ| * (81 / 100) * ‖w‖ ≤ |Δ| * (x * ‖w‖ ^ 2) * ‖w‖ := by gcongr
      _ = |Δ| * x * ‖w‖ ^ 3 := by ring
      _ = _ := by rw [h1]
  have h3 : |Δ| * ‖w‖ ≤ 3 * σ := by nlinarith [abs_nonneg Δ]
  refine ⟨h3, ?_⟩
  nlinarith [abs_nonneg Δ]

end RgScalar5

section RgScalar6

variable {ι : Type*} [Fintype ι]

/-- `n⁻¹ Σ |g_j|² (μ_j - Δ) = 0` when `Δ x = r₁`. -/
private lemma Rg_R3 [Nonempty ι] {μ : ι → ℝ} {t : ℝ} {w : ℂ} {x r Δ : ℝ}
    (hx : x = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2)
    (hr : r = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j * ‖Rg_g (t * μ j) w‖ ^ 2) (hΔ : Δ * x = r) :
    ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2 * (μ j - Δ) = 0 := by
  have hn' : ((Fintype.card ι : ℝ)) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have e : ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2 * (μ j - Δ) =
      (∑ j, μ j * ‖Rg_g (t * μ j) w‖ ^ 2) - Δ * ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h1 : ∑ j, μ j * ‖Rg_g (t * μ j) w‖ ^ 2 = (Fintype.card ι : ℝ) * r := by
    rw [hr, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
  have h2 : ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2 = (Fintype.card ι : ℝ) * x := by
    rw [hx, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
  rw [e, h1, h2, ← hΔ]
  ring

/-- `‖n⁻¹ Σ g_j² (μ_j - Δ)‖ ≤ 28 Im m ⟨Λ²⟩` when `Δ x = r₁`. -/
private lemma Rg_R4 [Nonempty ι] {μ : ι → ℝ} {t : ℝ} {w : ℂ} (H : Rg_H μ t w) {m : ℂ}
    (hm : m = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, Rg_g (t * μ j) w) (ham : 0 < m.im) {σ x r Δ : ℝ}
    (hσ : σ = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2)
    (hx : x = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Rg_g (t * μ j) w‖ ^ 2)
    (hr : r = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j * ‖Rg_g (t * μ j) w‖ ^ 2) (hΔ : Δ * x = r) :
    ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, Rg_g (t * μ j) w ^ 2 * ((μ j - Δ : ℝ) : ℂ)‖ ≤
      28 * (m.im * σ) := by
  have hW9 := H.hw
  have hW : 0 < ‖w‖ := by linarith
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hn : ((Fintype.card ι : ℂ)) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hw0 : w ≠ 0 := norm_pos_iff.1 hW
  obtain ⟨hσ0, hσ1⟩ := Rg_sigma_bd H.bd hσ
  have S3 := Rg_S3 H hx
  have S4 := Rg_S4 hm hx
  obtain ⟨R2a, R2b⟩ := Rg_R2 H hσ hx hr hΔ
  have hx0 : 0 < x := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg ‖w‖]
  have hwim : 0 < w.im := by
    by_contra h
    push Not at h
    nlinarith
  have R3 := Rg_R3 hx hr hΔ
  set g : ι → ℂ := fun j => Rg_g (t * μ j) w with hg
  set c : ι → ℂ := fun j => ((‖g j‖ ^ 2 : ℝ) : ℂ) with hc
  -- pointwise decomposition
  have hpt : ∀ j, g j ^ 2 * ((μ j - Δ : ℝ) : ℂ) = ((‖g j‖ ^ 2 * (μ j - Δ) : ℝ) : ℂ) +
      2 * Complex.I * (w.im : ℂ) * (g j * c j * ((μ j - Δ : ℝ) : ℂ)) := by
    intro j
    have h1 := Rg_sq_id (g j)
    have h2 : (g j).im = w.im * ‖g j‖ ^ 2 := Rg_im_g _ _
    rw [h1, h2]
    simp only [hc]
    push_cast
    ring
  have hT : ((Fintype.card ι : ℂ))⁻¹ * ∑ j, g j ^ 2 * ((μ j - Δ : ℝ) : ℂ) =
      2 * Complex.I * (w.im : ℂ) * (((Fintype.card ι : ℂ))⁻¹ *
        ∑ j, g j * c j * ((μ j - Δ : ℝ) : ℂ)) := by
    rw [Finset.sum_congr rfl fun j _ => hpt j, Finset.sum_add_distrib, ← Finset.mul_sum]
    have : ∑ j, ((‖g j‖ ^ 2 * (μ j - Δ) : ℝ) : ℂ) = 0 := by
      rw [← Complex.ofReal_sum, R3]; simp
    rw [this, zero_add]
    ring
  rw [hT]
  set R := ((Fintype.card ι : ℂ))⁻¹ * ∑ j, g j * c j * ((μ j - Δ : ℝ) : ℂ) with hR
  have hTR : ‖2 * Complex.I * (w.im : ℂ) * R‖ = 2 * w.im * ‖R‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hwim]
    simp
  rw [hTR]
  -- the bound on `R`
  set g0 : ℂ := (-w)⁻¹ with hg0def
  set c0 : ℂ := ((‖g0‖ ^ 2 : ℝ) : ℂ) with hc0def
  have hg0n : ‖g0‖ * ‖w‖ = 1 := by
    rw [hg0def, norm_inv, norm_neg]; field_simp
  have hRsplit : R = ((Fintype.card ι : ℂ))⁻¹ * (∑ j, ((μ j : ℝ) : ℂ) * (g j * c j - g0 * c0)) -
      (Δ : ℂ) * (((Fintype.card ι : ℂ))⁻¹ * ∑ j, g j * c j) := by
    have hs0 : ∑ j, ((μ j : ℝ) : ℂ) = 0 := by exact_mod_cast H.sum
    have e1 : ∀ j, g j * c j * ((μ j - Δ : ℝ) : ℂ) = ((μ j : ℝ) : ℂ) * (g j * c j - g0 * c0) +
        ((μ j : ℝ) : ℂ) * (g0 * c0) - (Δ : ℂ) * (g j * c j) := by
      intro j; push_cast; ring
    rw [hR, Finset.sum_congr rfl fun j _ => e1 j, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, hs0, zero_mul, add_zero, ← Finset.mul_sum]
    ring
  -- first part
  have hB1 : ∀ j, ‖((μ j : ℝ) : ℂ) * (g j * c j - g0 * c0)‖ ≤ 2187 / 512 * μ j ^ 2 / ‖w‖ ^ 4 := by
    intro j
    obtain ⟨-, h2, -, h4⟩ := Rg_pt (t * μ j) (H.nu j) H.hw
    have hu : ‖g j‖ ≤ 9 / 8 * ‖w‖⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hW]; exact h2
    have hv : ‖g0‖ ≤ 9 / 8 * ‖w‖⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hW]; nlinarith [norm_nonneg g0]
    have hcs := Rg_cube_sub (g j) g0 hu hv
    have h5 := Rg_nu_sq (μ := μ) H.ht j
    have e : (c j) = ((‖g j‖ ^ 2 : ℝ) : ℂ) := rfl
    rw [le_div_iff₀ (by positivity), norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hd : ‖g j - g0‖ * ‖w‖ ^ 2 ≤ 9 / 8 * |t * μ j| := h4
    have hB : (9 / 8 * ‖w‖⁻¹) ^ 2 * ‖w‖ ^ 2 = 81 / 64 := by field_simp; norm_num
    calc |μ j| * ‖g j * c j - g0 * c0‖ * ‖w‖ ^ 4
        ≤ |μ j| * (3 * (9 / 8 * ‖w‖⁻¹) ^ 2 * ‖g j - g0‖) * ‖w‖ ^ 4 := by
          gcongr
      _ = |μ j| * (3 * ((9 / 8 * ‖w‖⁻¹) ^ 2 * ‖w‖ ^ 2) * (‖g j - g0‖ * ‖w‖ ^ 2)) := by ring
      _ = |μ j| * (3 * (81 / 64) * (‖g j - g0‖ * ‖w‖ ^ 2)) := by rw [hB]
      _ ≤ |μ j| * (3 * (81 / 64) * (9 / 8 * |t * μ j|)) := by gcongr
      _ ≤ |μ j| * (3 * (81 / 64) * (9 / 8 * |μ j|)) := by gcongr
      _ = 2187 / 512 * μ j ^ 2 := by rw [← sq_abs (μ j)]; ring
  have hA1 : ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((μ j : ℝ) : ℂ) * (g j * c j - g0 * c0)‖ *
      ‖w‖ ^ 4 ≤ 2187 / 512 * σ := by
    have hb := Rg_avg_le (fun j => ((μ j : ℝ) : ℂ) * (g j * c j - g0 * c0))
      (fun j => 2187 / 512 * μ j ^ 2 / ‖w‖ ^ 4) hB1
    have hsum : ((Fintype.card ι : ℝ))⁻¹ * ∑ j, 2187 / 512 * μ j ^ 2 / ‖w‖ ^ 4 =
        2187 / 512 * σ / ‖w‖ ^ 4 := by
      rw [hσ, ← Finset.sum_div, ← Finset.mul_sum]; ring
    rw [hsum] at hb
    calc _ ≤ 2187 / 512 * σ / ‖w‖ ^ 4 * ‖w‖ ^ 4 := by gcongr
      _ = _ := by field_simp
  -- second part
  have hB2 : ∀ j, ‖g j * c j‖ ≤ 729 / 512 / ‖w‖ ^ 3 := by
    intro j
    obtain ⟨-, h2, -, -⟩ := Rg_pt (t * μ j) (H.nu j) H.hw
    have hG0 : 0 ≤ ‖g j‖ := norm_nonneg _
    rw [le_div_iff₀ (by positivity), norm_mul, hc]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖g j‖ ^ 2)]
    calc ‖g j‖ * ‖g j‖ ^ 2 * ‖w‖ ^ 3 = (‖g j‖ * ‖w‖) ^ 3 := by ring
      _ ≤ (9 / 8) ^ 3 := by gcongr
      _ = _ := by norm_num
  have hA2 : ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, g j * c j‖ * ‖w‖ ^ 3 ≤ 729 / 512 := by
    have hb := Rg_avg_le (fun j => g j * c j) (fun j => 729 / 512 / ‖w‖ ^ 3) hB2
    have hsum : ((Fintype.card ι : ℝ))⁻¹ * ∑ _j : ι, 729 / 512 / ‖w‖ ^ 3 = 729 / 512 / ‖w‖ ^ 3 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    rw [hsum] at hb
    calc _ ≤ 729 / 512 / ‖w‖ ^ 3 * ‖w‖ ^ 3 := by gcongr
      _ = _ := by field_simp
  have hRb : ‖R‖ * ‖w‖ ^ 4 ≤ 9 * σ := by
    have h1 : ‖R‖ ≤ ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((μ j : ℝ) : ℂ) * (g j * c j - g0 * c0)‖ +
        |Δ| * ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, g j * c j‖ := by
      rw [hRsplit]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul (Δ : ℂ), Complex.norm_real, Real.norm_eq_abs]
    have h2 : |Δ| * ‖w‖ * (‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, g j * c j‖ * ‖w‖ ^ 3) ≤
        3 * σ * (729 / 512) := by
      gcongr
    calc ‖R‖ * ‖w‖ ^ 4 ≤ (‖((Fintype.card ι : ℂ))⁻¹ *
          ∑ j, ((μ j : ℝ) : ℂ) * (g j * c j - g0 * c0)‖ +
        |Δ| * ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, g j * c j‖) * ‖w‖ ^ 4 := by gcongr
      _ = ‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((μ j : ℝ) : ℂ) * (g j * c j - g0 * c0)‖ * ‖w‖ ^ 4 +
          |Δ| * ‖w‖ * (‖((Fintype.card ι : ℂ))⁻¹ * ∑ j, g j * c j‖ * ‖w‖ ^ 3) := by ring
      _ ≤ 2187 / 512 * σ + 3 * σ * (729 / 512) := by gcongr
      _ ≤ 9 * σ := by nlinarith
  have hR2 : 2 * ‖R‖ ≤ 28 * x * σ := by
    have hW4 : 0 < ‖w‖ ^ 4 := by positivity
    refine le_of_mul_le_mul_right ?_ hW4
    have h3 : 28 * x * σ * ‖w‖ ^ 4 = 28 * σ * (x * ‖w‖ ^ 2) * ‖w‖ ^ 2 := by ring
    have h4 : (81 / 100 : ℝ) ≤ ‖w‖ ^ 2 := by nlinarith
    rw [h3]
    nlinarith [mul_nonneg hσ0 (sub_nonneg.2 S3), mul_nonneg hσ0 (sub_nonneg.2 h4),
      mul_nonneg (mul_nonneg hσ0 (sub_nonneg.2 S3)) (sub_nonneg.2 h4)]
  calc 2 * w.im * ‖R‖ = w.im * (2 * ‖R‖) := by ring
    _ ≤ w.im * (28 * x * σ) := by gcongr
    _ = 28 * (m.im * σ) := by rw [S4]; ring

end RgScalar6

/-! ### The spectral data of `m_t(z)` and `M_t(z)`, and the matrix form of the estimates -/

section RgMatrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The spectral data: `Λ = U diag(μ) U^*` with `Σ μ_j = 0`, `|μ_j| ≤ 1/10`,
`⟨Λ²⟩ = n⁻¹ Σ μ_j²`, and `m_t(z) = n⁻¹ Σ g_j`, `M_t(z) = U diag(g) U^*` with
`g_j = (tμ_j - w)⁻¹`, `w = z + m_t(z)`, `‖w‖ ≥ 9/10`, `‖m_t(z)‖ < 1`. -/
private lemma Rg_data {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hn : ntr Λ = 0)
    (hℓ : opNorm Λ ≤ 1 / 10) {t : ℝ} (ht : |t| ≤ 1) {z : ℂ} (hz : 0 < z.im) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ), Λ = Rg_cd U (fun j => (μ j : ℂ)) ∧
      avgSq Λ = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 ∧
      Rg_H μ t (z + mSol ((t : ℂ) • Λ) z) ∧ 0 < (mSol ((t : ℂ) • Λ) z).im ∧
      ‖mSol ((t : ℂ) • Λ) z‖ < 1 ∧
      mSol ((t : ℂ) • Λ) z = ((Fintype.card ι : ℂ))⁻¹ *
        ∑ j, Rg_g (t * μ j) (z + mSol ((t : ℂ) • Λ) z) ∧
      MSol ((t : ℂ) • Λ) z = Rg_cd U (fun j => Rg_g (t * μ j) (z + mSol ((t : ℂ) • Λ) z)) := by
  obtain ⟨U, μ, hΛd, hμ⟩ := Rg_decomp hΛ
  have hμ1 : ∀ j, |μ j| ≤ 1 / 10 := fun j => (hμ j).trans hℓ
  have hsum : ∑ j, μ j = 0 := by
    have := hn
    rw [hΛd, Rg_ntr_cd] at this
    have hnn : ((Fintype.card ι : ℂ))⁻¹ ≠ 0 := by
      apply inv_ne_zero; exact_mod_cast Fintype.card_ne_zero
    have h2 : ∑ j, (μ j : ℂ) = 0 := (mul_eq_zero.1 this).resolve_left hnn
    exact_mod_cast h2
  have hav : avgSq Λ = ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 := by
    rw [hΛd]
    simp only [avgSq, Rg_cd_mul, Rg_ntr_cd]
    rw [show ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (μ j : ℂ) * (μ j : ℂ) =
      ((((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2 : ℝ) : ℂ) by push_cast; simp [sq]]
    rw [Complex.ofReal_re]
  obtain ⟨hmim, hmeq, hMeq⟩ := Rg_bridge U μ t hz
  have hts : (t : ℂ) • Λ = (t : ℂ) • Rg_cd U (fun j => (μ j : ℂ)) := by rw [← hΛd]
  have hHt : ((t : ℂ) • Λ).IsHermitian := Rg_herm_smul hΛ t
  have hnt : opNorm ((t : ℂ) • Λ) ≤ 1 / 10 := by
    rw [Rg_opNorm_smul]
    calc |t| * opNorm Λ ≤ 1 * (1 / 10) :=
          mul_le_mul ht hℓ (by unfold opNorm; positivity) zero_le_one
      _ = 1 / 10 := one_mul _
  obtain ⟨hap1, hap2, -⟩ := mSol_apriori ((t : ℂ) • Λ) hHt hnt z hz
  rw [Rg_opNorm_smul] at hap1
  have hw : 9 / 10 ≤ ‖z + mSol ((t : ℂ) • Λ) z‖ := by
    have h1 : |t| * opNorm Λ ≤ 1 / 10 := by
      have := hnt; rwa [Rg_opNorm_smul] at this
    linarith
  refine ⟨U, μ, hΛd, hav, ⟨hsum, hμ1, ht, hw⟩, ?_, hap2, ?_, ?_⟩
  · rw [hts]; exact hmim
  · rw [hts]; exact hmeq
  · rw [hts]; exact hMeq

end RgMatrix

section RgMatrix2

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The estimates for `Δ_ev(z) = Re(z + m + m⁻¹)` of (5.2) [definition_shift_eigenvector]:
`|Δ_ev| ≤ (5/2)⟨Λ²⟩`, `‖1 + (z + m - Δ_ev) m‖ ≤ (7/2) Im m ⟨Λ²⟩`, `Im m ‖z + m‖² ≥ (81/100) Im z`,
for Hermitian `Λ` with `⟨Λ⟩ = 0`, `‖Λ‖ ≤ 1/10` and `Im z > 0`. -/
private lemma Rg_core1 {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hn : ntr Λ = 0)
    (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ} (hz : 0 < z.im) :
    |(z + mSol Λ z + (mSol Λ z)⁻¹).re| ≤ 5 / 2 * avgSq Λ ∧
      ‖1 + (z + mSol Λ z - (((z + mSol Λ z + (mSol Λ z)⁻¹).re : ℝ) : ℂ)) * mSol Λ z‖ ≤
        7 / 2 * ((mSol Λ z).im * avgSq Λ) ∧
      81 / 100 * z.im ≤ (mSol Λ z).im * ‖z + mSol Λ z‖ ^ 2 ∧ 0 < (mSol Λ z).im ∧
      ‖mSol Λ z‖ < 1 ∧ 0 ≤ avgSq Λ := by
  obtain ⟨U, μ, hΛd, hav, H, ham, hm1, hm, hM⟩ := Rg_data hΛ hn hℓ (t := 1) (by simp) hz
  simp only [Complex.ofReal_one, one_smul] at H ham hm1 hm hM
  have hS5 := Rg_S5 H hm ham hav (x := ((Fintype.card ι : ℝ))⁻¹ *
    ∑ j, ‖Rg_g (1 * μ j) (z + mSol Λ z)‖ ^ 2) rfl
  have hS3 := Rg_S3 H (x := ((Fintype.card ι : ℝ))⁻¹ *
    ∑ j, ‖Rg_g (1 * μ j) (z + mSol Λ z)‖ ^ 2) rfl
  have hS4 := Rg_S4 hm (x := ((Fintype.card ι : ℝ))⁻¹ *
    ∑ j, ‖Rg_g (1 * μ j) (z + mSol Λ z)‖ ^ 2) rfl
  refine ⟨hS5.1, hS5.2, ?_, ham, hm1, (Rg_sigma_bd H.bd hav).1⟩
  set x := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖Rg_g (1 * μ j) (z + mSol Λ z)‖ ^ 2
  have hwim : (z + mSol Λ z).im = z.im + (mSol Λ z).im := by simp
  have hx0 : 0 < x := by
    by_contra h
    push Not at h
    have := H.hw
    nlinarith [sq_nonneg ‖z + mSol Λ z‖]
  have h1 : z.im * x ≤ (mSol Λ z).im := by
    rw [hS4, hwim]; nlinarith
  have hW2 : 0 ≤ ‖z + mSol Λ z‖ ^ 2 := sq_nonneg _
  nlinarith

end RgMatrix2

section RgMatrix3

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Rg_gmg (g : ℂ) (a : ℝ) :
    g * (a : ℂ) * star g = ((a * ‖g‖ ^ 2 : ℝ) : ℂ) ∧
      star g * (a : ℂ) * g = ((a * ‖g‖ ^ 2 : ℝ) : ℂ) ∧ g * star g = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
  have h : g * star g = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine ⟨?_, ?_, h⟩
  · calc g * (a : ℂ) * star g = (a : ℂ) * (g * star g) := by ring
      _ = _ := by rw [h]; push_cast; ring
  · calc star g * (a : ℂ) * g = (a : ℂ) * (g * star g) := by ring
      _ = _ := by rw [h]; push_cast; ring

omit [Nonempty ι] in
private lemma Rg_ntr3 (U : Matrix.unitaryGroup ι ℂ) (d₁ d₂ d₃ : ι → ℂ) :
    ntr (Rg_cd U d₁ * Rg_cd U d₂ * Rg_cd U d₃) =
      ((Fintype.card ι : ℂ))⁻¹ * ∑ j, d₁ j * d₂ j * d₃ j := by
  rw [Rg_cd_mul, Rg_cd_mul, Rg_ntr_cd]

omit [DecidableEq ι] [Nonempty ι] in
private lemma Rg_cast_avg (f : ι → ℝ) :
    ((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((f j : ℝ) : ℂ) =
      ((((Fintype.card ι : ℝ))⁻¹ * ∑ j, f j : ℝ) : ℂ) := by
  push_cast; rfl

/-- Matrix form of the estimates for `Δ(t)` of (5.19) [definition_shift_eigenvalue]: with
`M = M_t(z)` and `Δ = Re ⟨M Λ M^*⟩ / ⟨M M^*⟩`: `|Δ| ≤ 4⟨Λ²⟩`, the mixed averages
`⟨M Λ̂ M^*⟩`, `⟨M^* Λ̂ M⟩` vanish and `⟨M Λ̂ M⟩`, `⟨M^* Λ̂ M^*⟩` are `O(Im m_t ⟨Λ²⟩)`,
`Λ̂ = Λ - Δ`. -/
private lemma Rg_core2 {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hn : ntr Λ = 0)
    (hℓ : opNorm Λ ≤ 1 / 10) {t : ℝ} (ht : |t| ≤ 1) {z : ℂ} (hz : 0 < z.im)
    {M : Matrix ι ι ℂ} (hM : M = MSol ((t : ℂ) • Λ) z) {Δ : ℝ}
    (hΔ : Δ = (ntr (M * Λ * Mᴴ) / ntr (M * Mᴴ)).re) :
    |Δ| ≤ 4 * avgSq Λ ∧ ntr (M * (Λ - (Δ : ℂ) • (1 : Matrix ι ι ℂ)) * Mᴴ) = 0 ∧
      ntr (Mᴴ * (Λ - (Δ : ℂ) • (1 : Matrix ι ι ℂ)) * M) = 0 ∧
      ‖ntr (M * (Λ - (Δ : ℂ) • (1 : Matrix ι ι ℂ)) * M)‖ ≤
        28 * ((mSol ((t : ℂ) • Λ) z).im * avgSq Λ) ∧
      ‖ntr (Mᴴ * (Λ - (Δ : ℂ) • (1 : Matrix ι ι ℂ)) * Mᴴ)‖ ≤
        28 * ((mSol ((t : ℂ) • Λ) z).im * avgSq Λ) := by
  obtain ⟨U, μ, hΛd, hav, H, ham, hm1, hm, hMd⟩ := Rg_data hΛ hn hℓ ht hz
  set w := z + mSol ((t : ℂ) • Λ) z with hw
  set m := mSol ((t : ℂ) • Λ) z with hmdef
  set g : ι → ℂ := fun j => Rg_g (t * μ j) w with hg
  have hM' : M = Rg_cd U g := by rw [hM, hMd]
  have hMh : Mᴴ = Rg_cd U (fun j => star (g j)) := by rw [hM', Rg_cd_conjTranspose]
  have hΛΔ : Λ - (Δ : ℂ) • (1 : Matrix ι ι ℂ) = Rg_cd U (fun j => (μ j : ℂ) - (Δ : ℂ)) := by
    rw [hΛd, Rg_cd_sub_smul_one]
  set x : ℝ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, ‖g j‖ ^ 2 with hxdef
  set r : ℝ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j * ‖g j‖ ^ 2 with hrdef
  have hx0 : 0 < x := by
    have S3 := Rg_S3 H (x := x) rfl
    by_contra h
    push Not at h
    have := H.hw
    nlinarith [sq_nonneg ‖w‖]
  have hΛ0 : Λ = Rg_cd U (fun j => (μ j : ℂ)) := hΛd
  -- the two traces
  have tr1 : ntr (M * Λ * Mᴴ) = (r : ℂ) := by
    rw [hMh, hM', hΛ0, Rg_ntr3]
    have e : ∀ j, g j * (μ j : ℂ) * star (g j) = ((μ j * ‖g j‖ ^ 2 : ℝ) : ℂ) :=
      fun j => (Rg_gmg (g j) (μ j)).1
    simp only [e]
    exact Rg_cast_avg _
  have tr2 : ntr (M * Mᴴ) = (x : ℂ) := by
    rw [hMh, hM', Rg_cd_mul, Rg_ntr_cd]
    have e : ∀ j, g j * star (g j) = ((‖g j‖ ^ 2 : ℝ) : ℂ) := fun j => (Rg_gmg (g j) 0).2.2
    simp only [e]
    exact Rg_cast_avg _
  have hΔx : Δ * x = r := by
    rw [hΔ, tr1, tr2, ← Complex.ofReal_div, Complex.ofReal_re]
    field_simp
  obtain ⟨R2a, R2b⟩ := Rg_R2 H hav rfl rfl hΔx
  have hR3 := Rg_R3 (x := x) rfl rfl hΔx
  have hn' : ((Fintype.card ι : ℝ)) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hR4 := Rg_R4 H hm ham hav (x := x) (r := r) rfl rfl hΔx
  refine ⟨R2b, ?_, ?_, ?_, ?_⟩
  · rw [hMh, hM', hΛΔ, Rg_ntr3]
    have e : ∀ j, g j * ((μ j : ℂ) - (Δ : ℂ)) * star (g j) =
        ((‖g j‖ ^ 2 * (μ j - Δ) : ℝ) : ℂ) := by
      intro j
      have := (Rg_gmg (g j) (μ j - Δ)).1
      push_cast at this ⊢
      rw [this]; ring
    simp only [e]
    rw [Rg_cast_avg, hR3]
    simp
  · rw [hMh, hM', hΛΔ, Rg_ntr3]
    have e : ∀ j, star (g j) * ((μ j : ℂ) - (Δ : ℂ)) * g j =
        ((‖g j‖ ^ 2 * (μ j - Δ) : ℝ) : ℂ) := by
      intro j
      have := (Rg_gmg (g j) (μ j - Δ)).2.1
      push_cast at this ⊢
      rw [this]; ring
    simp only [e]
    rw [Rg_cast_avg, hR3]
    simp
  · rw [hM', hΛΔ, Rg_ntr3]
    have e : ∀ j, g j * ((μ j : ℂ) - (Δ : ℂ)) * g j = g j ^ 2 * ((μ j - Δ : ℝ) : ℂ) := by
      intro j; push_cast; ring
    simp only [e]
    exact hR4
  · have e : ntr (Mᴴ * (Λ - (Δ : ℂ) • (1 : Matrix ι ι ℂ)) * Mᴴ) =
        (starRingEnd ℂ) (ntr (M * (Λ - (Δ : ℂ) • (1 : Matrix ι ι ℂ)) * M)) := by
      rw [hMh, hM', hΛΔ, Rg_ntr3, Rg_ntr3]
      simp [map_sum, map_mul, map_inv₀, Complex.conj_ofReal]
    rw [e, Complex.norm_conj]
    rw [hM', hΛΔ, Rg_ntr3]
    have e : ∀ j, g j * ((μ j : ℂ) - (Δ : ℂ)) * g j = g j ^ 2 * ((μ j - Δ : ℝ) : ℂ) := by
      intro j; push_cast; ring
    simp only [e]
    exact hR4

end RgMatrix3

section RgCompare

/-- If `p² + z₀ p + 1 = 0` with `Im p > 0`, `Im z₀ > 0` and `‖m² + z₀ m + 1‖ ≤ K Im m σ` with
`2Kσ ≤ Im m`, then `Im m / 2 ≤ Im p ≤ (3/2) Im m`. -/
private lemma Rg_compare {m p z₀ : ℂ} {K σ : ℝ} (hm : 0 < m.im) (hp : 0 < p.im)
    (hz₀ : 0 < z₀.im) (hroot : p ^ 2 + z₀ * p + 1 = 0)
    (hQ : ‖m ^ 2 + z₀ * m + 1‖ ≤ K * (m.im * σ)) (hbig : 2 * (K * σ) ≤ m.im) :
    m.im / 2 ≤ p.im ∧ p.im ≤ 3 / 2 * m.im := by
  set q : ℂ := -z₀ - p with hq
  have hprod : m ^ 2 + z₀ * m + 1 = (m - p) * (m - q) := by
    have : (m - p) * (m - q) = (m ^ 2 + z₀ * m + 1) - (p ^ 2 + z₀ * p + 1) := by
      rw [hq]; ring
    rw [this, hroot, sub_zero]
  have h1 : |m.im - p.im| ≤ ‖m - p‖ := by
    have := Complex.abs_im_le_norm (m - p)
    rwa [Complex.sub_im] at this
  have hqim : (m - q).im = m.im + z₀.im + p.im := by rw [hq]; simp; ring
  have h2 : m.im + p.im ≤ ‖m - q‖ := by
    have := Complex.abs_im_le_norm (m - q)
    rw [hqim, abs_of_pos (by linarith)] at this
    linarith
  have h3 : |m.im - p.im| * (m.im + p.im) ≤ K * (m.im * σ) := by
    calc |m.im - p.im| * (m.im + p.im) ≤ ‖m - p‖ * ‖m - q‖ := by
          gcongr
      _ = ‖m ^ 2 + z₀ * m + 1‖ := by rw [hprod, norm_mul]
      _ ≤ _ := hQ
  have h4 : |m.im - p.im| * m.im ≤ K * σ * m.im := by
    calc |m.im - p.im| * m.im ≤ |m.im - p.im| * (m.im + p.im) := by gcongr; linarith
      _ ≤ K * (m.im * σ) := h3
      _ = K * σ * m.im := by ring
  have h5 : |m.im - p.im| ≤ K * σ := le_of_mul_le_mul_right h4 hm
  have h6 : |m.im - p.im| ≤ m.im / 2 := by linarith
  rw [abs_le] at h6
  constructor <;> linarith [h6.1, h6.2]

end RgCompare

/-! ### Exponent bookkeeping for (2.8) [eq:condA2] -/

section RgExp

private lemma Rg_rpow_sq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num; ring_nf

/-- For `K > 0`, `a > 0`: `K ≤ N^a` once `N ≥ ⌈K^{1/a}⌉`. -/
private lemma Rg_pow_ge {K a : ℝ} (hK : 0 < K) (ha : 0 < a) {N : ℕ}
    (hN : ⌈K ^ (1 / a)⌉₊ ≤ N) : K ≤ (N : ℝ) ^ a := by
  have h1 : K ^ (1 / a) ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  calc K = (K ^ (1 / a)) ^ a := by
        rw [← Real.rpow_mul hK.le, one_div_mul_cancel ha.ne', Real.rpow_one]
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (by positivity) h1 ha.le

/-- With `σ ≤ 4D h²/n`, `h ≤ n^{1/3-ε_A} r^{-1/3}`, `η = n^{-2/3+ε} r^{-1/3}` and `ε < 2ε_A`:
`σ η ≤ 4D/n` and `σ² ≤ 16 D² n^{-4ε_A} η`. -/
private lemma Rg_sig_eta {n r D εA ε h σ η : ℝ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hD : 0 < D)
    (_hεA : 0 < εA) (hε : 0 < ε) (hε' : ε < 2 * εA) (hh0 : 0 ≤ h) (hσ0 : 0 ≤ σ)
    (hσ : σ ≤ 4 * D * h ^ 2 / n) (hhs : h ≤ n ^ ((1 / 3 : ℝ) - εA) * r ^ (-(1 / 3 : ℝ)))
    (hη : η = n ^ (-(2 / 3 : ℝ) + ε) * r ^ (-(1 / 3 : ℝ))) :
    σ * η ≤ 4 * D / n ∧ σ ^ 2 ≤ 16 * D ^ 2 * n ^ (-(4 * εA)) * η := by
  have hn0 : 0 < n := by linarith
  have hr0 : 0 < r := by linarith
  set a : ℝ := -(1 / 3 : ℝ) - 2 * εA with ha
  have hS : σ ≤ 4 * D * (n ^ a * r ^ (-(2 / 3 : ℝ))) := by
    have h2 : h ^ 2 ≤ n ^ (2 * ((1 / 3 : ℝ) - εA)) * r ^ (2 * (-(1 / 3 : ℝ))) := by
      calc h ^ 2 ≤ (n ^ ((1 / 3 : ℝ) - εA) * r ^ (-(1 / 3 : ℝ))) ^ 2 := by gcongr
        _ = _ := by rw [mul_pow, Rg_rpow_sq hn0.le, Rg_rpow_sq hr0.le]
    have h3 : n ^ (2 * ((1 / 3 : ℝ) - εA)) / n = n ^ a := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hn0]
      congr 1
      rw [ha]; ring
    have h4 : r ^ (2 * (-(1 / 3 : ℝ))) = r ^ (-(2 / 3 : ℝ)) := by congr 1; ring
    calc σ ≤ 4 * D * h ^ 2 / n := hσ
      _ ≤ 4 * D * (n ^ (2 * ((1 / 3 : ℝ) - εA)) * r ^ (2 * (-(1 / 3 : ℝ)))) / n := by gcongr
      _ = 4 * D * (n ^ (2 * ((1 / 3 : ℝ) - εA)) / n) * r ^ (2 * (-(1 / 3 : ℝ))) := by ring
      _ = _ := by rw [h3, h4]; ring
  constructor
  · have hη0 : 0 ≤ η := by rw [hη]; positivity
    have e1 : n ^ a * n ^ (-(2 / 3 : ℝ) + ε) = n ^ (a + (-(2 / 3 : ℝ) + ε)) :=
      (Real.rpow_add hn0 _ _).symm
    have e2 : r ^ (-(2 / 3 : ℝ)) * r ^ (-(1 / 3 : ℝ)) = r ^ (-(2 / 3 : ℝ) + -(1 / 3 : ℝ)) :=
      (Real.rpow_add hr0 _ _).symm
    have b1 : n ^ (a + (-(2 / 3 : ℝ) + ε)) ≤ n ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by rw [ha]; linarith)
    have b2 : r ^ (-(2 / 3 : ℝ) + -(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num)
    rw [Real.rpow_neg_one] at b1
    calc σ * η ≤ 4 * D * (n ^ a * r ^ (-(2 / 3 : ℝ))) * η := by gcongr
      _ = 4 * D * (n ^ (a + (-(2 / 3 : ℝ) + ε)) * r ^ (-(2 / 3 : ℝ) + -(1 / 3 : ℝ))) := by
        rw [hη, ← e1, ← e2]; ring
      _ ≤ 4 * D * (n⁻¹ * 1) := by gcongr
      _ = 4 * D / n := by ring
  · have e3 : (n ^ a * r ^ (-(2 / 3 : ℝ))) ^ 2 = n ^ (2 * a) * r ^ (-(4 / 3 : ℝ)) := by
      rw [mul_pow, Rg_rpow_sq hn0.le, Rg_rpow_sq hr0.le]
      congr 2; ring
    have e4 : n ^ (-(4 * εA)) * n ^ (-(2 / 3 : ℝ) + ε) = n ^ (-(4 * εA) + (-(2 / 3 : ℝ) + ε)) :=
      (Real.rpow_add hn0 _ _).symm
    have b1 : n ^ (2 * a) ≤ n ^ (-(4 * εA) + (-(2 / 3 : ℝ) + ε)) :=
      Real.rpow_le_rpow_of_exponent_le hn (by rw [ha]; linarith)
    have b2 : r ^ (-(4 / 3 : ℝ)) ≤ r ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
    calc σ ^ 2 ≤ (4 * D * (n ^ a * r ^ (-(2 / 3 : ℝ)))) ^ 2 := by gcongr
      _ = 16 * D ^ 2 * (n ^ (2 * a) * r ^ (-(4 / 3 : ℝ))) := by rw [mul_pow, e3]; ring
      _ ≤ 16 * D ^ 2 * (n ^ (-(4 * εA) + (-(2 / 3 : ℝ) + ε)) * r ^ (-(1 / 3 : ℝ))) := by gcongr
      _ = 16 * D ^ 2 * n ^ (-(4 * εA)) * η := by rw [hη, ← e4]; ring

end RgExp

/-! ### Block algebra for `Λ = lam D N A` -/

section RgLamAlg

private lemma Rg_ext_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) {z : ℂ}
    (hz : 0 < z.im) : mExt Λ z = mSol Λ z ∧ MExt Λ z = MSol Λ z := by
  have h : mExt Λ z = mSol Λ z := by unfold mExt; simp [hz]
  refine ⟨h, ?_⟩
  unfold MExt MSol
  rw [h]

private lemma Rg_Ea_sum (D N : ℕ) : ∑ a : Fin D, Ea D N a = 1 := by
  ext p q
  simp only [Matrix.sum_apply, Ea, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : p = q
  · subst h; simp
  · simp [h]

private lemma Rg_ntr_Ea (D N : ℕ) (hD : 0 < D) (hN : 1 ≤ N) (a : Fin D) :
    ntr (Ea D N a) = (D : ℂ)⁻¹ := by
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  unfold ntr Ea
  rw [Matrix.trace_diagonal]
  have : ∑ p : Idx D N, (if p.1 = a then (1 : ℂ) else 0) = (N : ℂ) := by
    rw [Fintype.sum_prod_type]
    have h1 : ∀ x : Fin D, ∑ y : Fin N, (if (x, y).1 = a then (1 : ℂ) else 0) =
        if x = a then (N : ℂ) else 0 := by
      intro x; by_cases h : x = a <;> simp [h]
    simp only [h1]
    simp
  rw [this]
  simp only [Fintype.card_prod, Fintype.card_fin]
  push_cast
  field_simp

private lemma Rg_ntr_lam_Ea (D N : ℕ) (hD : 2 ≤ D) (A : Matrix (Fin N) (Fin N) ℂ) (a : Fin D) :
    ntr (lam D N A * Ea D N a) = 0 := by
  unfold ntr Ea Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_diagonal, Rg_lam_diag D N hD A, zero_mul,
    Finset.sum_const_zero, mul_zero]

private lemma Rg_ntr_sub {ι : Type*} [Fintype ι] (B C : Matrix ι ι ℂ) :
    ntr (B - C) = ntr B - ntr C := by
  simp [ntr, Matrix.trace_sub, mul_sub]

private lemma Rg_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (B : Matrix ι ι ℂ) :
    ntr (c • B) = c * ntr B := by
  simp [ntr, Matrix.trace_smul]
  ring

private lemma Rg_ntr_add {ι : Type*} [Fintype ι] (B C : Matrix ι ι ℂ) :
    ntr (B + C) = ntr B + ntr C := by
  simp [ntr, Matrix.trace_add, mul_add]

private lemma Rg_ntr_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → Matrix ι ι ℂ) :
    ntr (∑ b ∈ s, f b) = ∑ b ∈ s, ntr (f b) := by
  simp [ntr, Matrix.trace_sum, Finset.mul_sum]

/-- `Λ M(z') = 1 + (z' + m(z')) M(z')` and `M(z')` commutes with `Λ`, for `Λ = lam D N A`,
`z' ∉ ℝ`. -/
private lemma Rg_resolvent (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (hz : z.im ≠ 0) :
    lam D N A * MExt (lam D N A) z = 1 + (z + mExt (lam D N A) z) • MExt (lam D N A) z ∧
      MExt (lam D N A) z * lam D N A = lam D N A * MExt (lam D N A) z := by
  obtain ⟨-, h⟩ := def_M_scalar D hD N hN A z hz
  set Λ := lam D N A
  set M := MExt Λ z
  set m := mExt Λ z
  rw [sub_mul, smul_mul_assoc, one_mul] at h
  have h' : (m + z) • M + 1 = Λ * M := by
    have h0 := h
    rw [sub_add_eq_add_sub, sub_eq_zero] at h0
    exact h0
  have h1 : Λ * M = 1 + (z + m) • M := by rw [← h', add_comm m z, add_comm]
  refine ⟨h1, ?_⟩
  have h2 : (Λ - (z + m) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M = 1 := by
    rw [sub_mul, smul_mul_assoc, one_mul, h1]; simp
  have h3 := mul_eq_one_comm.mp h2
  rw [mul_sub, mul_smul_comm, mul_one] at h3
  rw [h1]
  calc M * Λ = (M * Λ - (z + m) • M) + (z + m) • M := by abel
    _ = 1 + (z + m) • M := by rw [h3]

private lemma Rg_colsum {D : ℕ} [NeZero D] (F : Fin D → Fin D → ℂ)
    (hF : ∀ a b a' b' : Fin D, b - a = b' - a' → F a b = F a' b') (a a' : Fin D) :
    ∑ b, F b a = ∑ b, F b a' := by
  refine Fintype.sum_equiv (Equiv.addRight (a' - a)) _ _ fun b => ?_
  exact hF b a (b + (a' - a)) a' (by abel)

/-- The column sums of `M̂(z₁, z₂)` do not depend on the block: `⟨M(z₁) M(z₂) E_a⟩` is the same
for all `a`, by the translation invariance of Lemma A.1 [lemma_usual_properties_of_m_and_mu]
(vi). -/
private lemma Rg_prodEa (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0) (a a' : Fin D) :
    ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₂ * Ea D N a) =
      ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₂ * Ea D N a') := by
  have : NeZero D := ⟨by omega⟩
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have key : ∀ a : Fin D, ntr (MExt (lam D N A) z₁ * MExt (lam D N A) z₂ * Ea D N a) =
      (D : ℂ)⁻¹ * ∑ b : Fin D, Mhat (lam D N A) z₁ z₂ b a := by
    intro a
    have e : MExt (lam D N A) z₁ * MExt (lam D N A) z₂ * Ea D N a =
        ∑ b : Fin D, MExt (lam D N A) z₁ * Ea D N b * MExt (lam D N A) z₂ * Ea D N a := by
      have e2 : ∑ b : Fin D, MExt (lam D N A) z₁ * Ea D N b * MExt (lam D N A) z₂ * Ea D N a =
          (MExt (lam D N A) z₁ * (∑ b : Fin D, Ea D N b) * MExt (lam D N A) z₂) *
            Ea D N a := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      rw [e2, Rg_Ea_sum, mul_one]
    rw [e, Rg_ntr_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    change _ = (D : ℂ)⁻¹ * ((D : ℂ) * _)
    rw [← mul_assoc, inv_mul_cancel₀ hD0, one_mul]
  have hs := Rg_colsum (fun a b => Mhat (lam D N A) z₁ z₂ a b)
    (fun a b a' b' hab => Mhat_translation D hD N A z₁ z₂ h₁ h₂ a b a' b' hab) a a'
  rw [key a, key a', hs]

end RgLamAlg

/-! ### The averages `⟨(Λ - Δ) M E_a⟩` and the position of the quantile -/

section RgT1

private lemma Rg_trace1 (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (z' : ℂ) (hz' : z'.im ≠ 0) (Δ : ℝ) (a : Fin D) :
    ntr ((lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * MExt (lam D N A) z' *
        Ea D N a) =
      (D : ℂ)⁻¹ * (1 + (z' + mExt (lam D N A) z' - (Δ : ℂ)) * mExt (lam D N A) z') := by
  obtain ⟨hres, -⟩ := Rg_resolvent D hD N hN A z' hz'
  obtain ⟨hsc, -⟩ := def_M_scalar D hD N hN A z' hz'
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have h1 : ntr (MExt (lam D N A) z' * Ea D N a) = (D : ℂ)⁻¹ * mExt (lam D N A) z' := by
    rw [← hsc a]; field_simp
  have e : (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * MExt (lam D N A) z' *
      Ea D N a = Ea D N a + (z' + mExt (lam D N A) z' - (Δ : ℂ)) •
        (MExt (lam D N A) z' * Ea D N a) := by
    rw [sub_mul, smul_mul_assoc, one_mul, hres, sub_mul, add_mul, one_mul, smul_mul_assoc]
    rw [sub_smul]
    simp only [smul_mul_assoc]
    abel
  rw [e, Rg_ntr_add, Rg_ntr_smul, h1, Rg_ntr_Ea D N (by omega) hN a]
  ring

/-- `E⁻ ≤ γ_k ≤ E⁺` for the quantile, from (2.21) [eq:kappa_gamma_k]. -/
private lemma Rg_gamma_in (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
        Eminus (lam D N A) ≤ quant (rho (lam D N A)) (D * N) k ∧
          quant (rho (lam D N A)) (D * N) k ≤ Eplus (lam D N A) := by
  obtain ⟨c, C, hc, hC, N₁, h⟩ := kappa_gamma_k D hD δA hδA
  refine ⟨N₁, fun N hN A hA k hk hkN => ?_⟩
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; omega
    · exact h0
  have hk' : 1 ≤ D * N + 1 - k := by omega
  have hk'' : D * N + 1 - k ≤ D * N := by omega
  have hkk : D * N + 1 - (D * N + 1 - k) = k := by omega
  obtain ⟨a1, -, -, -⟩ := h N hN A hA k hk hkN
  obtain ⟨-, -, b3, -⟩ := h N hN A hA (D * N + 1 - k) hk' hk''
  rw [hkk] at b3
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have p1 : 0 ≤ c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by positivity
  have p2 : 0 ≤ c * (((D * N + 1 - k : ℕ) : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
    positivity
  constructor <;> linarith

end RgT1

section RgT1b

private lemma Rg_norm_zero_one : opNorm (0 : Matrix (Fin 1) (Fin 1) ℂ) ≤ 1 / 10 := by
  unfold opNorm
  simp

/-- `‖m_sc(z)‖ ≤ 1` and `m_sc(z)² + z m_sc(z) + 1 = 0`, `Im m_sc(z) > 0`, for `Im z > 0`. -/
private lemma Rg_msc_facts {z : ℂ} (hz : 0 < z.im) :
    ‖msc z‖ ≤ 1 ∧ msc z ^ 2 + z * msc z + 1 = 0 ∧ 0 < (msc z).im := by
  obtain ⟨h1, h2⟩ := (rho_zero (ι := Fin 1)).2.2.2.2.2.2 z hz
  refine ⟨?_, h1, h2⟩
  have h3 := (mSol_apriori (0 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.isHermitian_zero
    Rg_norm_zero_one z hz).2.1
  have h4 : msc z = mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z := (Rg_ext_eq _ hz).1
  rw [h4]; exact h3.le

end RgT1b

section RgBig

/-- The case `η ≤ 1` of the lower bound `7σ ≤ Im m`: `σ² ≤ 16 D² N^{-4ε_A} η` with
`784 D² C_s² N^{-4ε_A} ≤ 1` and `Im m ≥ C_s⁻¹ √(κ + η)` give `7σ ≤ Im m`. -/
private lemma Rg_big_small {σ η Cs mi κ Dd Nm : ℝ} (hCs : 0 < Cs) (hη : 0 < η)
    (hκ : 0 ≤ κ) (hσ2 : σ ^ 2 ≤ 16 * Dd ^ 2 * Nm * η)
    (hNp : Nm * (784 * Dd ^ 2 * Cs ^ 2) ≤ 1) (hlow : Cs⁻¹ * Real.sqrt (κ + η) ≤ mi) :
    2 * (7 / 2 * σ) ≤ mi := by
  have hsqrt : Real.sqrt η ≤ Real.sqrt (κ + η) := Real.sqrt_le_sqrt (by linarith)
  have h7 : (7 * Cs * σ) ^ 2 ≤ η := by
    calc (7 * Cs * σ) ^ 2 = 49 * Cs ^ 2 * σ ^ 2 := by ring
      _ ≤ 49 * Cs ^ 2 * (16 * Dd ^ 2 * Nm * η) := by gcongr
      _ = (Nm * (784 * Dd ^ 2 * Cs ^ 2)) * η := by ring
      _ ≤ 1 * η := by gcongr
      _ = η := one_mul _
  have h8 : 7 * Cs * σ ≤ Real.sqrt η := Real.le_sqrt_of_sq_le h7
  have h9 : 7 * σ ≤ Cs⁻¹ * Real.sqrt η := by
    rw [← mul_le_mul_iff_of_pos_left hCs]
    calc Cs * (7 * σ) = 7 * Cs * σ := by ring
      _ ≤ _ := h8
      _ = _ := by field_simp
  calc 2 * (7 / 2 * σ) = 7 * σ := by ring
    _ ≤ Cs⁻¹ * Real.sqrt η := h9
    _ ≤ Cs⁻¹ * Real.sqrt (κ + η) := by gcongr
    _ ≤ mi := hlow

/-- The case `η > 1` of the lower bound `7σ ≤ Im m`, from `Im m ‖w‖² ≥ (81/100) η`,
`‖w‖ ≤ (41/10) η`, `σ η ≤ 4D/N` and `N ≥ 1000 D`. -/
private lemma Rg_big_large {σ η mi Dd Nn w : ℝ} (hη : 1 < η) (hDd : 0 < Dd)
    (hNn : 1000 * Dd ≤ Nn) (hση : σ * η ≤ 4 * Dd / Nn) (hw : w ≤ 41 / 10 * η) (hw0 : 0 ≤ w)
    (hc3 : 81 / 100 * η ≤ mi * w ^ 2) (hmi : 0 ≤ mi) :
    2 * (7 / 2 * σ) ≤ mi := by
  have hη0 : 0 < η := by linarith
  have hw2 : w ^ 2 ≤ (41 / 10 * η) ^ 2 := pow_le_pow_left₀ hw0 hw 2
  have h1 : 81 / 100 * η ≤ mi * (41 / 10 * η) ^ 2 := hc3.trans (by gcongr)
  have h2 : 81 / 100 ≤ 1681 / 100 * (mi * η) := by
    have : 81 / 100 * η ≤ (1681 / 100 * (mi * η)) * η := by nlinarith
    exact le_of_mul_le_mul_right this hη0
  have hNn0 : 0 < Nn := by linarith
  have h4 : 4 * Dd / Nn ≤ 4 / 1000 := by
    rw [div_le_div_iff₀ hNn0 (by norm_num)]; linarith
  have h5 : 2 * (7 / 2 * σ) * η ≤ mi * η := by nlinarith
  exact le_of_mul_le_mul_right h5 hη0

end RgBig

section RgT1c

/-- The bound (5.5) [regular_estimate_localized_eigenvector] from
`‖1 + (z₁ + m - Δ) m‖ ≤ (7/2) Im m σ` and `‖p‖ ≤ 1`: all four sign choices. -/
private lemma Rg_T1_trace (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (hN1 : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) {z₁ : ℂ} (hz1ne : z₁.im ≠ 0) (Δ : ℝ) {m : ℂ} {σ : ℝ}
    (hext1 : mExt (lam D N A) z₁ = m) (hmσ : 0 ≤ m.im * σ)
    (c2 : ‖1 + (z₁ + m - (Δ : ℂ)) * m‖ ≤ 7 / 2 * (m.im * σ)) {p : ℂ} (hpc : ‖p‖ ≤ 1)
    (a : Fin D) (s₀ s₁ : Bool) :
    ‖ntr (((if s₀ then star p else p) •
          (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ))) *
        (if s₁ then (MExt (lam D N A) z₁)ᴴ else MExt (lam D N A) z₁) * Ea D N a)‖ ≤
      100 * (m.im * σ) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  have hΛ : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hc : ‖(if s₀ then star p else p)‖ ≤ 1 := by
    split_ifs
    · rw [norm_star]; exact hpc
    · exact hpc
  have hD2 : ‖((D : ℂ))⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, Complex.norm_natCast]
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hF : ‖ntr ((lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
      (if s₁ then (MExt (lam D N A) z₁)ᴴ else MExt (lam D N A) z₁) * Ea D N a)‖ ≤
      7 / 4 * (m.im * σ) := by
    by_cases hs₁ : s₁ = true
    · simp only [hs₁, ↓reduceIte]
      have hcj := mExt_conj (lam D N A) hΛ z₁ hz1ne
      rw [← hcj.2, Rg_trace1 D hD N hN1 A (star z₁) (by simpa using hz1ne) Δ a, hcj.1, hext1,
        norm_mul]
      have e : 1 + (star z₁ + star m - (Δ : ℂ)) * star m =
          star (1 + (z₁ + m - (Δ : ℂ)) * m) := by
        simp
      rw [e, norm_star]
      calc ‖((D : ℂ))⁻¹‖ * ‖1 + (z₁ + m - (Δ : ℂ)) * m‖ ≤ (1 / 2) * (7 / 2 * (m.im * σ)) := by
            gcongr
        _ = 7 / 4 * (m.im * σ) := by ring
    · simp only [hs₁, Bool.false_eq_true, ↓reduceIte]
      rw [Rg_trace1 D hD N hN1 A z₁ hz1ne Δ a, hext1, norm_mul]
      calc ‖((D : ℂ))⁻¹‖ * ‖1 + (z₁ + m - (Δ : ℂ)) * m‖ ≤ (1 / 2) * (7 / 2 * (m.im * σ)) := by
            gcongr
        _ = 7 / 4 * (m.im * σ) := by ring
  rw [smul_mul_assoc, smul_mul_assoc, Rg_ntr_smul, norm_mul]
  calc _ ≤ 1 * (7 / 4 * (m.im * σ)) := by gcongr
    _ ≤ 100 * (m.im * σ) := by linarith

end RgT1c

/-! ### The block average of `𝔐₀ Λ̂ 𝔐₁ E_a` -/

section RgT2

/-- `⟨M₀ (Λ - Δ) M₁ E_a⟩` does not depend on the block `a`, for `M_i = M_t(z_i)`, `z_i ∉ ℝ`. -/
private lemma Rg_Ea_indep (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (hN1 : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) (z₀ z₁ : ℂ) (h₀ : z₀.im ≠ 0) (h₁ : z₁.im ≠ 0)
    (Δ : ℝ) (a a' : Fin D) :
    ntr (MExt ((t : ℂ) • lam D N A) z₀ *
        (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
        MExt ((t : ℂ) • lam D N A) z₁ * Ea D N a) =
      ntr (MExt ((t : ℂ) • lam D N A) z₀ *
        (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
        MExt ((t : ℂ) • lam D N A) z₁ * Ea D N a') := by
  have hD0 : 0 < D := by omega
  rw [Rg_lam_smul D N A t]
  set A' := (t : ℂ) • A with hA'
  by_cases ht : t = 0
  · -- `t = 0`: the resolvents are scalar
    have hl0 : lam D N A' = 0 := by
      rw [hA', ht, ← Rg_lam_smul]; simp
    have hsc : ∀ z : ℂ, z.im ≠ 0 → ∃ c : ℂ,
        MExt (lam D N A') z = c • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by
      intro z hz
      obtain ⟨hres, -⟩ := Rg_resolvent D hD N hN1 A' z hz
      set w := z + mExt (lam D N A') z
      set M := MExt (lam D N A') z
      have hz0 : lam D N A' * M = 0 := by rw [hl0, zero_mul]
      rw [hz0] at hres
      have hw0 : w ≠ 0 := by
        intro h
        rw [h, zero_smul, add_zero] at hres
        have := congrFun (congrFun hres ((⟨0, hD0⟩ : Fin D), (⟨0, hN1⟩ : Fin N)))
          ((⟨0, hD0⟩ : Fin D), (⟨0, hN1⟩ : Fin N))
        simp at this
      refine ⟨-w⁻¹, ?_⟩
      have h2 : w • M = -1 := by
        have := hres
        rw [eq_comm, add_comm, add_eq_zero_iff_eq_neg] at this
        exact this
      calc M = w⁻¹ • (w • M) := by rw [smul_smul, inv_mul_cancel₀ hw0, one_smul]
        _ = w⁻¹ • (-1 : Matrix (Idx D N) (Idx D N) ℂ) := by rw [h2]
        _ = (-w⁻¹) • (1 : Matrix (Idx D N) (Idx D N) ℂ) := by rw [smul_neg, neg_smul]
    obtain ⟨c₀, hc₀⟩ := hsc z₀ h₀
    obtain ⟨c₁, hc₁⟩ := hsc z₁ h₁
    have e : ∀ b : Fin D, ntr (MExt (lam D N A') z₀ *
        (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * MExt (lam D N A') z₁ *
        Ea D N b) = c₀ * c₁ * (0 - Δ * (D : ℂ)⁻¹) := by
      intro b
      rw [hc₀, hc₁]
      have : (c₀ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
          (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
          (c₁ • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * Ea D N b =
          (c₀ * c₁) • ((lam D N A * Ea D N b) - (Δ : ℂ) • Ea D N b) := by
        simp only [smul_mul_assoc, one_mul, mul_smul_comm, mul_one, sub_mul, smul_sub, smul_smul]
        rw [show c₁ * c₀ = c₀ * c₁ by ring, show c₁ * (c₀ * (Δ : ℂ)) = c₀ * c₁ * Δ by ring]
      rw [this, Rg_ntr_smul, Rg_ntr_sub, Rg_ntr_smul, Rg_ntr_lam_Ea D N hD A,
        Rg_ntr_Ea D N hD0 hN1]
    rw [e a, e a']
  · -- `t ≠ 0`
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have hlam : lam D N A = (t : ℂ)⁻¹ • lam D N A' := by
      rw [hA', ← Rg_lam_smul, smul_smul, inv_mul_cancel₀ htc, one_smul]
    obtain ⟨hres0, hcomm0⟩ := Rg_resolvent D hD N hN1 A' z₀ h₀
    set M₀ := MExt (lam D N A') z₀ with hM₀
    set M₁ := MExt (lam D N A') z₁ with hM₁
    set w₀ := z₀ + mExt (lam D N A') z₀ with hw₀
    have hX : M₀ * (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M₁ =
        (t : ℂ)⁻¹ • M₁ + ((t : ℂ)⁻¹ * w₀ - (Δ : ℂ)) • (M₀ * M₁) := by
      rw [hlam]
      have h1 : M₀ * ((t : ℂ)⁻¹ • lam D N A' - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) * M₁ =
          (t : ℂ)⁻¹ • (M₀ * lam D N A' * M₁) - (Δ : ℂ) • (M₀ * M₁) := by
        simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one]
      rw [h1, hcomm0, hres0, add_mul, one_mul, smul_mul_assoc, smul_add, smul_smul, sub_smul]
      abel
    obtain ⟨hsc, -⟩ := def_M_scalar D hD N hN1 A' z₁ h₁
    have e : ∀ b : Fin D, ntr (M₀ * (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
        M₁ * Ea D N b) = (t : ℂ)⁻¹ * ((D : ℂ)⁻¹ * mExt (lam D N A') z₁) +
          ((t : ℂ)⁻¹ * w₀ - (Δ : ℂ)) * ntr (M₀ * M₁ * Ea D N b) := by
      intro b
      rw [hX, add_mul, smul_mul_assoc, smul_mul_assoc, Rg_ntr_add, Rg_ntr_smul, Rg_ntr_smul]
      congr 2
      have hD0c : (D : ℂ) ≠ 0 := by exact_mod_cast hD0.ne'
      rw [← hsc b, ← mul_assoc, inv_mul_cancel₀ hD0c, one_mul]
    rw [e a, e a', Rg_prodEa D hD N A' z₀ z₁ h₀ h₁ a a']


/-- `⟨M₀ (Λ - Δ) M₁ E_a⟩ = D⁻¹ ⟨M₀ (Λ - Δ) M₁⟩`. -/
private lemma Rg_Ea_reduce (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (hN1 : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) (z₀ z₁ : ℂ) (h₀ : z₀.im ≠ 0) (h₁ : z₁.im ≠ 0)
    (Δ : ℝ) (a : Fin D) :
    ntr (MExt ((t : ℂ) • lam D N A) z₀ *
        (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
        MExt ((t : ℂ) • lam D N A) z₁ * Ea D N a) =
      (D : ℂ)⁻¹ * ntr (MExt ((t : ℂ) • lam D N A) z₀ *
        (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
        MExt ((t : ℂ) • lam D N A) z₁) := by
  set X := MExt ((t : ℂ) • lam D N A) z₀ *
    (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
    MExt ((t : ℂ) • lam D N A) z₁ with hX
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hs : ∑ b : Fin D, ntr (X * Ea D N b) = ntr X := by
    rw [← Rg_ntr_sum, ← Finset.mul_sum, Rg_Ea_sum, mul_one]
  have hc : ∑ b : Fin D, ntr (X * Ea D N b) = (D : ℂ) * ntr (X * Ea D N a) := by
    rw [Finset.sum_congr rfl fun b _ => Rg_Ea_indep D hD N hN1 A t z₀ z₁ h₀ h₁ Δ b a,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← hs, hc, ← mul_assoc, inv_mul_cancel₀ hD0, one_mul]

end RgT2

section RgT2b

/-- (5.21) [shift_bound_localized_eigenvalue] and (5.22) [regular_estimate_localized_eigenvalue]
at any `z` in the upper half plane, for `|t| ≤ 1` and `‖Λ‖ ≤ 1/10`. -/
private lemma Rg_T2_main (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (hN1 : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) (hℓ : opNorm (lam D N A) ≤ 1 / 10) {t : ℝ} (ht : |t| ≤ 1)
    {z : ℂ} (hz : 0 < z.im) {Δ : ℝ}
    (hΔ : Δ = (ntr (MExt ((t : ℂ) • lam D N A) z * lam D N A *
        (MExt ((t : ℂ) • lam D N A) z)ᴴ) /
      ntr (MExt ((t : ℂ) • lam D N A) z * (MExt ((t : ℂ) • lam D N A) z)ᴴ)).re) :
    |Δ| ≤ 100 * avgSq (lam D N A) ∧ ∀ (a : Fin D) (s₀ s₁ : Bool),
      ‖ntr ((if s₀ then (MExt ((t : ℂ) • lam D N A) z)ᴴ else MExt ((t : ℂ) • lam D N A) z) *
          (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
          (if s₁ then (MExt ((t : ℂ) • lam D N A) z)ᴴ else MExt ((t : ℂ) • lam D N A) z) *
          Ea D N a)‖ ≤
        100 * ((mExt ((t : ℂ) • lam D N A) z).im * avgSq (lam D N A)) := by
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  have hΛ : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hn0 : ntr (lam D N A) = 0 := Rg_ntr_lam D N hD A
  have hΛt : ((t : ℂ) • lam D N A).IsHermitian := Rg_herm_smul hΛ t
  obtain ⟨hext1, hext2⟩ := Rg_ext_eq ((t : ℂ) • lam D N A) hz
  rw [hext2] at hΔ
  obtain ⟨c1, c2, c3, c4, c5⟩ := Rg_core2 hΛ hn0 hℓ ht hz (M := MSol ((t : ℂ) • lam D N A) z) rfl
    hΔ
  obtain ⟨hpos, -⟩ := mSol_spec ((t : ℂ) • lam D N A) hΛt z hz
  obtain ⟨-, -, -, -, -, hσ0⟩ := Rg_core1 hΛ hn0 hℓ hz
  refine ⟨by linarith, ?_⟩
  intro a s₀ s₁
  have hzs : (star z).im ≠ 0 := by simpa using hz.ne'
  have hcj := mExt_conj ((t : ℂ) • lam D N A) hΛt z hz.ne'
  rw [hext1]
  have hmσ : 0 ≤ (mSol ((t : ℂ) • lam D N A) z).im * avgSq (lam D N A) :=
    mul_nonneg hpos.le hσ0
  have hD2 : ‖((D : ℂ))⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, Complex.norm_natCast]
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  cases s₀ <;> cases s₁
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Rg_Ea_reduce D hD N hN1 A t z z hz.ne' hz.ne' Δ a, hext2, norm_mul]
    calc ‖((D : ℂ))⁻¹‖ * ‖ntr (MSol ((t : ℂ) • lam D N A) z *
          (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
          MSol ((t : ℂ) • lam D N A) z)‖ ≤
        (1 / 2) * (28 * ((mSol ((t : ℂ) • lam D N A) z).im * avgSq (lam D N A))) := by
          gcongr
      _ ≤ _ := by linarith
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← hcj.2, Rg_Ea_reduce D hD N hN1 A t z (star z) hz.ne' hzs Δ a, hcj.2, hext2, c2]
    simp only [mul_zero, norm_zero]
    linarith
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← hcj.2, Rg_Ea_reduce D hD N hN1 A t (star z) z hzs hz.ne' Δ a, hcj.2, hext2, c3]
    simp only [mul_zero, norm_zero]
    linarith
  · simp only [↓reduceIte]
    rw [← hcj.2, Rg_Ea_reduce D hD N hN1 A t (star z) (star z) hzs hzs Δ a, hcj.2, hext2,
      norm_mul]
    calc ‖((D : ℂ))⁻¹‖ * ‖ntr ((MSol ((t : ℂ) • lam D N A) z)ᴴ *
          (lam D N A - (Δ : ℂ) • (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
          (MSol ((t : ℂ) • lam D N A) z)ᴴ)‖ ≤
        (1 / 2) * (28 * ((mSol ((t : ℂ) • lam D N A) z).im * avgSq (lam D N A))) := by
          gcongr
      _ ≤ _ := by linarith

end RgT2b

/-- Lemma 5.1 [lem_regular_estimate_localized_eigenvector] with (5.3) [sim_m_sc_and_m]: under
(2.8) [eq:condA2] and `ε ∈ (0, 2ε_A)`, with `z₀ = z₁ - Δ_ev` and `Λ̃ = Λ - Δ_ev`:
`Im m_sc(z₀) ∼ Im m(z₁)`, (5.4) [shift_bound_localized_eigenvector] `Δ_ev = O(⟨Λ²⟩)`, and
(5.5) [regular_estimate_localized_eigenvector] `⟨𝔐₀ Λ̃ 𝔐₁ E_a⟩ = Im m(z₁) · O(⟨Λ²⟩)` for
`𝔐₀ ∈ {m_sc(z₀), m_sc(z₀)^*}`, `𝔐₁ ∈ {M(z₁), M(z₁)^*}`. -/
theorem regular_estimate_localized_eigenvector (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ)
    (hδA : 0 < δA) (hεA : 0 < εA) (hε : 0 < ε) (hε' : ε < 2 * εA) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
        C⁻¹ * (msc (zOne (lam D N A) k ε -
            (shiftEv (lam D N A) (zOne (lam D N A) k ε) : ℂ))).im ≤
            (mExt (lam D N A) (zOne (lam D N A) k ε)).im ∧
          (mExt (lam D N A) (zOne (lam D N A) k ε)).im ≤
            C * (msc (zOne (lam D N A) k ε -
              (shiftEv (lam D N A) (zOne (lam D N A) k ε) : ℂ))).im ∧
          |shiftEv (lam D N A) (zOne (lam D N A) k ε)| ≤ C * avgSq (lam D N A) ∧
          ∀ (a : Fin D) (s₀ s₁ : Bool),
            ‖ntr (((if s₀ then star (msc (zOne (lam D N A) k ε -
                    (shiftEv (lam D N A) (zOne (lam D N A) k ε) : ℂ)))
                  else msc (zOne (lam D N A) k ε -
                    (shiftEv (lam D N A) (zOne (lam D N A) k ε) : ℂ))) •
                (lam D N A - (shiftEv (lam D N A) (zOne (lam D N A) k ε) : ℂ) •
                  (1 : Matrix (Idx D N) (Idx D N) ℂ))) *
              (if s₁ then (MExt (lam D N A) (zOne (lam D N A) k ε))ᴴ
                else MExt (lam D N A) (zOne (lam D N A) k ε)) * Ea D N a)‖ ≤
            C * ((mExt (lam D N A) (zOne (lam D N A) k ε)).im * avgSq (lam D N A)) := by
  obtain ⟨Ce, hCe, hedge⟩ := edge_close_to_edge_sc
  obtain ⟨Cs, hCs, hsq⟩ := square_root_density (1 / 4) (by norm_num)
  obtain ⟨N₁, hN₁⟩ := Rg_gamma_in D hD δA hδA
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  set T : ℝ := 20 * (D : ℝ) ^ 2 * (1 + Ce) with hT
  have hT0 : 0 < T := by positivity
  have hK0 : (0 : ℝ) < 784 * (D : ℝ) ^ 2 * Cs ^ 2 := by positivity
  refine ⟨100, by norm_num, max (max (max N₁ 1) ⌈T ^ (1 / δA)⌉₊)
    (max ⌈(784 * (D : ℝ) ^ 2 * Cs ^ 2) ^ (1 / (4 * εA))⌉₊ ⌈1000 * (D : ℝ)⌉₊), ?_⟩
  intro N hN A hA k hk hkN hhs
  have hN' : max (max N₁ 1) ⌈T ^ (1 / δA)⌉₊ ≤ N := (le_max_left _ _).trans hN
  have hN'' : max ⌈(784 * (D : ℝ) ^ 2 * Cs ^ 2) ^ (1 / (4 * εA))⌉₊ ⌈1000 * (D : ℝ)⌉₊ ≤ N :=
    (le_max_right _ _).trans hN
  have hNN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN')
  have hN1 : 1 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN')
  have hNT : T ≤ (N : ℝ) ^ δA := Rg_pow_ge hT0 hδA ((le_max_right _ _).trans hN')
  have hN4 : 784 * (D : ℝ) ^ 2 * Cs ^ 2 ≤ (N : ℝ) ^ (4 * εA) :=
    Rg_pow_ge hK0 (by positivity) ((le_max_left _ _).trans hN'')
  have hN1000 : 1000 * (D : ℝ) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN'')
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, hN1⟩)⟩
  have hNd : (N : ℝ) ^ (-δA) ≤ T⁻¹ := by
    rw [Real.rpow_neg hNpos.le]
    exact inv_anti₀ hT0 hNT
  have hℓ : opNorm (lam D N A) ≤ 1 / (10 * (1 + Ce)) := by
    refine (Rg_opNorm_lam D N hN1 A).trans ?_
    calc 2 * (D : ℝ) ^ 2 * opNorm A ≤ 2 * (D : ℝ) ^ 2 * T⁻¹ := by
          gcongr; exact hA.trans hNd
      _ = 1 / (10 * (1 + Ce)) := by simp only [hT]; field_simp; ring
  have hℓ10 : opNorm (lam D N A) ≤ 1 / 10 := by
    refine hℓ.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hΛ : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hn0 : ntr (lam D N A) = 0 := Rg_ntr_lam D N hD A
  -- the position of the quantile
  have hE := hedge (Idx D N) (lam D N A) hΛ hℓ10
  have hCℓ : Ce * opNorm (lam D N A) ≤ 1 / 10 := by
    calc Ce * opNorm (lam D N A) ≤ Ce * (1 / (10 * (1 + Ce))) := by gcongr
      _ ≤ 1 / 10 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨hγ1, hγ2⟩ := hN₁ N hNN₁ A hA k hk hkN
  have hγ : |quant (rho (lam D N A)) (D * N) k| ≤ 21 / 10 := by
    have a1 := abs_nonneg (2 - Eplus (lam D N A))
    have a2 := abs_nonneg (2 + Eminus (lam D N A))
    have h2 := (abs_le.1 (show |2 - Eplus (lam D N A)| ≤ 1 / 10 by linarith)).1
    have h3 := (abs_le.1 (show |2 + Eminus (lam D N A)| ≤ 1 / 10 by linarith)).1
    rw [abs_le]; constructor <;> linarith
  -- the point `z₁`
  have hrk := Rg_rk D N k hk hkN
  have hηpos : 0 < etaK D N k ε := by
    unfold etaK
    have : (0 : ℝ) < rk D N k := by linarith [hrk.1]
    positivity
  have hz1im : (zOne (lam D N A) k ε).im = etaK D N k ε := by simp [zOne]
  have hz1re : (zOne (lam D N A) k ε).re = quant (rho (lam D N A)) (D * N) k := by simp [zOne]
  have hz1 : 0 < (zOne (lam D N A) k ε).im := by rw [hz1im]; exact hηpos
  have hz1norm : ‖zOne (lam D N A) k ε‖ ≤ 21 / 10 + etaK D N k ε := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hz1im, hz1re, abs_of_pos hηpos]; linarith
  have hz1ne : (zOne (lam D N A) k ε).im ≠ 0 := hz1.ne'
  obtain ⟨hext1, hext2⟩ := Rg_ext_eq (lam D N A) hz1
  obtain ⟨c1, c2, c3, ham, hm1, hσ0⟩ := Rg_core1 hΛ hn0 hℓ10 hz1
  have hΔdef : shiftEv (lam D N A) (zOne (lam D N A) k ε) =
      (zOne (lam D N A) k ε + mSol (lam D N A) (zOne (lam D N A) k ε) +
        (mSol (lam D N A) (zOne (lam D N A) k ε))⁻¹).re := by
    unfold shiftEv; rw [hext1]
  rw [← hΔdef] at c1 c2
  rw [hext1, hext2]
  generalize hz₁def : zOne (lam D N A) k ε = z₁ at *
  generalize hΔ : shiftEv (lam D N A) z₁ = Δ at *
  generalize hmdef : mSol (lam D N A) z₁ = m at *
  set σ := avgSq (lam D N A) with hσdef
  have hz₀ : 0 < (z₁ - (Δ : ℂ)).im := by simpa using hz1
  obtain ⟨hpc, hroot, hp⟩ := Rg_msc_facts hz₀
  -- the lower bound `7σ ≤ Im m`
  have hbig : 2 * (7 / 2 * σ) ≤ m.im := by
    have hσle : σ ≤ 4 * D * hsNorm A ^ 2 / N := Rg_avgSq_lam D N hD hN1 A
    have hh0 : 0 ≤ hsNorm A := Real.sqrt_nonneg _
    obtain ⟨se1, se2⟩ := Rg_sig_eta hn1 hrk.1 hDpos hεA hε hε' hh0 hσ0 hσle hhs
      (η := etaK D N k ε) rfl
    by_cases hη1 : etaK D N k ε ≤ 1
    · have hz4 : ‖z₁‖ ≤ (1 / 4 : ℝ)⁻¹ := by norm_num; linarith
      have hre : z₁.re ∈ Set.Icc (Eminus (lam D N A)) (Eplus (lam D N A)) := by
        rw [hz1re]; exact ⟨hγ1, hγ2⟩
      have hlow := ((hsq (Idx D N) (lam D N A) hΛ hℓ10).2 z₁ hz4 hz1).1 hre |>.1
      rw [hmdef, hz1im] at hlow
      have hNp : (N : ℝ) ^ (-(4 * εA)) * (784 * (D : ℝ) ^ 2 * Cs ^ 2) ≤ 1 := by
        rw [Real.rpow_neg hNpos.le]
        calc ((N : ℝ) ^ (4 * εA))⁻¹ * (784 * (D : ℝ) ^ 2 * Cs ^ 2) ≤
            ((N : ℝ) ^ (4 * εA))⁻¹ * (N : ℝ) ^ (4 * εA) := by gcongr
          _ = 1 := inv_mul_cancel₀ (by positivity)
      exact Rg_big_small hCs hηpos (le_min (abs_nonneg _) (abs_nonneg _)) se2 hNp hlow
    · have hw : ‖z₁ + m‖ ≤ 41 / 10 * etaK D N k ε := by
        refine (norm_add_le _ _).trans ?_
        linarith
      rw [hz1im] at c3
      exact Rg_big_large (lt_of_not_ge hη1) hDpos hN1000 se1 hw (norm_nonneg _) c3 ham.le
  have hcmp := Rg_compare (K := 7 / 2) ham hp hz₀ hroot
    (by convert c2 using 2; ring) hbig
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [hcmp.2, ham]
  · linarith [hcmp.1, ham]
  · linarith
  · intro a s₀ s₁
    have hT := Rg_T1_trace D hD N hN1 A hz1ne Δ hext1 (mul_nonneg ham.le hσ0) c2 hpc a s₀ s₁
    rw [hext2] at hT
    exact hT

/-- Lemma 5.3 [lem_regular_estimate_localized_eigenvalue]: under (2.8) [eq:condA2] and
`ε ∈ (0, 2ε_A)`, uniformly in `t ∈ [0, 1]`, (5.21) [shift_bound_localized_eigenvalue]
`Δ(t) = O(⟨Λ²⟩)` and (5.22) [regular_estimate_localized_eigenvalue]
`⟨𝔐₀ Λ̂_t 𝔐₁ E_a⟩ = O(Im m_t(z_t) ⟨Λ²⟩)` for `𝔐₀, 𝔐₁ ∈ {M_t(z_t), M_t(z_t)^*}`,
`Λ̂_t = Λ - Δ(t)`. -/
theorem regular_estimate_localized_eigenvalue (D : ℕ) (hD : 2 ≤ D) (δA εA ε : ℝ)
    (hδA : 0 < δA) (hεA : 0 < εA) (hε : 0 < ε) (hε' : ε < 2 * εA) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
      hsNorm A ≤ (N : ℝ) ^ ((1 / 3 : ℝ) - εA) * rk D N k ^ (-(1 / 3 : ℝ)) →
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        |shiftT (lam D N A) k ε t| ≤ C * avgSq (lam D N A) ∧
        ∀ (a : Fin D) (s₀ s₁ : Bool),
          ‖ntr ((if s₀ then (MExt ((t : ℂ) • lam D N A) (zOne ((t : ℂ) • lam D N A) k ε))ᴴ
                else MExt ((t : ℂ) • lam D N A) (zOne ((t : ℂ) • lam D N A) k ε)) *
              (lam D N A - (shiftT (lam D N A) k ε t : ℂ) •
                (1 : Matrix (Idx D N) (Idx D N) ℂ)) *
              (if s₁ then (MExt ((t : ℂ) • lam D N A) (zOne ((t : ℂ) • lam D N A) k ε))ᴴ
                else MExt ((t : ℂ) • lam D N A) (zOne ((t : ℂ) • lam D N A) k ε)) *
              Ea D N a)‖ ≤
            C * ((mExt ((t : ℂ) • lam D N A) (zOne ((t : ℂ) • lam D N A) k ε)).im *
              avgSq (lam D N A)) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  refine ⟨100, by norm_num, max 1 ⌈(20 * (D : ℝ) ^ 2) ^ (1 / δA)⌉₊, ?_⟩
  intro N hN A hA k hk hkN hhs t ht
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNT : 20 * (D : ℝ) ^ 2 ≤ (N : ℝ) ^ δA :=
    Rg_pow_ge (by positivity) hδA ((le_max_right _ _).trans hN)
  have hNd : (N : ℝ) ^ (-δA) ≤ (20 * (D : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hNpos.le]
    exact inv_anti₀ (by positivity) hNT
  have hℓ : opNorm (lam D N A) ≤ 1 / 10 := by
    refine (Rg_opNorm_lam D N hN1 A).trans ?_
    calc 2 * (D : ℝ) ^ 2 * opNorm A ≤ 2 * (D : ℝ) ^ 2 * (20 * (D : ℝ) ^ 2)⁻¹ := by
          gcongr; exact hA.trans hNd
      _ = 1 / 10 := by field_simp; ring
  have hrk := Rg_rk D N k hk hkN
  have hηpos : 0 < etaK D N k ε := by
    unfold etaK
    have : (0 : ℝ) < rk D N k := by linarith [hrk.1]
    positivity
  have hz : 0 < (zOne ((t : ℂ) • lam D N A) k ε).im := by simpa [zOne] using hηpos
  have ht1 : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨h1, h2⟩ := Rg_T2_main D hD N hN1 A hℓ ht1 hz (Δ := shiftT (lam D N A) k ε t) rfl
  exact ⟨h1, h2⟩

end RBMTransitionEdge

end

