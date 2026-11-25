module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Model.Deterministic
public import RBMTransitionEdge.Det.Core
public import RBMTransitionEdge.Det.Edge
public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.Det.Taylor
public import RBMTransitionEdge.Det.MhatSpec

@[expose] public section

/-!
# Edge stability of the self-consistent equations

The sharp upper bound `|1 - ⟨M²⟩| ≤ C √(κ + η)` on the mean mode of the stability operator of
(2.16) [self_m], and the lower bound on the other modes `1 - λ̂_l` of `1 - M̂(z, z)` of (3.1)
[def_ML], used by the stability of the vector equation in the proof of Lemma 2.9 [lem_loc].
-/

open MeasureTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### Operator norm, normalized trace and the Fourier vectors -/

section ES_Tools

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma ES_op_eq (A : Matrix ι ι ℂ) : opNorm A = ‖A‖ := rfl

private lemma ES_op_nonneg (A : Matrix ι ι ℂ) : 0 ≤ opNorm A := norm_nonneg _

private lemma ES_op_mul (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [ES_op_eq] using norm_mul_le A B

private lemma ES_op_conj (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  simpa only [ES_op_eq] using Matrix.l2_opNorm_conjTranspose A

/-- The squared Euclidean norm of the column `j` of `A` is at most `‖A‖²`. -/
private lemma ES_col_le (A : Matrix ι ι ℂ) (j : ι) : ∑ i, ‖A i j‖ ^ 2 ≤ opNorm A ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [h1, mul_one] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [EuclideanSpace.norm_sq_eq] at h2
  have h3 : ∀ i, ((EuclideanSpace.equiv ι ℂ).symm
      (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)).ofLp i = A i j := fun i => by simp
  simp only [h3] at h2
  simpa [ES_op_eq] using h2

private lemma ES_entry_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
  have h := (Finset.single_le_sum (f := fun i => ‖A i j‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ i)).trans (ES_col_le A j)
  exact (sq_le_sq₀ (norm_nonneg _) (ES_op_nonneg _)).1 h

private lemma ES_ntr_le [Nonempty ι] (A : Matrix ι ι ℂ) : ‖ntr A‖ ≤ opNorm A := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, opNorm A := Finset.sum_le_sum fun i _ => ES_entry_le A i i
    _ = _ := by simp

omit [DecidableEq ι] in
private lemma ES_ntr_smul (c : ℂ) (A : Matrix ι ι ℂ) : ntr (c • A) = c * ntr A := by
  simp [ntr, Matrix.trace_smul]; ring

omit [DecidableEq ι] in
private lemma ES_ntr_sub (A B : Matrix ι ι ℂ) : ntr (A - B) = ntr A - ntr B := by
  simp [ntr, Matrix.trace_sub]; ring

omit [DecidableEq ι] in
private lemma ES_ntr_neg (A : Matrix ι ι ℂ) : ntr (-A) = -ntr A := by
  simp [ntr, Matrix.trace_neg]

/-- `‖A‖²_HS ≤ n ‖A‖²` for an `n × n` matrix. -/
private lemma ES_hs_le (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    hsNorm A ^ 2 ≤ N * opNorm A ^ 2 := by
  unfold hsNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity),
    Finset.sum_comm]
  calc ∑ j : Fin N, ∑ i : Fin N, ‖A i j‖ ^ 2 ≤ ∑ _j : Fin N, opNorm A ^ 2 :=
        Finset.sum_le_sum fun j _ => ES_col_le A j
    _ = N * opNorm A ^ 2 := by simp

end ES_Tools

section ES_Fourier

/-- Each entry of the Fourier vector `u_l` has modulus `D^{-1/2}`. -/
private lemma ES_u_norm (D : ℕ) (l a : Fin D) : ‖fourierVec D l a‖ = (Real.sqrt D)⁻¹ := by
  unfold fourierVec
  rw [norm_mul, Complex.norm_exp]
  have : (2 * Real.pi * Complex.I * (((l : ℕ) * (a : ℕ) : ℕ) : ℂ) / D).re = 0 := by
    simp [Complex.div_re]
  rw [this, Real.exp_zero, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- `Σ_a |u_l(a)|² = 1`. -/
private lemma ES_u_sq (D : ℕ) (hD : D ≠ 0) (l : Fin D) :
    ∑ a : Fin D, star (fourierVec D l a) * fourierVec D l a = 1 := by
  have e : ∀ a : Fin D, star (fourierVec D l a) * fourierVec D l a = ((D : ℝ)⁻¹ : ℝ) := by
    intro a
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ES_u_norm,
      inv_pow, Real.sq_sqrt (Nat.cast_nonneg D)]
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  push_cast
  field_simp

/-- `Σ_a u_l(a) = 0` for `l ≠ 0`, the Fourier vectors of (A.25) [eq_lambdak]. -/
private lemma ES_u_sum (D : ℕ) (hD : D ≠ 0) (l : Fin D) (hl : (l : ℕ) ≠ 0) :
    ∑ a : Fin D, fourierVec D l a = 0 := by
  have hζ := Complex.isPrimitiveRoot_exp D hD
  set ζ := Complex.exp (2 * Real.pi * Complex.I / D)
  have e : ∀ a : Fin D, fourierVec D l a = ((Real.sqrt D : ℂ))⁻¹ * (ζ ^ (l : ℕ)) ^ (a : ℕ) := by
    intro a
    unfold fourierVec
    rw [← pow_mul, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  simp only [e, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun a => (ζ ^ (l : ℕ)) ^ a)]
  set r := ζ ^ (l : ℕ)
  have hrD : r ^ D = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hr1 : r ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hl l.isLt
  have hg := geom_sum_mul r D
  rw [hrD, sub_self] at hg
  rw [(mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hr1), mul_zero]

end ES_Fourier

/-- `|1 - ⟨M²⟩| ≤ C √(κ + η)` for `|z| ≤ τ⁻¹`, `η > 0`, `‖Λ‖ ≤ 1/10`, `⟨Λ⟩ = 0`: the sharp upper
bound on the mean mode of the stability operator of (2.16) [self_m]; `C` depends on `τ` only. -/
theorem one_minus_M2_edge (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → ntr Λ = 0 →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
        ‖1 - ntr (MSol Λ z ^ 2)‖ ≤ C * Real.sqrt (kappa Λ z.re + z.im) := by
  obtain ⟨C₁, hC₁, hsrd⟩ := square_root_density τ hτ
  set r : ℝ := Real.sqrt τ⁻¹ with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  refine ⟨5 * C₁ + 4 * r, by positivity, ?_⟩
  intro ι _ _ _ Λ hΛ hℓ _ z hzn hz
  obtain ⟨-, hS⟩ := hsrd ι Λ hΛ hℓ
  have hS' := hS z hzn hz
  obtain ⟨hy, -, -⟩ := mSol_spec Λ hΛ z hz
  obtain ⟨-, -, hMn⟩ := mSol_apriori Λ hΛ hℓ z hz
  obtain ⟨h1, h2⟩ := equation_z_im_m Λ hΛ z hz
  set M := MSol Λ z
  set y := (mSol Λ z).im
  set η := z.im
  set κ := kappa Λ z.re
  have hκ : 0 ≤ κ := le_min (abs_nonneg _) (abs_nonneg _)
  set q := Real.sqrt (κ + η)
  have hs : 0 < κ + η := by positivity
  have hq : 0 < q := Real.sqrt_pos.2 hs
  have hqq : q * q = κ + η := Real.mul_self_sqrt hs.le
  have hηn : η ≤ τ⁻¹ := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hzn)
  have hηr : η ≤ r * q := by
    have e1 : η = Real.sqrt η * Real.sqrt η := (Real.mul_self_sqrt hz.le).symm
    have e2 : Real.sqrt η ≤ r := Real.sqrt_le_sqrt hηn
    have e3 : Real.sqrt η ≤ q := Real.sqrt_le_sqrt (by linarith)
    rw [e1]
    exact mul_le_mul e2 e3 (Real.sqrt_nonneg _) hr0
  -- the two regimes of (A.1) [square_root_density]
  have hηy : η / y ≤ C₁ * q ∧ y ≤ C₁ * q := by
    by_cases hin : z.re ∈ Set.Icc (Eminus Λ) (Eplus Λ)
    · obtain ⟨a1, a2⟩ := hS'.1 hin
      refine ⟨?_, a2⟩
      rw [div_le_iff₀ hy]
      have : q * q ≤ C₁ * q * y := by
        have := mul_le_mul_of_nonneg_left a1 (mul_nonneg hC₁.le hq.le)
        calc q * q = C₁ * q * (C₁⁻¹ * q) := by field_simp
          _ ≤ C₁ * q * y := this
      linarith
    · obtain ⟨a1, a2⟩ := hS'.2 hin
      have hηq : η / q ≤ q := by rw [div_le_iff₀ hq]; linarith
      refine ⟨?_, a2.trans (mul_le_mul_of_nonneg_left hηq hC₁.le)⟩
      rw [div_le_iff₀ hy]
      have := mul_le_mul_of_nonneg_left a1 (mul_nonneg hC₁.le hq.le)
      calc η = C₁ * q * (C₁⁻¹ * (η / q)) := by field_simp
        _ ≤ C₁ * q * y := this
  obtain ⟨hηy1, hy1⟩ := hηy
  have hd1 : 1 - y / (y + η) = η / (y + η) := by field_simp; ring
  have hd2 : η / (y + η) ≤ η / y := div_le_div_of_nonneg_left hz.le hy (by linarith)
  -- `|⟨M M^*⟩ - ⟨M²⟩| ≤ 4 (η + Im m)`, from `M - M^* = 2i (η + Im m) M M^*` of (A.3)
  -- [equation_z_im_m]
  have hdiff : ‖ntr (M * Mᴴ) - ntr (M * M)‖ ≤ 4 * (η + y) := by
    have e : M * Mᴴ - M * M = -((2 * Complex.I * ((η + y : ℝ) : ℂ)) • (M * (M * Mᴴ))) := by
      rw [← Matrix.mul_smul, ← h2]; noncomm_ring
    rw [← ES_ntr_sub, e, ES_ntr_neg, norm_neg, ES_ntr_smul, norm_mul]
    have hc : ‖2 * Complex.I * ((η + y : ℝ) : ℂ)‖ = 2 * (η + y) := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      norm_num
    rw [hc]
    have hM54 : opNorm M ≤ 5 / 4 := by
      refine hMn.le.trans ?_
      rw [inv_le_comm₀ (by linarith [ES_op_nonneg Λ]) (by norm_num)]
      linarith [ES_op_nonneg Λ]
    have hn : ‖ntr (M * (M * Mᴴ))‖ ≤ 2 := by
      refine (ES_ntr_le _).trans ?_
      refine (ES_op_mul _ _).trans ?_
      have := ES_op_mul M Mᴴ
      rw [ES_op_conj] at this
      have h0 := ES_op_nonneg M
      nlinarith
    nlinarith
  have hup : ‖1 - ntr (M * M)‖ ≤ η / y + 4 * (η + y) := by
    have : 1 - ntr (M * M) = ((1 - y / (y + η) : ℝ) : ℂ) + (ntr (M * Mᴴ) - ntr (M * M)) := by
      rw [h1]; push_cast; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, hd1, abs_of_nonneg (by positivity)]
    linarith
  rw [sq]
  calc ‖1 - ntr (M * M)‖ ≤ η / y + 4 * (η + y) := hup
    _ ≤ C₁ * q + 4 * (r * q + C₁ * q) := by linarith
    _ = (5 * C₁ + 4 * r) * q := by ring

/-- For `l ≠ 0` the eigenvalues `λ̂_l` of `M̂(z₁, z₁)` of (3.1) [def_ML], `z₁ ∈ {z, z̄}`, satisfy
`|1 - λ̂_l| ≥ c (√(κ + η) + ‖A‖²_HS / N)` for `|z| ≤ τ⁻¹`, `η > 0`; `c` and `N₀` depend on
`D, δ_A, τ` only. -/
theorem one_minus_Mhat_nonzero (D : ℕ) (hD : 2 ≤ D) (δA τ : ℝ) (hδA : 0 < δA) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im → ∀ z₁ : ℂ, z₁ = z ∨ z₁ = star z →
      ∀ l : Fin D, (l : ℕ) ≠ 0 →
        c * (Real.sqrt (kappa (lam D N A) z.re + z.im) + hsNorm A ^ 2 / N) ≤
          ‖1 - circEig (Mhat (lam D N A) z₁ z₁) l‖ := by
  have : NeZero D := ⟨by omega⟩
  have hD0 : D ≠ 0 := by omega
  obtain ⟨Cs, hCs, Ns, hst⟩ := one_minus_Mhat_stability D hD δA τ hδA hτ
  obtain ⟨CF, hCF, NF, hfl⟩ := flat_M D hD δA τ hδA hτ
  set c₂ : ℝ := min (1 / 2) (1 / (2 * D * CF)) with hc₂
  have hc₂0 : 0 < c₂ := lt_min (by norm_num) (by positivity)
  refine ⟨min Cs⁻¹ c₂ / 2, by positivity, max (max Ns NF) 1,
    fun N hN A hA z hzn hz z₁ h₁ l hl => ?_⟩
  have hNs : Ns ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNF : NF ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hdet, hinv⟩ := hst N hNs A hA z hzn hz z₁ h₁
  obtain ⟨-, hK⟩ := hfl N hNF A hA z hzn hz z₁ z₁ h₁ h₁
  have hz₁ : z₁.im ≠ 0 := by
    rcases h₁ with rfl | rfl
    · exact hz.ne'
    · simp [hz.ne']
  have hev := Mhat_eigvec D hD N A z₁ z₁ hz₁ hz₁ l
  set B := Mhat (lam D N A) z₁ z₁ with hB
  set μ := circEig B l
  set u := fourierVec D l with hu
  set R := (1 - B)⁻¹ with hRdef
  set q := Real.sqrt (kappa (lam D N A) z.re + z.im)
  set X := hsNorm A ^ 2 / N
  have hκ : 0 ≤ kappa (lam D N A) z.re := le_min (abs_nonneg _) (abs_nonneg _)
  have hq : 0 < q := Real.sqrt_pos.2 (by linarith)
  have hX0 : 0 ≤ X := by positivity
  -- `‖A‖²_HS / N ≤ ‖A‖² ≤ 1`
  have hX1 : X ≤ 1 := by
    have hop1 : opNorm A ≤ 1 := hA.trans
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith))
    have h0 : 0 ≤ opNorm A := norm_nonneg _
    have h2 : opNorm A ^ 2 ≤ 1 := by nlinarith
    have := ES_hs_le N A
    rw [div_le_one hNpos]
    nlinarith
  -- `(1 - B)⁻¹ u = (1 - λ̂_l)⁻¹ u`
  have hR : R * (1 - B) = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
  have hRu : (1 - μ) • (R *ᵥ u) = u := by
    have e : (1 - B) *ᵥ u = (1 - μ) • u := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hev, sub_smul, one_smul]
    rw [← Matrix.mulVec_smul, ← e, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  have hu0 : u ≠ 0 := by
    intro h
    have := ES_u_sq D hD0 l
    simp [← hu, h] at this
  have hμ1 : 1 - μ ≠ 0 := by
    intro h
    rw [h, zero_smul] at hRu
    exact hu0 hRu.symm
  -- the part `√(κ + η)`: `1 ≤ |1 - λ̂_l| ‖(1 - B)⁻¹‖`
  have hsq : Cs⁻¹ * q ≤ ‖1 - μ‖ := by
    set x : EuclideanSpace ℂ (Fin D) := WithLp.toLp 2 u
    have hx : ‖x‖ = 1 := by
      have h := EuclideanSpace.norm_sq_eq x
      have e : ∑ i, ‖x i‖ ^ 2 = 1 := by
        have := ES_u_sq D hD0 l
        have e2 : ∀ i, ‖x i‖ ^ 2 = (((Real.sqrt D)⁻¹) ^ 2 : ℝ) := fun i => by
          change ‖u i‖ ^ 2 = _
          rw [hu, ES_u_norm]
        simp only [e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, inv_pow,
          Real.sq_sqrt (Nat.cast_nonneg D)]
        have : (D : ℝ) ≠ 0 := by exact_mod_cast hD0
        field_simp
      rw [e] at h
      have h0 := norm_nonneg x
      nlinarith
    have hle := (Matrix.toEuclideanCLM (𝕜 := ℂ) R).le_opNorm x
    rw [hx, mul_one] at hle
    have hxe : x = (1 - μ) • (Matrix.toEuclideanCLM (𝕜 := ℂ) R x) := by
      rw [Matrix.toEuclideanCLM_toLp, ← WithLp.toLp_smul, hRu]
    have h1 : 1 ≤ ‖1 - μ‖ * opNorm R := by
      have := congrArg norm hxe
      rw [hx, norm_smul] at this
      rw [this]
      exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    have h2 : 1 ≤ ‖1 - μ‖ * (Cs / q) := h1.trans (mul_le_mul_of_nonneg_left hinv (norm_nonneg _))
    rw [inv_mul_le_iff₀ hCs]
    rw [mul_div_assoc', le_div_iff₀ hq] at h2
    linarith
  -- the part `‖A‖²_HS / N`: `λ̂_l / (1 - λ̂_l)` is a combination of the differences
  -- `K_{ab} - K_{00}`, bounded by (A.11) [flat_M]
  have hKu : Kmat (lam D N A) z₁ z₁ *ᵥ u = (μ * (1 - μ)⁻¹) • u := by
    have e : Kmat (lam D N A) z₁ z₁ = R * B := rfl
    have hRu' : R *ᵥ u = (1 - μ)⁻¹ • u := by
      calc R *ᵥ u = (1 - μ)⁻¹ • ((1 - μ) • (R *ᵥ u)) := by
            rw [smul_smul, inv_mul_cancel₀ hμ1, one_smul]
        _ = (1 - μ)⁻¹ • u := by rw [hRu]
    rw [e, ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul, hRu', smul_smul]
  set K := Kmat (lam D N A) z₁ z₁
  set κl := μ * (1 - μ)⁻¹
  have hκl : κl = ∑ a : Fin D, ∑ b : Fin D, star (u a) * (K a b - K 0 0) * u b := by
    have e1 : ∑ a : Fin D, star (u a) * (K *ᵥ u) a = κl := by
      rw [hKu]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (∑ a : Fin D, star (u a) * (κl * u a)) = κl * ∑ a : Fin D, star (u a) * u a by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring, ES_u_sq D hD0 l,
        mul_one]
    have e2 : ∑ a : Fin D, ∑ b : Fin D, star (u a) * K 0 0 * u b = 0 := by
      have : ∑ a : Fin D, ∑ b : Fin D, star (u a) * K 0 0 * u b =
          (∑ a : Fin D, star (u a)) * K 0 0 * ∑ b : Fin D, u b := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
      rw [this, ES_u_sum D hD0 l hl, mul_zero]
    have e3 : ∑ a : Fin D, star (u a) * (K *ᵥ u) a =
        ∑ a : Fin D, ∑ b : Fin D, star (u a) * K a b * u b := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    have e4 : ∑ a : Fin D, ∑ b : Fin D, star (u a) * (K a b - K 0 0) * u b =
        (∑ a : Fin D, ∑ b : Fin D, star (u a) * K a b * u b) -
          ∑ a : Fin D, ∑ b : Fin D, star (u a) * K 0 0 * u b := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e4, e2, sub_zero, ← e3, e1]
  have hKbd : X * ‖κl‖ ≤ D * CF := by
    have hb : ‖κl‖ ≤ ∑ a : Fin D, ∑ b : Fin D, (D : ℝ)⁻¹ * ‖K a b - K 0 0‖ := by
      rw [hκl]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => le_of_eq ?_)
      rw [norm_mul, norm_mul, norm_star, hu, ES_u_norm, ES_u_norm]
      have e : (Real.sqrt D)⁻¹ * (Real.sqrt D)⁻¹ = (D : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      rw [← e]
      ring
    have hc : ∀ a b : Fin D, X * ‖K a b - K 0 0‖ ≤ CF := by
      intro a b
      have := hK a b 0 0
      calc X * ‖K a b - K 0 0‖ = hsNorm A ^ 2 * ‖K a b - K 0 0‖ / N := by
            simp only [X]; ring
        _ ≤ CF * N / N := div_le_div_of_nonneg_right this hNpos.le
        _ = CF := by field_simp
    have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD0
    calc X * ‖κl‖ ≤ X * ∑ a : Fin D, ∑ b : Fin D, (D : ℝ)⁻¹ * ‖K a b - K 0 0‖ :=
          mul_le_mul_of_nonneg_left hb hX0
      _ = ∑ a : Fin D, ∑ b : Fin D, (D : ℝ)⁻¹ * (X * ‖K a b - K 0 0‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
      _ ≤ ∑ _a : Fin D, ∑ _b : Fin D, (D : ℝ)⁻¹ * CF :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
            mul_le_mul_of_nonneg_left (hc a b) (by positivity)
      _ = D * CF := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hpart : c₂ * X ≤ ‖1 - μ‖ := by
    have hμe : μ = κl * (1 - μ) := by
      simp only [κl]; rw [mul_assoc, inv_mul_cancel₀ hμ1, mul_one]
    by_cases hbig : 1 / 2 ≤ ‖μ‖
    · have h3 : X * ‖μ‖ ≤ D * CF * ‖1 - μ‖ := by
        have hn : ‖μ‖ = ‖κl‖ * ‖1 - μ‖ := by rw [← norm_mul, ← hμe]
        rw [hn, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hKbd (norm_nonneg _)
      have h4 : c₂ ≤ 1 / (2 * D * CF) := min_le_right _ _
      have h5 : X / 2 ≤ D * CF * ‖1 - μ‖ := by nlinarith
      calc c₂ * X ≤ 1 / (2 * D * CF) * X := mul_le_mul_of_nonneg_right h4 hX0
        _ = (X / 2) / (D * CF) := by field_simp
        _ ≤ ‖1 - μ‖ := by rw [div_le_iff₀ (by positivity)]; linarith
    · push Not at hbig
      have h3 : 1 - ‖μ‖ ≤ ‖1 - μ‖ := by
        have := norm_sub_norm_le (1 : ℂ) μ
        rwa [norm_one] at this
      have h4 : c₂ ≤ 1 / 2 := min_le_left _ _
      nlinarith
  have hm1 : min Cs⁻¹ c₂ ≤ Cs⁻¹ := min_le_left _ _
  have hm2 : min Cs⁻¹ c₂ ≤ c₂ := min_le_right _ _
  nlinarith

end RBMTransitionEdge

end
