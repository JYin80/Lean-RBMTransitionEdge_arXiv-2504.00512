module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Model.Deterministic
public import RBMTransitionEdge.Det.Core
public import RBMTransitionEdge.Det.Edge
public import RBMTransitionEdge.Det.Block

@[expose] public section

/-!
# Comparison with the semicircle law and the expansions (A.5)–(A.7), (A.12)

(A.5) [eq:msc] in its two forms, the replacement (A.6) [estimate_replace_M_by_m], the expansion (A.7)
[add_one_more_Lambda] and the two-sided bounds (A.12) [de_ir_0].
-/

open MeasureTheory Matrix Filter Topology

noncomputable section
open Classical

namespace RBMTransitionEdge

section Tools

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma Tay_opNorm_eq (A : Matrix ι ι ℂ) : opNorm A = ‖A‖ := rfl

private lemma Tay_op_mul (A B : Matrix ι ι ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [Tay_opNorm_eq] using norm_mul_le A B

private lemma Tay_op_add (A B : Matrix ι ι ℂ) : opNorm (A + B) ≤ opNorm A + opNorm B := by
  simpa only [Tay_opNorm_eq] using norm_add_le A B

private lemma Tay_op_smul (c : ℂ) (A : Matrix ι ι ℂ) : opNorm (c • A) = ‖c‖ * opNorm A := by
  simpa only [Tay_opNorm_eq] using norm_smul c A

private lemma Tay_op_nonneg (A : Matrix ι ι ℂ) : 0 ≤ opNorm A := norm_nonneg _

private lemma Tay_op_one : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

private lemma Tay_op_conj (A : Matrix ι ι ℂ) : opNorm Aᴴ = opNorm A := by
  simpa only [Tay_opNorm_eq] using Matrix.l2_opNorm_conjTranspose A

private lemma Tay_op_diag (d : ι → ℂ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ j, ‖d j‖ ≤ B) :
    opNorm (diagonal d) ≤ B := by
  rw [Tay_opNorm_eq, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hB).2 h

private lemma Tay_entry_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ opNorm A := by
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

private lemma Tay_ntr_le [Nonempty ι] (A : Matrix ι ι ℂ) : ‖ntr A‖ ≤ opNorm A := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, opNorm A := Finset.sum_le_sum fun i _ => Tay_entry_le A i i
    _ = _ := by simp


/-- `∑ᵢⱼ |Aᵢⱼ|²`. -/
private def Tay_S (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq ι] in
private lemma Tay_S_nonneg (A : Matrix ι ι ℂ) : 0 ≤ Tay_S A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

omit [DecidableEq ι] in
private lemma Tay_ntr_mul_le [Nonempty ι] (X Y : Matrix ι ι ℂ) :
    ‖ntr (X * Y)‖ ≤ (Fintype.card ι : ℝ)⁻¹ * (Real.sqrt (Tay_S X) * Real.sqrt (Tay_S Y)) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : ‖(X * Y).trace‖ ≤ ∑ p : ι × ι, ‖X p.1 p.2‖ * ‖Y p.2 p.1‖ := by
    rw [Matrix.trace]
    calc ‖∑ i, (X * Y).diag i‖ ≤ ∑ i, ‖(X * Y).diag i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Y j i‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [Matrix.diag, Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
      _ = _ := by rw [Fintype.sum_prod_type]
  refine h1.trans ?_
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ι × ι))
    (fun p => ‖X p.1 p.2‖) (fun p => ‖Y p.2 p.1‖)
  have e1 : ∑ p : ι × ι, ‖X p.1 p.2‖ ^ 2 = Tay_S X := by
    rw [Fintype.sum_prod_type]; rfl
  have e2 : ∑ p : ι × ι, ‖Y p.2 p.1‖ ^ 2 = Tay_S Y := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rw [e1, e2] at h2
  exact h2

private lemma Tay_S_mul_le (U B : Matrix ι ι ℂ) : Tay_S (U * B) ≤ opNorm U ^ 2 * Tay_S B := by
  unfold Tay_S
  rw [Finset.sum_comm (f := fun i j => ‖(U * B) i j‖ ^ 2),
    Finset.sum_comm (f := fun i j => ‖B i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := Matrix.l2_opNorm_mulVec U ((EuclideanSpace.equiv ι ℂ).symm (fun i => B i j))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  have e : ∀ i, ((EuclideanSpace.equiv ι ℂ).symm (U *ᵥ ((EuclideanSpace.equiv ι ℂ).symm
      (fun i => B i j)).ofLp)).ofLp i = (U * B) i j := fun i => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [e] at h2
  simpa [Tay_opNorm_eq] using h2

omit [DecidableEq ι] in
/-- For Hermitian `Λ`, `∑ |Λᵢⱼ|² = |ι| ⟨Λ²⟩`. -/
private lemma Tay_S_herm [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    Tay_S Λ = Fintype.card ι * avgSq Λ := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ι)).ne'
  have e : (Λ * Λ).trace = ((Tay_S Λ : ℝ) : ℂ) := by
    rw [Matrix.trace, Tay_S]
    simp only [Matrix.diag, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h : Λ j i = star (Λ i j) := by rw [← hΛ.apply i j, star_star]
    rw [h, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  unfold avgSq ntr
  rw [e]
  have : ((Fintype.card ι : ℂ)⁻¹ * ((Tay_S Λ : ℝ) : ℂ)).re = (Fintype.card ι : ℝ)⁻¹ * Tay_S Λ := by
    rw [show ((Fintype.card ι : ℂ)⁻¹ : ℂ) = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [this]
  field_simp

omit [DecidableEq ι] in
private lemma Tay_avgSq_nonneg [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    0 ≤ avgSq Λ := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have := Tay_S_herm hΛ
  have h0 := Tay_S_nonneg Λ
  rw [this] at h0
  exact (mul_nonneg_iff_of_pos_left hn).1 h0

/-- The key bound: `|⟨U Λ V Λ⟩| ≤ ‖U‖ ‖V‖ ⟨Λ²⟩`. -/
private lemma Tay_BL [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (U V : Matrix ι ι ℂ) :
    ‖ntr (U * Λ * V * Λ)‖ ≤ opNorm U * opNorm V * avgSq Λ := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h1 := Tay_ntr_mul_le (U * Λ) (V * Λ)
  have e : U * Λ * (V * Λ) = U * Λ * V * Λ := by simp only [mul_assoc]
  rw [e] at h1
  refine h1.trans ?_
  have a1 := Tay_S_mul_le U Λ
  have a2 := Tay_S_mul_le V Λ
  have b1 : Real.sqrt (Tay_S (U * Λ)) ≤ opNorm U * Real.sqrt (Tay_S Λ) := by
    rw [← Real.sqrt_sq (Tay_op_nonneg U), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt a1
  have b2 : Real.sqrt (Tay_S (V * Λ)) ≤ opNorm V * Real.sqrt (Tay_S Λ) := by
    rw [← Real.sqrt_sq (Tay_op_nonneg V), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt a2
  have hS : Real.sqrt (Tay_S Λ) * Real.sqrt (Tay_S Λ) = Fintype.card ι * avgSq Λ := by
    rw [Real.mul_self_sqrt (Tay_S_nonneg Λ), Tay_S_herm hΛ]
  calc (Fintype.card ι : ℝ)⁻¹ * (Real.sqrt (Tay_S (U * Λ)) * Real.sqrt (Tay_S (V * Λ)))
      ≤ (Fintype.card ι : ℝ)⁻¹ * ((opNorm U * Real.sqrt (Tay_S Λ)) *
          (opNorm V * Real.sqrt (Tay_S Λ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul b1 b2 (Real.sqrt_nonneg _)
          (mul_nonneg (Tay_op_nonneg U) (Real.sqrt_nonneg _))
    _ = opNorm U * opNorm V * ((Fintype.card ι : ℝ)⁻¹ *
          (Real.sqrt (Tay_S Λ) * Real.sqrt (Tay_S Λ))) := by ring
    _ = _ := by rw [hS]; field_simp


private lemma Tay_ntr_one [Nonempty ι] : ntr (1 : Matrix ι ι ℂ) = 1 := by
  have : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := ι)).ne'
  simp [ntr, Matrix.trace_one, this]

omit [DecidableEq ι] in
private lemma Tay_ntr_smul (c : ℂ) (A : Matrix ι ι ℂ) : ntr (c • A) = c * ntr A := by
  simp [ntr, Matrix.trace_smul]; ring

omit [DecidableEq ι] in
private lemma Tay_ntr_add (A B : Matrix ι ι ℂ) : ntr (A + B) = ntr A + ntr B := by
  simp [ntr, Matrix.trace_add]; ring

omit [DecidableEq ι] in
private lemma Tay_ntr_sub (A B : Matrix ι ι ℂ) : ntr (A - B) = ntr A - ntr B := by
  simp [ntr, Matrix.trace_sub]; ring

/-- The basic a priori and algebraic facts about `m`, `w = z + m`, `M`. -/
private lemma Tay_facts [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ} (hz : 0 < z.im) :
    9 / 10 < ‖z + mSol Λ z‖ ∧ ‖mSol Λ z‖ < 1 ∧ 0 < (mSol Λ z).im ∧
      opNorm (MSol Λ z) ≤ 5 / 4 ∧
      (z + mSol Λ z) • MSol Λ z = MSol Λ z * Λ - 1 ∧
      Λ * MSol Λ z = MSol Λ z * Λ ∧
      MSol Λ z = (-(z + mSol Λ z)⁻¹) • (1 : Matrix ι ι ℂ) +
        (z + mSol Λ z)⁻¹ • (MSol Λ z * Λ) ∧
      mSol Λ z * (z + mSol Λ z) + 1 = ntr (MSol Λ z * Λ) := by
  obtain ⟨h1, h2, h3⟩ := mSol_apriori Λ hΛ hℓ z hz
  obtain ⟨hm, hmn, hinv⟩ := mSol_spec Λ hΛ z hz
  have hl0 := Tay_op_nonneg Λ
  have hw : 9 / 10 < ‖z + mSol Λ z‖ := by linarith
  have hw0 : z + mSol Λ z ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  have hM : opNorm (MSol Λ z) ≤ 5 / 4 := by
    refine h3.le.trans ?_
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hinv' := mul_eq_one_comm.mp hinv
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at hinv hinv'
  have hcomm : Λ * MSol Λ z = MSol Λ z * Λ := sub_left_inj.mp (hinv.trans hinv'.symm)
  have hrel : (z + mSol Λ z) • MSol Λ z = MSol Λ z * Λ - 1 := by
    rw [← hinv']; abel
  refine ⟨hw, h2, hm, hM, hrel, hcomm, ?_, ?_⟩
  · have : MSol Λ z = (z + mSol Λ z)⁻¹ • ((z + mSol Λ z) • MSol Λ z) := by
      rw [smul_smul, inv_mul_cancel₀ hw0, one_smul]
    conv_lhs => rw [this, hrel]
    rw [smul_sub, neg_smul]
    abel
  · have := congrArg ntr hrel
    rw [Tay_ntr_smul, Tay_ntr_sub, Tay_ntr_one, ← hmn] at this
    linear_combination this


/-- Root separation: the two roots of `t² + zt + 1` are `a` and `-z - a`, and `m` (with
`Im m > 0`, `|m| < 1`) is within `s` of the root `a` with `Im a > 0` whenever the residual
`m(z + m) + 1` is at most `s²` in modulus. -/
private lemma Tay_root_sep (z m a : ℂ) (hz : 0 < z.im) (hm : 0 < m.im) (hm1 : ‖m‖ < 1)
    (ha : 0 < a.im) (ha1 : ‖a‖ < 1) (hsq : a * (z + a) = -1) (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (hs : ‖m * (z + m) + 1‖ ≤ s ^ 2) : ‖m - a‖ ≤ 8 * s := by
  by_contra hcon
  push Not at hcon
  have hfac : (m - a) * (m - (-z - a)) = m * (z + m) + 1 := by
    linear_combination (-1 : ℂ) * hsq
  have hprod : ‖m - a‖ * ‖m - (-z - a)‖ ≤ s ^ 2 := by
    rw [← norm_mul, hfac]; exact hs
  have hP0 : 0 ≤ ‖m - (-z - a)‖ := norm_nonneg _
  have hpt : ‖m - (-z - a)‖ ≤ s / 8 := by
    by_contra hh
    push Not at hh
    nlinarith [mul_pos (sub_pos.2 hh) (show 0 < ‖m - a‖ by linarith)]
  set a' := -z - a with ha'
  have him := Complex.abs_im_le_norm (m - a')
  have him' : (m - a').im = m.im + z.im + a.im := by simp [ha']; ring
  rw [him'] at him
  have hy : a.im ≤ s / 8 := by
    have := le_abs_self (m.im + z.im + a.im)
    linarith
  have haa : a * a' = 1 := by rw [ha']; linear_combination (-1 : ℂ) * hsq
  have hρ : ‖a‖ * ‖a'‖ = 1 := by rw [← norm_mul, haa, norm_one]
  have hn' : ‖a'‖ < 1 + s / 8 := by
    have h2 : ‖a'‖ ≤ ‖m‖ + ‖m - a'‖ := by
      have := norm_sub_le m (m - a')
      rwa [sub_sub_cancel] at this
    linarith
  have hρ0 : 0 < ‖a‖ := norm_pos_iff.2 (fun h => by rw [h] at ha; simp at ha)
  have hρ1 : 1 < ‖a‖ * (1 + s / 8) := by nlinarith
  have hρ2 : 8 / 9 < ‖a‖ := by nlinarith
  have hid : ‖a ^ 2 - 1‖ ^ 2 = (1 - ‖a‖ ^ 2) ^ 2 + 4 * a.im ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp [sq]
    ring
  have hlt : 1 - ‖a‖ ^ 2 ≤ 2 * (s / 8) + (s / 8) ^ 2 := by nlinarith
  have hpos : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith
  have hb : ‖a ^ 2 - 1‖ ≤ 3 * (s / 8) := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    rw [hid]
    nlinarith [sq_nonneg a.im, ha]
  have hc : ‖a - a'‖ * ‖a‖ = ‖a ^ 2 - 1‖ := by
    rw [← norm_mul]
    congr 1
    linear_combination (-1 : ℂ) * haa
  have hd : ‖a - a'‖ ≤ 27 / 8 * (s / 8) := by nlinarith [norm_nonneg (a - a')]
  have he : ‖m - a‖ ≤ ‖m - a'‖ + ‖a - a'‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub m a' a
    rwa [norm_sub_rev a' a] at this
  nlinarith


private lemma Tay_op_zero_fin1 : opNorm (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  unfold opNorm; simp

/-- Facts about `m_sc`: `Im m_sc > 0`, `|m_sc| < 1`, `|z + m_sc| > 1`, `m_sc (z + m_sc) = -1`. -/
private lemma Tay_msc_facts {z : ℂ} (hz : 0 < z.im) :
    0 < (msc z).im ∧ ‖msc z‖ < 1 ∧ 1 < ‖z + msc z‖ ∧ msc z * (z + msc z) = -1 := by
  have hmsc : msc z = mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z := by
    simp only [msc, mExt, hz, ↓reduceIte]
  have h0 : opNorm (0 : Matrix (Fin 1) (Fin 1) ℂ) ≤ 1 / 10 := by
    rw [Tay_op_zero_fin1]; norm_num
  obtain ⟨h1, h2, -⟩ := mSol_apriori (0 : Matrix (Fin 1) (Fin 1) ℂ) isHermitian_zero h0 z hz
  obtain ⟨hm, hmn, hinv⟩ := mSol_spec (0 : Matrix (Fin 1) (Fin 1) ℂ) isHermitian_zero z hz
  rw [Tay_op_zero_fin1] at h1
  rw [hmsc]
  refine ⟨hm, h2, by linarith, ?_⟩
  have := congrFun (congrFun hinv 0) 0
  simp [Matrix.mul_apply, Matrix.one_apply] at this
  have hmn' : mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z =
      MSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z 0 0 := by
    rw [hmn]; simp [ntr, Matrix.trace]
  linear_combination (-1 : ℂ) * this + (z + mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z) * hmn'


/-- The core of (A.5): residual `‖⟨MΛ⟩‖ ≤ s²` gives `|m - m_sc| ≤ 8s` and
`‖M - m_sc‖ ≤ (25/18)‖Λ‖ + (10/9)·8s`. -/
private lemma Tay_eq_msc_core [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ} (hz : 0 < z.im) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hs : ‖ntr (MSol Λ z * Λ)‖ ≤ s ^ 2) :
    ‖mSol Λ z - msc z‖ ≤ 8 * s ∧
      opNorm (MSol Λ z - msc z • (1 : Matrix ι ι ℂ)) ≤ 25 / 18 * opNorm Λ + 10 / 9 * (8 * s) := by
  obtain ⟨hw, hm1, hm, hM, -, -, hdec, hres⟩ := Tay_facts hΛ hℓ hz
  obtain ⟨ha, ha1, hws, hsq⟩ := Tay_msc_facts hz
  have hsep : ‖mSol Λ z - msc z‖ ≤ 8 * s :=
    Tay_root_sep z _ _ hz hm hm1 ha ha1 hsq s hs0 hs1 (by rw [hres]; exact hs)
  refine ⟨hsep, ?_⟩
  have hw0 : z + mSol Λ z ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  have hws0 : z + msc z ≠ 0 := by
    intro h; rw [h, norm_zero] at hws; linarith
  have hms : msc z = -(z + msc z)⁻¹ := by
    field_simp
    linear_combination hsq
  have hid : MSol Λ z - msc z • (1 : Matrix ι ι ℂ) =
      ((z + msc z)⁻¹ - (z + mSol Λ z)⁻¹) • (1 : Matrix ι ι ℂ) +
        (z + mSol Λ z)⁻¹ • (MSol Λ z * Λ) := by
    conv_lhs => rw [hdec]
    conv_lhs => rw [hms]
    rw [sub_smul, neg_smul, neg_smul]
    abel
  have hc : ‖(z + msc z)⁻¹ - (z + mSol Λ z)⁻¹‖ ≤ 10 / 9 * ‖mSol Λ z - msc z‖ := by
    rw [inv_sub_inv hws0 hw0, norm_div, norm_mul]
    have : (z + mSol Λ z) - (z + msc z) = mSol Λ z - msc z := by ring
    rw [this, div_le_iff₀ (by positivity)]
    have h1 : 0 ≤ ‖mSol Λ z - msc z‖ := norm_nonneg _
    have hp : 9 / 10 ≤ ‖z + msc z‖ * ‖z + mSol Λ z‖ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hp h1]
  have hwi : ‖(z + mSol Λ z)⁻¹‖ ≤ 10 / 9 := by
    rw [norm_inv]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  rw [hid]
  have hl0 := Tay_op_nonneg Λ
  have hMΛ : opNorm (MSol Λ z * Λ) ≤ 5 / 4 * opNorm Λ :=
    (Tay_op_mul _ _).trans (mul_le_mul_of_nonneg_right hM hl0)
  calc opNorm (((z + msc z)⁻¹ - (z + mSol Λ z)⁻¹) • (1 : Matrix ι ι ℂ) +
        (z + mSol Λ z)⁻¹ • (MSol Λ z * Λ))
      ≤ opNorm (((z + msc z)⁻¹ - (z + mSol Λ z)⁻¹) • (1 : Matrix ι ι ℂ)) +
        opNorm ((z + mSol Λ z)⁻¹ • (MSol Λ z * Λ)) := Tay_op_add _ _
    _ ≤ 10 / 9 * (8 * s) + 10 / 9 * (5 / 4 * opNorm Λ) := by
      rw [Tay_op_smul, Tay_op_smul]
      have h1 : ‖(z + msc z)⁻¹ - (z + mSol Λ z)⁻¹‖ * opNorm (1 : Matrix ι ι ℂ) ≤
          10 / 9 * (8 * s) :=
        calc _ ≤ ‖(z + msc z)⁻¹ - (z + mSol Λ z)⁻¹‖ * 1 :=
              mul_le_mul_of_nonneg_left Tay_op_one (norm_nonneg _)
          _ ≤ 10 / 9 * ‖mSol Λ z - msc z‖ := by rw [mul_one]; exact hc
          _ ≤ _ := by gcongr
      have h2 : ‖(z + mSol Λ z)⁻¹‖ * opNorm (MSol Λ z * Λ) ≤ 10 / 9 * (5 / 4 * opNorm Λ) :=
        mul_le_mul hwi hMΛ (Tay_op_nonneg _) (by norm_num)
      linarith
    _ = _ := by ring


private lemma Tay_avgSq_le [Nonempty ι] (Λ : Matrix ι ι ℂ) : avgSq Λ ≤ opNorm Λ ^ 2 := by
  unfold avgSq
  calc (ntr (Λ * Λ)).re ≤ ‖ntr (Λ * Λ)‖ := Complex.re_le_norm _
    _ ≤ opNorm (Λ * Λ) := Tay_ntr_le _
    _ ≤ opNorm Λ * opNorm Λ := Tay_op_mul _ _
    _ = _ := by ring

/-- `|⟨MΛ⟩| ≤ (5/4)‖Λ‖`. -/
private lemma Tay_resid_le [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ} (hz : 0 < z.im) :
    ‖ntr (MSol Λ z * Λ)‖ ≤ 5 / 4 * opNorm Λ := by
  obtain ⟨-, -, -, hM, -⟩ := Tay_facts hΛ hℓ hz
  exact (Tay_ntr_le _).trans ((Tay_op_mul _ _).trans
    (mul_le_mul_of_nonneg_right hM (Tay_op_nonneg Λ)))

/-- If `⟨Λ⟩ = 0`, `|⟨MΛ⟩| ≤ (25/18) ⟨Λ²⟩`. -/
private lemma Tay_resid_traceless [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) (htr : ntr Λ = 0) {z : ℂ} (hz : 0 < z.im) :
    ‖ntr (MSol Λ z * Λ)‖ ≤ 25 / 18 * avgSq Λ := by
  obtain ⟨hw, -, -, hM, -, -, hdec, -⟩ := Tay_facts hΛ hℓ hz
  have hw0 : z + mSol Λ z ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  have e : ntr (MSol Λ z * Λ) = (z + mSol Λ z)⁻¹ * ntr (MSol Λ z * Λ * 1 * Λ) := by
    have h1 : MSol Λ z * Λ = (-(z + mSol Λ z)⁻¹) • Λ +
        (z + mSol Λ z)⁻¹ • (MSol Λ z * Λ * 1 * Λ) := by
      conv_lhs => rw [hdec]
      rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, mul_one]
    conv_lhs => rw [h1]
    rw [Tay_ntr_add, Tay_ntr_smul, Tay_ntr_smul, htr]
    ring
  rw [e, norm_mul]
  have hb := Tay_BL hΛ (MSol Λ z) (1 : Matrix ι ι ℂ)
  have hwi : ‖(z + mSol Λ z)⁻¹‖ ≤ 10 / 9 := by
    rw [norm_inv]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have ha0 := Tay_avgSq_nonneg hΛ
  have h1 : opNorm (MSol Λ z) * opNorm (1 : Matrix ι ι ℂ) * avgSq Λ ≤ 5 / 4 * avgSq Λ := by
    have := mul_le_mul hM (Tay_op_one (ι := ι)) (Tay_op_nonneg _) (by norm_num)
    nlinarith
  calc ‖(z + mSol Λ z)⁻¹‖ * ‖ntr (MSol Λ z * Λ * 1 * Λ)‖
      ≤ 10 / 9 * (5 / 4 * avgSq Λ) :=
        mul_le_mul hwi (hb.trans h1) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

end Tools

section BlockTools

open scoped Matrix.Norms.L2Operator

variable {D N : ℕ}

private lemma Tay_Ea_mul (a b : Fin D) :
    Ea D N a * Ea D N b = if a = b then Ea D N a else 0 := by
  unfold Ea
  rw [Matrix.diagonal_mul_diagonal]
  by_cases h : a = b
  · subst h
    simp only [↓reduceIte]
    congr 1
    funext p
    by_cases hp : p.1 = a <;> simp [hp]
  · simp only [h, ↓reduceIte]
    ext p q
    by_cases hpq : p = q
    · subst hpq
      by_cases hp : p.1 = a
      · have : ¬ p.1 = b := fun e => h (hp.symm.trans e)
        simp [hp, h]
      · simp [hp]
    · simp [hpq]

private lemma Tay_op_Ea (a : Fin D) : opNorm (Ea D N a) ≤ 1 := by
  unfold Ea
  refine Tay_op_diag _ 1 (by norm_num) fun p => ?_
  by_cases hp : p.1 = a <;> simp [hp]

/-- Leading factors of the products in (A.7): `1` or a block projection `E_a`. -/
private def Tay_lead (D N : ℕ) (L : Matrix (Idx D N) (Idx D N) ℂ) : Prop :=
  L = 1 ∨ ∃ a : Fin D, L = Ea D N a

private lemma Tay_lead_op {L : Matrix (Idx D N) (Idx D N) ℂ} (h : Tay_lead D N L) :
    opNorm L ≤ 1 := by
  rcases h with rfl | ⟨a, rfl⟩
  · exact Tay_op_one
  · exact Tay_op_Ea a

private lemma Tay_lead_mul {L : Matrix (Idx D N) (Idx D N) ℂ} (h : Tay_lead D N L) (a : Fin D) :
    L * Ea D N a = 0 ∨ Tay_lead D N (L * Ea D N a) := by
  rcases h with rfl | ⟨a', rfl⟩
  · exact Or.inr (Or.inr ⟨a, by simp⟩)
  · rw [Tay_Ea_mul]
    by_cases h : a' = a
    · exact Or.inr (Or.inr ⟨a, by simp [h]⟩)
    · exact Or.inl (by simp [h])

/-- `⟨L Λ E_b⟩ = 0` for a leading factor `L` when every diagonal block of `Λ` is traceless. -/
private lemma Tay_lead_tr {Λ : Matrix (Idx D N) (Idx D N) ℂ}
    (htr : ∀ a : Fin D, ntr (Ea D N a * Λ) = 0) {L : Matrix (Idx D N) (Idx D N) ℂ}
    (h : Tay_lead D N L) (b : Fin D) : ntr (L * Λ * Ea D N b) = 0 := by
  have e : ntr (L * Λ * Ea D N b) = ntr (Ea D N b * L * Λ) := by
    unfold ntr
    rw [Matrix.trace_mul_cycle]
  rw [e]
  rcases h with rfl | ⟨a', rfl⟩
  · simpa using htr b
  · rw [Tay_Ea_mul]
    by_cases h : b = a'
    · subst h; simpa using htr b
    · simp [h, ntr]

end BlockTools

section A7

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `M` and `M^*` are each `c + Λ K` with `|c| ≤ 10/9` and `‖K‖ ≤ 25/18`. -/
private lemma Tay_g_decomp [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ} (hz : 0 < z.im) {g : Matrix ι ι ℂ}
    (hg : g = MSol Λ z ∨ g = (MSol Λ z)ᴴ) :
    opNorm g ≤ 5 / 4 ∧ ∃ (c : ℂ) (K : Matrix ι ι ℂ), ‖c‖ ≤ 10 / 9 ∧ opNorm K ≤ 25 / 18 ∧
      g = c • (1 : Matrix ι ι ℂ) + Λ * K := by
  obtain ⟨hw, -, -, hM, -, hcomm, hdec, -⟩ := Tay_facts hΛ hℓ hz
  have hwi : ‖(z + mSol Λ z)⁻¹‖ ≤ 10 / 9 := by
    rw [norm_inv]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  rcases hg with rfl | rfl
  · refine ⟨hM, -(z + mSol Λ z)⁻¹, (z + mSol Λ z)⁻¹ • MSol Λ z, by rwa [norm_neg], ?_, ?_⟩
    · rw [Tay_op_smul]
      calc ‖(z + mSol Λ z)⁻¹‖ * opNorm (MSol Λ z) ≤ 10 / 9 * (5 / 4) :=
            mul_le_mul hwi hM (Tay_op_nonneg _) (by norm_num)
        _ = _ := by norm_num
    · conv_lhs => rw [hdec]
      rw [mul_smul_comm, hcomm]
  · refine ⟨by rwa [Tay_op_conj], star (-(z + mSol Λ z)⁻¹),
      star ((z + mSol Λ z)⁻¹) • (MSol Λ z)ᴴ, by rwa [norm_star, norm_neg], ?_, ?_⟩
    · rw [Tay_op_smul, Tay_op_conj, norm_star]
      calc ‖(z + mSol Λ z)⁻¹‖ * opNorm (MSol Λ z) ≤ 10 / 9 * (5 / 4) :=
            mul_le_mul hwi hM (Tay_op_nonneg _) (by norm_num)
        _ = _ := by norm_num
    · conv_lhs => rw [hdec]
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hΛ.eq, mul_smul_comm]

/-- The norm of a product of factors each of norm at most `B`. -/
private lemma Tay_prod_norm (B : ℝ) (hB : 0 ≤ B) :
    ∀ (n : ℕ) (f : Fin n → Matrix ι ι ℂ), (∀ i, opNorm (f i) ≤ B) →
      opNorm (List.ofFn f).prod ≤ B ^ n := by
  intro n
  induction n with
  | zero =>
    intro f _
    simp only [List.ofFn_zero, List.prod_nil, pow_zero]
    exact Tay_op_one
  | succ n ih =>
    intro f hf
    rw [List.ofFn_succ, List.prod_cons, pow_succ']
    exact (Tay_op_mul _ _).trans (mul_le_mul (hf 0) (ih _ fun i => hf _) (Tay_op_nonneg _) hB)

end A7

section A7b

open scoped Matrix.Norms.L2Operator

/-- The induction behind (A.7): a leading factor `L ∈ {1, E_{a'}}`, then `n` factors
`M^{s_i} E_{a_i}`, then `Λ E_b`. -/
private lemma Tay_A7_aux (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ) [Nonempty (Idx D N)],
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → (∀ a : Fin D, ntr (Ea D N a * Λ) = 0) →
      ∀ z : ℂ, 0 < z.im → ∀ L : Matrix (Idx D N) (Idx D N) ℂ, Tay_lead D N L →
      ∀ (s : Fin n → Bool) (a : Fin n → Fin D) (b : Fin D),
        ‖ntr (L * (List.ofFn fun i : Fin n =>
            (if s i then (MSol Λ z)ᴴ else MSol Λ z) * Ea D N (a i)).prod * Λ * Ea D N b)‖ ≤
          C * avgSq Λ := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, fun D N Λ _ hΛ hℓ htr z hz L hL s a b => ?_⟩
    simp only [List.ofFn_zero, List.prod_nil, mul_one]
    rw [Tay_lead_tr htr hL b]
    simp
  | succ n ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    refine ⟨10 / 9 * C + 25 / 18 * (5 / 4) ^ n, by positivity, ?_⟩
    intro D N Λ _ hΛ hℓ htr z hz L hL s a b
    have ha0 := Tay_avgSq_nonneg hΛ
    -- decompose the first factor
    obtain ⟨hg0, c, K, hc, hK, hgK⟩ := Tay_g_decomp hΛ hℓ hz
      (g := if s 0 then (MSol Λ z)ᴴ else MSol Λ z) (by cases s 0 <;> simp)
    set P := (List.ofFn fun i : Fin n =>
      (if s i.succ then (MSol Λ z)ᴴ else MSol Λ z) * Ea D N (a i.succ)).prod with hP
    have hPn : opNorm P ≤ (5 / 4) ^ n := by
      refine Tay_prod_norm (5 / 4) (by norm_num) n _ fun i => ?_
      obtain ⟨h1, -⟩ := Tay_g_decomp hΛ hℓ hz
        (g := if s i.succ then (MSol Λ z)ᴴ else MSol Λ z) (by cases s i.succ <;> simp)
      calc _ ≤ opNorm (if s i.succ then (MSol Λ z)ᴴ else MSol Λ z) *
            opNorm (Ea D N (a i.succ)) := Tay_op_mul _ _
        _ ≤ 5 / 4 * 1 := mul_le_mul h1 (Tay_op_Ea _) (Tay_op_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have hexp : L * (List.ofFn fun i : Fin (n + 1) =>
          (if s i then (MSol Λ z)ᴴ else MSol Λ z) * Ea D N (a i)).prod * Λ * Ea D N b =
        c • (L * Ea D N (a 0) * P * Λ * Ea D N b) +
          L * Λ * (K * Ea D N (a 0) * P) * Λ * Ea D N b := by
      rw [List.ofFn_succ, List.prod_cons, ← hP, hgK]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_assoc]
    rw [hexp, Tay_ntr_add, Tay_ntr_smul]
    -- first term
    have t1 : ‖c * ntr (L * Ea D N (a 0) * P * Λ * Ea D N b)‖ ≤ 10 / 9 * (C * avgSq Λ) := by
      rw [norm_mul]
      refine mul_le_mul hc ?_ (norm_nonneg _) (by norm_num)
      rcases Tay_lead_mul hL (a 0) with h0 | h1
      · rw [h0, zero_mul, zero_mul, zero_mul]
        simp only [ntr, Matrix.trace_zero, mul_zero, norm_zero]
        exact mul_nonneg hC0 ha0
      · have := hC D N Λ hΛ hℓ htr z hz _ h1 (fun i => s i.succ) (fun i => a i.succ) b
        simpa only [mul_assoc] using this
    -- second term
    have t2 : ‖ntr (L * Λ * (K * Ea D N (a 0) * P) * Λ * Ea D N b)‖ ≤
        25 / 18 * (5 / 4) ^ n * avgSq Λ := by
      have e : ntr (L * Λ * (K * Ea D N (a 0) * P) * Λ * Ea D N b) =
          ntr ((Ea D N b * L) * Λ * (K * Ea D N (a 0) * P) * Λ) := by
        unfold ntr
        rw [← Matrix.trace_mul_comm]
        simp only [mul_assoc]
      rw [e]
      refine (Tay_BL hΛ _ _).trans ?_
      have hU : opNorm (Ea D N b * L) ≤ 1 := by
        calc _ ≤ opNorm (Ea D N b) * opNorm L := Tay_op_mul _ _
          _ ≤ 1 * 1 := mul_le_mul (Tay_op_Ea b) (Tay_lead_op hL) (Tay_op_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      have hV : opNorm (K * Ea D N (a 0) * P) ≤ 25 / 18 * (5 / 4) ^ n := by
        calc _ ≤ opNorm (K * Ea D N (a 0)) * opNorm P := Tay_op_mul _ _
          _ ≤ (25 / 18 * 1) * (5 / 4) ^ n := by
            refine mul_le_mul ?_ hPn (Tay_op_nonneg _) (by norm_num)
            exact (Tay_op_mul _ _).trans
              (mul_le_mul hK (Tay_op_Ea _) (Tay_op_nonneg _) (by norm_num))
          _ = _ := by ring
      have := mul_le_mul hU hV (Tay_op_nonneg _) (by norm_num)
      nlinarith
    calc _ ≤ ‖c * ntr (L * Ea D N (a 0) * P * Λ * Ea D N b)‖ +
          ‖ntr (L * Λ * (K * Ea D N (a 0) * P) * Λ * Ea D N b)‖ := norm_add_le _ _
      _ ≤ _ := by nlinarith

end A7b

section Spec

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `U diag(d) U^*` for a unitary `U`. -/
private def Tay_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (diagonal d)

private lemma Tay_cd_mul (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    Tay_cd U d * Tay_cd U e = Tay_cd U (fun j => d j * e j) := by
  rw [Tay_cd, Tay_cd, Tay_cd, ← map_mul, diagonal_mul_diagonal]

private lemma Tay_cd_one (U : Matrix.unitaryGroup ι ℂ) : Tay_cd U (fun _ => 1) = 1 := by
  rw [Tay_cd, diagonal_one, map_one]

private lemma Tay_cd_smul (U : Matrix.unitaryGroup ι ℂ) (c : ℂ) (d : ι → ℂ) :
    c • Tay_cd U d = Tay_cd U (fun j => c * d j) := by
  rw [Tay_cd, Tay_cd, ← map_smul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

private lemma Tay_cd_sub (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    Tay_cd U d - Tay_cd U e = Tay_cd U (fun j => d j - e j) := by
  rw [Tay_cd, Tay_cd, Tay_cd, ← map_sub, diagonal_sub]

private lemma Tay_cd_sub_smul_one (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (c : ℂ) :
    Tay_cd U d - c • (1 : Matrix ι ι ℂ) = Tay_cd U (fun j => d j - c) := by
  rw [← Tay_cd_one U, Tay_cd_smul, Tay_cd_sub]
  simp

private lemma Tay_cd_pow (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (l : ℕ) :
    Tay_cd U d ^ l = Tay_cd U (fun j => d j ^ l) := by
  rw [Tay_cd, Tay_cd, ← map_pow, diagonal_pow]
  rfl

private lemma Tay_cd_conjTranspose (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    (Tay_cd U d)ᴴ = Tay_cd U (fun j => star (d j)) := by
  rw [← star_eq_conjTranspose, Tay_cd, Tay_cd, ← map_star, star_eq_conjTranspose,
    diagonal_conjTranspose]
  rfl

private lemma Tay_ntr_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    ntr (Tay_cd U d) = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, d j := by
  rw [ntr, Tay_cd, Unitary.conjStarAlgAut_apply, trace_mul_comm, ← mul_assoc,
    Unitary.star_mul_self_of_mem U.property, one_mul, trace_diagonal]

private lemma Tay_cd_inv (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (h : ∀ j, d j ≠ 0) :
    (Tay_cd U d)⁻¹ = Tay_cd U (fun j => (d j)⁻¹) := by
  apply inv_eq_right_inv
  rw [Tay_cd_mul]
  simp only [mul_inv_cancel₀ (h _)]
  exact Tay_cd_one U

/-- Every eigenvalue of a Hermitian matrix is bounded by the operator norm. -/
private lemma Tay_eig_le {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (j : ι) :
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

/-- The spectral data of `Λ` and of `M`: `Λ = U diag(μ) U^*` with `|μ_j| ≤ ‖Λ‖` and
`M = U diag((μ_j - z - m)⁻¹) U^*`. -/
private lemma Tay_spec_data [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ), (∀ j, |μ j| ≤ opNorm Λ) ∧
      Λ = Tay_cd U (fun j => (μ j : ℂ)) ∧
      MSol Λ z = Tay_cd U (fun j => ((μ j : ℂ) - (z + mSol Λ z))⁻¹) := by
  have hm := (mSol_spec Λ hΛ z hz).1
  refine ⟨hΛ.eigenvectorUnitary, fun j => hΛ.eigenvalues j, Tay_eig_le hΛ, hΛ.spectral_theorem, ?_⟩
  have hs : Λ = Tay_cd hΛ.eigenvectorUnitary (fun j => (hΛ.eigenvalues j : ℂ)) :=
    hΛ.spectral_theorem
  have hne : ∀ j, (hΛ.eigenvalues j : ℂ) - (z + mSol Λ z) ≠ 0 := fun j h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  unfold MSol
  generalize z + mSol Λ z = w at hne ⊢
  conv_lhs => rw [hs]
  rw [Tay_cd_sub_smul_one, Tay_cd_inv _ _ hne]

end Spec

section Poly

/-- The derivative `p m^{p-1}`, defined by recursion: `d_0 = 0`, `d_{p+1} = d_p m + m^p`. -/
private def Tay_dpow : ℕ → ℂ → ℂ
  | 0, _ => 0
  | p + 1, m => Tay_dpow p m * m + m ^ p

private lemma Tay_dpow_bound (B : ℝ) (hB : 0 ≤ B) :
    ∀ p : ℕ, ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ m : ℂ, ‖m‖ ≤ B → ‖Tay_dpow p m‖ ≤ Kd
  | 0 => ⟨0, le_rfl, fun m _ => by simp [Tay_dpow]⟩
  | p + 1 => by
    obtain ⟨K, hK0, hK⟩ := Tay_dpow_bound B hB p
    refine ⟨K * B + B ^ p, by positivity, fun m hm => ?_⟩
    simp only [Tay_dpow]
    calc ‖Tay_dpow p m * m + m ^ p‖ ≤ ‖Tay_dpow p m‖ * ‖m‖ + ‖m‖ ^ p := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_pow]
      _ ≤ K * B + B ^ p := by
          have := hK m hm
          gcongr

/-- Taylor's formula to first order for `u ↦ u^p` with an explicit second-order constant. -/
private lemma Tay_pow_taylor (B : ℝ) (hB : 0 ≤ B) :
    ∀ p : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u m : ℂ, ‖u‖ ≤ B → ‖m‖ ≤ B →
      ‖u ^ p - m ^ p - Tay_dpow p m * (u - m)‖ ≤ K * ‖u - m‖ ^ 2
  | 0 => ⟨0, le_rfl, fun u m _ _ => by simp [Tay_dpow]⟩
  | p + 1 => by
    obtain ⟨K, hK0, hK⟩ := Tay_pow_taylor B hB p
    obtain ⟨Kd, hKd0, hKd⟩ := Tay_dpow_bound B hB p
    refine ⟨Kd + B * K, by positivity, fun u m hu hm => ?_⟩
    have e : u ^ (p + 1) - m ^ (p + 1) - Tay_dpow (p + 1) m * (u - m) =
        Tay_dpow p m * (u - m) ^ 2 + u * (u ^ p - m ^ p - Tay_dpow p m * (u - m)) := by
      simp only [Tay_dpow]
      ring
    rw [e]
    calc _ ≤ ‖Tay_dpow p m * (u - m) ^ 2‖ + ‖u * (u ^ p - m ^ p - Tay_dpow p m * (u - m))‖ :=
          norm_add_le _ _
      _ ≤ Kd * ‖u - m‖ ^ 2 + B * (K * ‖u - m‖ ^ 2) := by
          refine add_le_add ?_ ?_
          · rw [norm_mul, norm_pow]
            exact mul_le_mul_of_nonneg_right (hKd m hm) (by positivity)
          · rw [norm_mul]
            exact mul_le_mul hu (hK u m hu hm) (norm_nonneg _) hB
      _ = _ := by ring

/-- First-order Taylor expansion of `u ↦ u^p (u^*)^q` at `m` for `|u|, |m| ≤ 5/4`. -/
private lemma Tay_mono_taylor (p q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u m : ℂ, ‖u‖ ≤ 5 / 4 → ‖m‖ ≤ 5 / 4 →
      ‖u ^ p * star u ^ q - m ^ p * star m ^ q - (Tay_dpow p m * star m ^ q) * (u - m) -
        (m ^ p * Tay_dpow q (star m)) * star (u - m)‖ ≤ K * ‖u - m‖ ^ 2 := by
  obtain ⟨Kp, hKp0, hKp⟩ := Tay_pow_taylor (5 / 4) (by norm_num) p
  obtain ⟨Kq, hKq0, hKq⟩ := Tay_pow_taylor (5 / 4) (by norm_num) q
  obtain ⟨Kdp, hKdp0, hKdp⟩ := Tay_dpow_bound (5 / 4) (by norm_num) p
  obtain ⟨Kdq, hKdq0, hKdq⟩ := Tay_dpow_bound (5 / 4) (by norm_num) q
  refine ⟨(5 / 4) ^ p * Kq + Kp * (5 / 4) ^ q + Kdp * Kdq + 5 / 2 * Kdp * Kq +
    5 / 2 * Kp * Kdq + 25 / 4 * Kp * Kq, by positivity, fun u m hu hm => ?_⟩
  have hu' : ‖star u‖ ≤ 5 / 4 := by rwa [norm_star]
  have hm' : ‖star m‖ ≤ 5 / 4 := by rwa [norm_star]
  have hRx := hKp u m hu hm
  have hRy := hKq (star u) (star m) hu' hm'
  rw [← star_sub, norm_star] at hRy
  set δ := u - m with hδ
  set a := ‖δ‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have ha2 : a ≤ 5 / 2 := by
    have := norm_sub_le u m
    rw [ha, hδ]
    linarith
  set Rx := u ^ p - m ^ p - Tay_dpow p m * δ with hRxd
  set Ry := star u ^ q - star m ^ q - Tay_dpow q (star m) * star δ with hRyd
  have e : u ^ p * star u ^ q - m ^ p * star m ^ q - (Tay_dpow p m * star m ^ q) * δ -
        (m ^ p * Tay_dpow q (star m)) * star δ =
      m ^ p * Ry + Rx * star m ^ q + (Tay_dpow p m * δ) * (Tay_dpow q (star m) * star δ) +
        (Tay_dpow p m * δ) * Ry + Rx * (Tay_dpow q (star m) * star δ) + Rx * Ry := by
    simp only [hRxd, hRyd]
    ring
  rw [e]
  have b1 : ‖m ^ p * Ry‖ ≤ (5 / 4) ^ p * (Kq * a ^ 2) := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hm p) hRy (norm_nonneg _) (by positivity)
  have b2 : ‖Rx * star m ^ q‖ ≤ (Kp * a ^ 2) * (5 / 4) ^ q := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul hRx (pow_le_pow_left₀ (norm_nonneg _) hm' q) (by positivity) (by positivity)
  have b3 : ‖(Tay_dpow p m * δ) * (Tay_dpow q (star m) * star δ)‖ ≤ Kdp * Kdq * a ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, norm_star]
    have h1 := hKdp m hm
    have h2 := hKdq (star m) hm'
    calc _ ≤ (Kdp * a) * (Kdq * a) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right h1 ha0)
            (mul_le_mul_of_nonneg_right h2 ha0) (by positivity) (by positivity)
      _ = _ := by ring
  have b4 : ‖(Tay_dpow p m * δ) * Ry‖ ≤ Kdp * a * (Kq * a ^ 2) := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hKdp m hm) ha0) hRy (norm_nonneg _)
      (by positivity)
  have b5 : ‖Rx * (Tay_dpow q (star m) * star δ)‖ ≤ (Kp * a ^ 2) * (Kdq * a) := by
    rw [norm_mul, norm_mul, norm_star]
    exact mul_le_mul hRx (mul_le_mul_of_nonneg_right (hKdq _ hm') ha0) (by positivity)
      (by positivity)
  have b6 : ‖Rx * Ry‖ ≤ (Kp * a ^ 2) * (Kq * a ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul hRx hRy (norm_nonneg _) (by positivity)
  have n1 := norm_add_le (m ^ p * Ry + Rx * star m ^ q +
    (Tay_dpow p m * δ) * (Tay_dpow q (star m) * star δ) +
    (Tay_dpow p m * δ) * Ry + Rx * (Tay_dpow q (star m) * star δ)) (Rx * Ry)
  have n2 := norm_add_le (m ^ p * Ry + Rx * star m ^ q +
    (Tay_dpow p m * δ) * (Tay_dpow q (star m) * star δ) +
    (Tay_dpow p m * δ) * Ry) (Rx * (Tay_dpow q (star m) * star δ))
  have n3 := norm_add_le (m ^ p * Ry + Rx * star m ^ q +
    (Tay_dpow p m * δ) * (Tay_dpow q (star m) * star δ)) ((Tay_dpow p m * δ) * Ry)
  have n4 := norm_add_le (m ^ p * Ry + Rx * star m ^ q)
    ((Tay_dpow p m * δ) * (Tay_dpow q (star m) * star δ))
  have n5 := norm_add_le (m ^ p * Ry) (Rx * star m ^ q)
  have c4 : Kdp * a * (Kq * a ^ 2) ≤ 5 / 2 * Kdp * Kq * a ^ 2 := by
    have : Kdp * Kq * a ^ 2 * a ≤ Kdp * Kq * a ^ 2 * (5 / 2) :=
      mul_le_mul_of_nonneg_left ha2 (by positivity)
    nlinarith
  have c5 : (Kp * a ^ 2) * (Kdq * a) ≤ 5 / 2 * Kp * Kdq * a ^ 2 := by
    have : Kp * Kdq * a ^ 2 * a ≤ Kp * Kdq * a ^ 2 * (5 / 2) :=
      mul_le_mul_of_nonneg_left ha2 (by positivity)
    nlinarith
  have c6 : (Kp * a ^ 2) * (Kq * a ^ 2) ≤ 25 / 4 * Kp * Kq * a ^ 2 := by
    have h1 : a ^ 2 ≤ (5 / 2) ^ 2 := pow_le_pow_left₀ ha0 ha2 2
    have : Kp * Kq * a ^ 2 * a ^ 2 ≤ Kp * Kq * a ^ 2 * (5 / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  nlinarith

end Poly

section A6

/-- The scalar form of (A.6) [estimate_replace_M_by_m]: for `a_j = (μ_j - w)⁻¹`, `|μ_j| ≤ 1/10`,
`|w| > 9/10`, `m` the mean of the `a_j`: the mean of `a_j^p (a_j^*)^q` differs from
`m^p (m^*)^q` by at most `K ⟨μ²⟩`. -/
private lemma Tay_A6_scalar (p q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (μ : ι → ℝ) (w : ℂ),
      (∀ j, |μ j| ≤ 1 / 10) → 9 / 10 < ‖w‖ →
      ‖((Fintype.card ι : ℂ))⁻¹ * (∑ j, ((μ j : ℂ) - w)⁻¹ ^ p * star ((μ j : ℂ) - w)⁻¹ ^ q) -
        (((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((μ j : ℂ) - w)⁻¹) ^ p *
          star (((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((μ j : ℂ) - w)⁻¹) ^ q‖ ≤
        K * (((Fintype.card ι : ℝ))⁻¹ * ∑ j, μ j ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := Tay_mono_taylor p q
  refine ⟨K * (4 * (25 / 18) ^ 2), by positivity, fun ι _ _ _ μ w hμ hw => ?_⟩
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hnC : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  set a : ι → ℂ := fun j => ((μ j : ℂ) - w)⁻¹ with ha
  set m : ℂ := ((Fintype.card ι : ℂ))⁻¹ * ∑ j, a j with hm
  set S2 : ℝ := ∑ j, μ j ^ 2 with hS2
  have hS2n : 0 ≤ S2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  -- bounds on `a_j` and `m`
  have hden : ∀ j, 4 / 5 < ‖(μ j : ℂ) - w‖ := fun j => by
    have h1 := norm_sub_norm_le w (μ j : ℂ)
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [hμ j]
  have haj : ∀ j, ‖a j‖ ≤ 5 / 4 := fun j => by
    rw [ha]; dsimp only
    rw [norm_inv, inv_le_comm₀ (by linarith [hden j]) (by norm_num)]
    linarith [hden j]
  have hmn : ‖m‖ ≤ 5 / 4 := by
    rw [hm, norm_mul, norm_inv, Complex.norm_natCast]
    have : ‖∑ j, a j‖ ≤ Fintype.card ι * (5 / 4) :=
      (norm_sum_le _ _).trans (by
        calc ∑ j, ‖a j‖ ≤ ∑ _j : ι, (5 / 4 : ℝ) := Finset.sum_le_sum fun j _ => haj j
          _ = _ := by simp)
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ j, a j‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι * (5 / 4)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 5 / 4 := by field_simp
  -- distance to `c = -1/w`
  set c : ℂ := -w⁻¹ with hc
  have hdc : ∀ j, ‖a j - c‖ ≤ 25 / 18 * |μ j| := fun j => by
    have hne : (μ j : ℂ) - w ≠ 0 := fun h => by
      have := hden j; rw [h, norm_zero] at this; linarith
    have e : a j - c = (μ j : ℂ) * a j * w⁻¹ := by
      rw [ha, hc]; dsimp only
      field_simp
      ring
    rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inv w]
    have h1 : ‖w‖⁻¹ ≤ 10 / 9 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc |μ j| * ‖a j‖ * ‖w‖⁻¹ ≤ |μ j| * (5 / 4) * (10 / 9) := by
          gcongr
          exact haj j
      _ = _ := by ring
  have hmc : ‖m - c‖ ≤ 25 / 18 * ((Fintype.card ι : ℝ)⁻¹ * ∑ j, |μ j|) := by
    have e : m - c = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (a j - c) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm]
      field_simp
    rw [e, norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ j, (a j - c)‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ j, (25 / 18 * |μ j|) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun j _ => hdc j)) (by positivity)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hcs : (∑ j, |μ j|) ^ 2 ≤ Fintype.card ι * S2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun j => |μ j|)
    simpa [sq_abs, hS2] using this
  have he2 : ‖m - c‖ ^ 2 ≤ (25 / 18) ^ 2 * ((Fintype.card ι : ℝ)⁻¹ * S2) := by
    have h0 : 0 ≤ ‖m - c‖ := norm_nonneg _
    calc ‖m - c‖ ^ 2 ≤ (25 / 18 * ((Fintype.card ι : ℝ)⁻¹ * ∑ j, |μ j|)) ^ 2 :=
          pow_le_pow_left₀ h0 hmc 2
      _ = (25 / 18) ^ 2 * ((Fintype.card ι : ℝ)⁻¹) ^ 2 * (∑ j, |μ j|) ^ 2 := by ring
      _ ≤ (25 / 18) ^ 2 * ((Fintype.card ι : ℝ)⁻¹) ^ 2 * (Fintype.card ι * S2) := by gcongr
      _ = _ := by field_simp
  -- the deviations `δ_j = a_j - m`
  have hsum0 : ∑ j, (a j - m) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm]
    field_simp
    ring
  have hR : ∑ j, ‖a j - m‖ ^ 2 ≤ 4 * (25 / 18) ^ 2 * S2 := by
    have h1 : ∀ j, ‖a j - m‖ ^ 2 ≤ 2 * ((25 / 18) ^ 2 * μ j ^ 2) + 2 * ‖m - c‖ ^ 2 := fun j => by
      have h2 : ‖a j - m‖ ≤ 25 / 18 * |μ j| + ‖m - c‖ := by
        calc ‖a j - m‖ = ‖(a j - c) - (m - c)‖ := by congr 1; ring
          _ ≤ ‖a j - c‖ + ‖m - c‖ := norm_sub_le _ _
          _ ≤ _ := by linarith [hdc j]
      have h3 : 0 ≤ ‖a j - m‖ := norm_nonneg _
      calc ‖a j - m‖ ^ 2 ≤ (25 / 18 * |μ j| + ‖m - c‖) ^ 2 := pow_le_pow_left₀ h3 h2 2
        _ ≤ 2 * ((25 / 18 * |μ j|) ^ 2) + 2 * ‖m - c‖ ^ 2 := by
          nlinarith [sq_nonneg (25 / 18 * |μ j| - ‖m - c‖)]
        _ = _ := by rw [mul_pow, sq_abs]
    calc ∑ j, ‖a j - m‖ ^ 2 ≤ ∑ j, (2 * ((25 / 18) ^ 2 * μ j ^ 2) + 2 * ‖m - c‖ ^ 2) :=
          Finset.sum_le_sum fun j _ => h1 j
      _ = 2 * (25 / 18) ^ 2 * S2 + 2 * (Fintype.card ι : ℝ) * ‖m - c‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hS2, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ 2 * (25 / 18) ^ 2 * S2 + 2 * (Fintype.card ι : ℝ) *
            ((25 / 18) ^ 2 * ((Fintype.card ι : ℝ)⁻¹ * S2)) := by gcongr
      _ = _ := by field_simp; ring
  -- per-index Taylor remainder
  set E : ι → ℂ := fun j => a j ^ p * star (a j) ^ q - m ^ p * star m ^ q -
    (Tay_dpow p m * star m ^ q) * (a j - m) - (m ^ p * Tay_dpow q (star m)) * star (a j - m)
    with hE
  have hEb : ∀ j, ‖E j‖ ≤ K * ‖a j - m‖ ^ 2 := fun j => hK (a j) m (haj j) hmn
  have hmain : ((Fintype.card ι : ℂ))⁻¹ * (∑ j, a j ^ p * star (a j) ^ q) - m ^ p * star m ^ q =
      ((Fintype.card ι : ℂ))⁻¹ * ∑ j, E j := by
    have h1 : ∑ j, E j =
        (∑ j, a j ^ p * star (a j) ^ q) - Fintype.card ι * (m ^ p * star m ^ q) := by
      have hs1 : ∑ j, star (a j - m) = 0 := by rw [← star_sum, hsum0, star_zero]
      have : ∑ j, E j = (∑ j, (a j ^ p * star (a j) ^ q - m ^ p * star m ^ q)) -
          (Tay_dpow p m * star m ^ q) * (∑ j, (a j - m)) -
          (m ^ p * Tay_dpow q (star m)) * ∑ j, star (a j - m) := by
        simp only [hE, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [this, hsum0, hs1]
      simp [Finset.sum_sub_distrib]
    rw [h1]
    field_simp
  rw [hmain, norm_mul, norm_inv, Complex.norm_natCast]
  calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ j, E j‖
      ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ j, K * ‖a j - m‖ ^ 2 :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => hEb j)) (by positivity)
    _ = K * ((Fintype.card ι : ℝ)⁻¹ * ∑ j, ‖a j - m‖ ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ K * ((Fintype.card ι : ℝ)⁻¹ * (4 * (25 / 18) ^ 2 * S2)) := by gcongr
    _ = _ := by ring

end A6

section A6b

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `⟨Λ²⟩ = |ι|⁻¹ ∑ μ_j²` for `Λ = U diag(μ) U^*`. -/
private lemma Tay_avgSq_cd (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) :
    avgSq (Tay_cd U (fun j => (μ j : ℂ))) = (Fintype.card ι : ℝ)⁻¹ * ∑ j, μ j ^ 2 := by
  unfold avgSq
  rw [Tay_cd_mul, Tay_ntr_cd]
  have : ((Fintype.card ι : ℂ))⁻¹ * ∑ j, (μ j : ℂ) * (μ j : ℂ) =
      (((Fintype.card ι : ℝ)⁻¹ * ∑ j, μ j ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp only [sq]
  rw [this, Complex.ofReal_re]

end A6b

section A12

/-- `|1 - m²|² = (1 - |m|²)² + 4 (Im m)²`. -/
private lemma Tay_one_sub_sq (m : ℂ) : ‖1 - m ^ 2‖ ^ 2 = (1 - ‖m‖ ^ 2) ^ 2 + 4 * m.im ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp [sq]
  ring

private lemma Tay_one_sub_sq_ge (m : ℂ) : 2 * m.im ≤ ‖1 - m ^ 2‖ := by
  by_contra h
  push Not at h
  have h1 := Tay_one_sub_sq m
  have h2 : 0 ≤ ‖1 - m ^ 2‖ := norm_nonneg _
  nlinarith [sq_nonneg (1 - ‖m‖ ^ 2)]

private lemma Tay_one_sub_sq_le (m : ℂ) (hm : ‖m‖ ≤ 1) (hy : 0 ≤ m.im) :
    ‖1 - m ^ 2‖ ≤ (1 - ‖m‖ ^ 2) + 2 * m.im := by
  by_contra h
  push Not at h
  have h1 := Tay_one_sub_sq m
  have h2 : 0 ≤ ‖1 - m ^ 2‖ := norm_nonneg _
  have h3 : 0 ≤ 1 - ‖m‖ ^ 2 := by nlinarith [norm_nonneg m]
  nlinarith

/-- Real and imaginary parts of the square of `(x - w)⁻¹`. -/
private lemma Tay_inv_sq_parts (x : ℝ) (w : ℂ) (hN : 0 < Complex.normSq ((x : ℂ) - w)) :
    Complex.normSq ((x : ℂ) - w) = (x - w.re) ^ 2 + w.im ^ 2 ∧
    ((((x : ℂ) - w)⁻¹) ^ 2).re =
        ((x - w.re) ^ 2 - w.im ^ 2) / Complex.normSq ((x : ℂ) - w) ^ 2 ∧
    ((((x : ℂ) - w)⁻¹) ^ 2).im =
        2 * (x - w.re) * w.im / Complex.normSq ((x : ℂ) - w) ^ 2 := by
  have hN' : Complex.normSq ((x : ℂ) - w) = (x - w.re) ^ 2 + w.im ^ 2 := by
    rw [Complex.normSq_apply]; simp [sq]
  refine ⟨hN', ?_, ?_⟩
  · rw [sq, Complex.mul_re, Complex.inv_re, Complex.inv_im]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
    field_simp
  · rw [sq, Complex.mul_im, Complex.inv_re, Complex.inv_im]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
    field_simp
    ring

private lemma Tay_normSq_lower (x : ℝ) (w : ℂ) (hx : |x| ≤ 1 / 10) (hw : 9 / 10 < ‖w‖) :
    16 / 25 ≤ Complex.normSq ((x : ℂ) - w) := by
  have h1 := norm_sub_norm_le w (x : ℂ)
  rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at h1
  rw [Complex.normSq_eq_norm_sq]
  nlinarith

private lemma Tay_normSq_upper (x : ℝ) (w : ℂ) (R : ℝ) (hx : |x| ≤ 1 / 10) (hR : ‖w‖ ≤ R) :
    Complex.normSq ((x : ℂ) - w) ≤ (R + 1 / 10) ^ 2 := by
  have h1 := norm_sub_le (x : ℂ) w
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  rw [Complex.normSq_eq_norm_sq]
  have h2 : 0 ≤ ‖(x : ℂ) - w‖ := norm_nonneg _
  nlinarith

/-- Case `|Re w| < 1/2`: `Re (x - w)⁻² ≤ 1/4`. -/
private lemma Tay_case_mid (x : ℝ) (w : ℂ) (hx : |x| ≤ 1 / 10) (hw : 9 / 10 < ‖w‖)
    (hu : |w.re| < 1 / 2) : ((((x : ℂ) - w)⁻¹) ^ 2).re ≤ 1 / 4 := by
  have hlow := Tay_normSq_lower x w hx hw
  obtain ⟨hN, hre, -⟩ := Tay_inv_sq_parts x w (by linarith)
  rw [hre]
  set N := Complex.normSq ((x : ℂ) - w) with hNdef
  have hxu : (x - w.re) ^ 2 ≤ 9 / 25 := by
    have := abs_lt.1 hu
    have := abs_le.1 hx
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg w.im]

/-- Case `Re w ≥ 1/2`. -/
private lemma Tay_case_pos (x : ℝ) (w : ℂ) (R : ℝ) (hx : |x| ≤ 1 / 10) (hw : 9 / 10 < ‖w‖)
    (hR : ‖w‖ ≤ R) (hb : 0 < w.im) (hu : 1 / 2 ≤ w.re) :
    ((((x : ℂ) - w)⁻¹) ^ 2).im ≤ -(4 / 5 * w.im / (R + 1 / 10) ^ 4) := by
  have hlow := Tay_normSq_lower x w hx hw
  have hup := Tay_normSq_upper x w R hx hR
  obtain ⟨hN, -, him⟩ := Tay_inv_sq_parts x w (by linarith)
  rw [him]
  set N := Complex.normSq ((x : ℂ) - w) with hNdef
  have hx1 := abs_le.1 hx
  have hR0 : 0 < R + 1 / 10 := by nlinarith [norm_nonneg w]
  have hN2 : N ^ 2 ≤ (R + 1 / 10) ^ 4 := by
    have : (R + 1 / 10) ^ 4 = ((R + 1 / 10) ^ 2) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) hup 2
  have hN0 : 0 < N ^ 2 := by positivity
  have hnum : 2 * (x - w.re) * w.im ≤ -(4 / 5 * w.im) := by nlinarith
  rw [div_le_iff₀ hN0, neg_mul]
  have h1 : 4 / 5 * w.im / (R + 1 / 10) ^ 4 * (R + 1 / 10) ^ 4 = 4 / 5 * w.im :=
    div_mul_cancel₀ _ (pow_ne_zero 4 hR0.ne')
  have h2 : 4 / 5 * w.im / (R + 1 / 10) ^ 4 * N ^ 2 ≤ 4 / 5 * w.im := by
    calc _ ≤ 4 / 5 * w.im / (R + 1 / 10) ^ 4 * (R + 1 / 10) ^ 4 := by
          gcongr
      _ = _ := h1
  linarith

/-- Case `Re w ≤ -1/2`. -/
private lemma Tay_case_neg (x : ℝ) (w : ℂ) (R : ℝ) (hx : |x| ≤ 1 / 10) (hw : 9 / 10 < ‖w‖)
    (hR : ‖w‖ ≤ R) (hb : 0 < w.im) (hu : w.re ≤ -(1 / 2)) :
    4 / 5 * w.im / (R + 1 / 10) ^ 4 ≤ ((((x : ℂ) - w)⁻¹) ^ 2).im := by
  have hlow := Tay_normSq_lower x w hx hw
  have hup := Tay_normSq_upper x w R hx hR
  obtain ⟨hN, -, him⟩ := Tay_inv_sq_parts x w (by linarith)
  rw [him]
  set N := Complex.normSq ((x : ℂ) - w) with hNdef
  have hx1 := abs_le.1 hx
  have hR0 : 0 < R + 1 / 10 := by nlinarith [norm_nonneg w]
  have hN2 : N ^ 2 ≤ (R + 1 / 10) ^ 4 := by
    have : (R + 1 / 10) ^ 4 = ((R + 1 / 10) ^ 2) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) hup 2
  have hN0 : 0 < N ^ 2 := by positivity
  have hnum : 4 / 5 * w.im ≤ 2 * (x - w.re) * w.im := by nlinarith
  rw [le_div_iff₀ hN0]
  have h2 : 4 / 5 * w.im / (R + 1 / 10) ^ 4 * N ^ 2 ≤ 4 / 5 * w.im := by
    calc _ ≤ 4 / 5 * w.im / (R + 1 / 10) ^ 4 * (R + 1 / 10) ^ 4 := by
          gcongr
      _ = _ := div_mul_cancel₀ _ (pow_ne_zero 4 hR0.ne')
  linarith

end A12

section A12b

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma Tay_re_avg (f : ι → ℂ) :
    (((Fintype.card ι : ℂ))⁻¹ * ∑ j, f j).re = (Fintype.card ι : ℝ)⁻¹ * ∑ j, (f j).re := by
  rw [show ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    Complex.re_ofReal_mul, Complex.re_sum]

omit [DecidableEq ι] in
private lemma Tay_im_avg (f : ι → ℂ) :
    (((Fintype.card ι : ℂ))⁻¹ * ∑ j, f j).im = (Fintype.card ι : ℝ)⁻¹ * ∑ j, (f j).im := by
  rw [show ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    Complex.im_ofReal_mul, Complex.im_sum]

omit [DecidableEq ι] in
private lemma Tay_avg_le [Nonempty ι] (g : ι → ℝ) (c : ℝ) (h : ∀ j, g j ≤ c) :
    (Fintype.card ι : ℝ)⁻¹ * ∑ j, g j ≤ c := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc (Fintype.card ι : ℝ)⁻¹ * ∑ j, g j ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _j : ι, c :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => h j) (by positivity)
    _ = c := by simp

omit [DecidableEq ι] in
private lemma Tay_le_avg [Nonempty ι] (g : ι → ℝ) (c : ℝ) (h : ∀ j, c ≤ g j) :
    c ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ j, g j := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc c = (Fintype.card ι : ℝ)⁻¹ * ∑ _j : ι, c := by simp
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ j, g j :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => h j) (by positivity)

/-- The lower bound `|1 - ⟨M²⟩| ≳ Im m` of (A.12) [de_ir_0] (no spectral condition on `z`). -/
private lemma Tay_A12_lower [Nonempty ι] {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ} (hz : 0 < z.im) (R : ℝ) (hR : ‖z + mSol Λ z‖ ≤ R) :
    min (3 / 4) (4 / 5 / (R + 1 / 10) ^ 4) * (mSol Λ z).im ≤ ‖1 - ntr (MSol Λ z ^ 2)‖ := by
  obtain ⟨hw, hm1, hm, -⟩ := Tay_facts hΛ hℓ hz
  obtain ⟨U, μ, hμ, hΛd, hMd⟩ := Tay_spec_data hΛ hz
  have hb : 0 < (z + mSol Λ z).im := by simp; linarith
  have hbm : (mSol Λ z).im ≤ (z + mSol Λ z).im := by simp; linarith
  have hymm : (mSol Λ z).im ≤ 1 := by
    have := Complex.abs_im_le_norm (mSol Λ z)
    linarith [le_abs_self (mSol Λ z).im]
  have hnt : ntr (MSol Λ z ^ 2) = ((Fintype.card ι : ℂ))⁻¹ *
      ∑ j, ((μ j : ℂ) - (z + mSol Λ z))⁻¹ ^ 2 := by
    rw [hMd, Tay_cd_pow, Tay_ntr_cd]
  rw [hnt]
  generalize z + mSol Λ z = w at hw hb hbm hR
  generalize (mSol Λ z).im = y at hm hbm hymm ⊢
  have hμ' : ∀ j, |μ j| ≤ 1 / 10 := fun j => (hμ j).trans hℓ
  set T : ℂ := ((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((μ j : ℂ) - w)⁻¹ ^ 2 with hT
  have hR0 : 0 < R + 1 / 10 := by nlinarith [norm_nonneg w]
  have hmin0 : 0 < min (3 / 4 : ℝ) (4 / 5 / (R + 1 / 10) ^ 4) := by
    apply lt_min (by norm_num); positivity
  rcases lt_or_ge |w.re| (1 / 2) with hu | hu
  · -- middle
    have h1 : T.re ≤ 1 / 4 := by
      rw [hT, Tay_re_avg]
      exact Tay_avg_le _ _ fun j => Tay_case_mid (μ j) w (hμ' j) hw hu
    have h2 : |(1 - T).re| ≤ ‖1 - T‖ := Complex.abs_re_le_norm _
    have h3 : (1 - T).re = 1 - T.re := by simp
    rw [h3] at h2
    have h4 := le_abs_self (1 - T.re)
    calc min (3 / 4) (4 / 5 / (R + 1 / 10) ^ 4) * y ≤ 3 / 4 * y := by
          gcongr; exact min_le_left _ _
      _ ≤ 3 / 4 * 1 := by gcongr
      _ ≤ _ := by linarith
  · have hu' : 1 / 2 ≤ w.re ∨ w.re ≤ -(1 / 2) := by
      rcases le_abs'.1 hu with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hc : min (3 / 4) (4 / 5 / (R + 1 / 10) ^ 4) * y ≤ 4 / 5 * w.im / (R + 1 / 10) ^ 4 := by
      calc min (3 / 4) (4 / 5 / (R + 1 / 10) ^ 4) * y ≤ 4 / 5 / (R + 1 / 10) ^ 4 * w.im := by
            gcongr
            exact min_le_right _ _
        _ = _ := by ring
    have h2 : |(1 - T).im| ≤ ‖1 - T‖ := Complex.abs_im_le_norm _
    have h3 : (1 - T).im = -T.im := by simp
    rw [h3] at h2
    rcases hu' with h | h
    · have h1 : T.im ≤ -(4 / 5 * w.im / (R + 1 / 10) ^ 4) := by
        rw [hT, Tay_im_avg]
        exact Tay_avg_le _ _ fun j => Tay_case_pos (μ j) w R (hμ' j) hw hR hb h
      have := neg_abs_le (-T.im)
      have := le_abs_self (-T.im)
      linarith
    · have h1 : 4 / 5 * w.im / (R + 1 / 10) ^ 4 ≤ T.im := by
        rw [hT, Tay_im_avg]
        exact Tay_le_avg _ _ fun j => Tay_case_neg (μ j) w R (hμ' j) hw hR hb h
      have := le_abs_self (-T.im)
      have := neg_abs_le (T.im)
      have := abs_neg T.im
      have h5 := le_abs_self T.im
      rw [← abs_neg] at h5
      linarith [abs_neg T.im]

end A12b

/-- (A.5) [eq:msc]: `|m - m_sc| ≤ C‖Λ‖^{1/2}` and `‖M - m_sc‖ ≤ C‖Λ‖^{1/2}` for `|z| ≤ τ⁻¹`,
`η > 0`; the constant depends on `τ` only. -/
theorem eq_msc (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
        ‖mSol Λ z - msc z‖ ≤ C * Real.sqrt (opNorm Λ) ∧
          opNorm (MSol Λ z - msc z • (1 : Matrix ι ι ℂ)) ≤ C * Real.sqrt (opNorm Λ) := by
  have _hτ := hτ
  refine ⟨12, by norm_num, fun ι _ _ _ Λ hΛ hℓ z _ hz => ?_⟩
  have hl0 := Tay_op_nonneg Λ
  set q := Real.sqrt (opNorm Λ) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = opNorm Λ := Real.sq_sqrt hl0
  have hq1 : q ≤ 1 / 3 := by nlinarith
  obtain ⟨h1, h2⟩ := Tay_eq_msc_core hΛ hℓ hz (9 / 8 * q) (by positivity) (by linarith)
    ((Tay_resid_le hΛ hℓ hz).trans (by nlinarith))
  constructor
  · linarith
  · refine h2.trans ?_
    nlinarith

/-- The form of (A.5) [eq:msc] with `⟨Λ⟩ = 0`: `|m - m_sc| + ‖M - m_sc‖ ≤ C‖Λ‖`. -/
theorem eq_msc_traceless (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → ntr Λ = 0 → ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
        ‖mSol Λ z - msc z‖ + opNorm (MSol Λ z - msc z • (1 : Matrix ι ι ℂ)) ≤
          C * opNorm Λ := by
  have _hτ := hτ
  refine ⟨22, by norm_num, fun ι _ _ _ Λ hΛ hℓ htr z _ hz => ?_⟩
  have hl0 := Tay_op_nonneg Λ
  have hav := Tay_avgSq_le Λ
  obtain ⟨h1, h2⟩ := Tay_eq_msc_core hΛ hℓ hz (6 / 5 * opNorm Λ) (by positivity) (by linarith)
    ((Tay_resid_traceless hΛ hℓ htr hz).trans (by nlinarith))
  linarith

/-- (A.6) [estimate_replace_M_by_m] for the monomials `M^p (M^*)^q`, `p, q ≤ d` (every word in
`M`, `M^*` is one of these, since `M` and `M^*` commute):
`|⟨M^p (M^*)^q⟩ - m^p m̄^q| ≤ C ⟨Λ²⟩` when `⟨Λ⟩ = 0`; the constant depends on `τ` and `d`. -/
theorem estimate_replace_M_by_m (τ : ℝ) (hτ : 0 < τ) (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → ntr Λ = 0 → ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
        ∀ p q : ℕ, p ≤ d → q ≤ d →
          ‖ntr (MSol Λ z ^ p * (MSol Λ z)ᴴ ^ q) - mSol Λ z ^ p * star (mSol Λ z) ^ q‖ ≤
            C * avgSq Λ := by
  have _hτ := hτ
  choose K hK0 hK using Tay_A6_scalar
  refine ⟨(∑ p ∈ Finset.range (d + 1), ∑ q ∈ Finset.range (d + 1), K p q) + 1, ?_, ?_⟩
  · have : 0 ≤ ∑ p ∈ Finset.range (d + 1), ∑ q ∈ Finset.range (d + 1), K p q :=
      Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => hK0 p q
    linarith
  intro ι _ _ _ Λ hΛ hℓ _ z _ hz p q hp hq
  obtain ⟨hw, -, -, -⟩ := Tay_facts hΛ hℓ hz
  obtain ⟨U, μ, hμ, hΛd, hMd⟩ := Tay_spec_data hΛ hz
  have hmn := (mSol_spec Λ hΛ z hz).2.1
  have havg : avgSq Λ = (Fintype.card ι : ℝ)⁻¹ * ∑ j, μ j ^ 2 := by
    rw [hΛd]; exact Tay_avgSq_cd U μ
  have hKle : K p q ≤ ∑ p ∈ Finset.range (d + 1), ∑ q ∈ Finset.range (d + 1), K p q := by
    refine (Finset.single_le_sum (f := fun q => K p q) (fun q _ => hK0 p q)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hq))).trans ?_
    exact Finset.single_le_sum (f := fun p => ∑ q ∈ Finset.range (d + 1), K p q)
      (fun p _ => Finset.sum_nonneg fun q _ => hK0 p q) (Finset.mem_range.2 (Nat.lt_succ_of_le hp))
  generalize hwdef : z + mSol Λ z = w at hw hMd
  have h1 : ntr (MSol Λ z ^ p * (MSol Λ z)ᴴ ^ q) = ((Fintype.card ι : ℂ))⁻¹ *
      ∑ j, ((μ j : ℂ) - w)⁻¹ ^ p * star ((μ j : ℂ) - w)⁻¹ ^ q := by
    rw [hMd, Tay_cd_pow, Tay_cd_conjTranspose, Tay_cd_pow, Tay_cd_mul, Tay_ntr_cd]
  have h2 : mSol Λ z = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, ((μ j : ℂ) - w)⁻¹ := by
    rw [hmn, hMd, Tay_ntr_cd]
  have key := hK p q ι μ w (fun j => (hμ j).trans hℓ) hw
  rw [← h2] at key
  rw [h1]
  rw [← havg] at key
  have ha0 : 0 ≤ avgSq Λ := Tay_avgSq_nonneg hΛ
  calc _ ≤ K p q * avgSq Λ := key
    _ ≤ _ := by nlinarith

/-- (A.7) [add_one_more_Lambda]: `⟨(Π_{i<n} M^{s_i} E_{a_i}) Λ E_b⟩ = O(⟨Λ²⟩)` when every
diagonal block of `Λ` is traceless; `s_i = true` stands for `M^*`; the constant depends on `τ`
and `n`. -/
theorem add_one_more_Lambda (τ : ℝ) (hτ : 0 < τ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D N : ℕ) (Λ : Matrix (Idx D N) (Idx D N) ℂ), 1 ≤ N →
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → (∀ a : Fin D, ntr (Ea D N a * Λ) = 0) →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im →
      ∀ (s : Fin n → Bool) (a : Fin n → Fin D) (b : Fin D),
        ‖ntr ((List.ofFn fun i : Fin n =>
            (if s i then (MSol Λ z)ᴴ else MSol Λ z) * Ea D N (a i)).prod * Λ * Ea D N b)‖ ≤
          C * avgSq Λ := by
  have _hτ := hτ
  obtain ⟨C, hC0, hC⟩ := Tay_A7_aux n
  refine ⟨C + 1, by linarith, fun D N Λ hN hΛ hℓ htr z _ hz s a b => ?_⟩
  have : Nonempty (Idx D N) := ⟨(b, ⟨0, hN⟩)⟩
  have h := hC D N Λ hΛ hℓ htr z hz 1 (Or.inl rfl) s a b
  rw [one_mul] at h
  have ha0 := Tay_avgSq_nonneg hΛ
  calc _ ≤ C * avgSq Λ := h
    _ ≤ (C + 1) * avgSq Λ := by nlinarith

set_option maxHeartbeats 1000000 in
/-- (A.12) [de_ir_0]: for `E ∈ [E⁻, E⁺]`, `|z| ≤ τ⁻¹`, `η > 0` and `⟨Λ⟩ = 0`,
`Im m ≲ |1 - ⟨M²⟩| ≲ Im m + ⟨Λ²⟩` and `Im m ≲ |1 - m²| ≲ Im m + ⟨Λ²⟩`. -/
theorem de_ir_0 (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → ntr Λ = 0 →
      ∀ z : ℂ, ‖z‖ ≤ τ⁻¹ → 0 < z.im → z.re ∈ Set.Icc (Eminus Λ) (Eplus Λ) →
        C⁻¹ * (mSol Λ z).im ≤ ‖1 - ntr (MSol Λ z ^ 2)‖ ∧
          ‖1 - ntr (MSol Λ z ^ 2)‖ ≤ C * ((mSol Λ z).im + avgSq Λ) ∧
          C⁻¹ * (mSol Λ z).im ≤ ‖1 - mSol Λ z ^ 2‖ ∧
          ‖1 - mSol Λ z ^ 2‖ ≤ C * ((mSol Λ z).im + avgSq Λ) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := square_root_density τ hτ
  obtain ⟨CA, hCA0, hCA⟩ := estimate_replace_M_by_m τ hτ 2
  have hτ0 : 0 < τ⁻¹ := inv_pos.2 hτ
  set R : ℝ := τ⁻¹ + 1 with hRdef
  have hR0 : 0 < R + 1 / 10 := by linarith
  set c₀ : ℝ := min (3 / 4) (4 / 5 / (R + 1 / 10) ^ 4) with hc₀
  have hc₀0 : 0 < c₀ := by
    apply lt_min (by norm_num); positivity
  refine ⟨1 / c₀ + C₁ ^ 2 + 2 * CA + 3, by positivity, ?_⟩
  intro ι _ _ _ Λ hΛ hℓ htr z hzn hz hre
  set C : ℝ := 1 / c₀ + C₁ ^ 2 + 2 * CA + 3 with hCdef
  have hCpos : 0 < C := by positivity
  have hCinv : C⁻¹ ≤ c₀ := by
    rw [inv_le_comm₀ hCpos hc₀0]
    have : 1 / c₀ ≤ C := by rw [hCdef]; nlinarith [sq_nonneg C₁]
    simpa [one_div] using this
  have hCinv2 : C⁻¹ ≤ 2 := by
    have : 1 ≤ C := by
      rw [hCdef]; have : 0 < 1 / c₀ := by positivity
      nlinarith [sq_nonneg C₁]
    calc C⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
      _ ≤ 2 := by norm_num
  obtain ⟨hw, hm1, hm, -⟩ := Tay_facts hΛ hℓ hz
  set m := mSol Λ z with hmdef
  set y := m.im with hy
  have hy0 : 0 ≤ y := hm.le
  have hym : y ≤ 1 := by
    have := Complex.abs_im_le_norm m
    linarith [le_abs_self m.im]
  have hav := Tay_avgSq_nonneg hΛ
  -- the lower bounds
  have hwR : ‖z + m‖ ≤ R := by
    have := norm_add_le z m
    rw [hRdef]; linarith
  have L1 : c₀ * y ≤ ‖1 - ntr (MSol Λ z ^ 2)‖ := Tay_A12_lower hΛ hℓ hz R hwR
  have L1' : C⁻¹ * y ≤ ‖1 - ntr (MSol Λ z ^ 2)‖ :=
    (mul_le_mul_of_nonneg_right hCinv hy0).trans L1
  have L3 : C⁻¹ * y ≤ ‖1 - m ^ 2‖ :=
    (mul_le_mul_of_nonneg_right hCinv2 hy0).trans (Tay_one_sub_sq_ge m)
  -- the upper bound for `1 - m²`
  obtain ⟨-, hdens⟩ := hC₁ ι Λ hΛ hℓ
  have hsq := (hdens z hzn hz).1 hre
  have hκ : 0 ≤ kappa Λ z.re := le_min (abs_nonneg _) (abs_nonneg _)
  have hy1 : C₁⁻¹ * Real.sqrt (kappa Λ z.re + z.im) ≤ y := hsq.1
  have hsqrt : Real.sqrt (kappa Λ z.re + z.im) ≤ C₁ * y := by
    have := mul_le_mul_of_nonneg_left hy1 hC₁0.le
    rwa [← mul_assoc, mul_inv_cancel₀ hC₁0.ne', one_mul] at this
  have hηle : z.im ≤ C₁ ^ 2 * y ^ 2 := by
    have h1 : (Real.sqrt (kappa Λ z.re + z.im)) ^ 2 ≤ (C₁ * y) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
    rw [Real.sq_sqrt (by linarith)] at h1
    nlinarith
  have hEq := (equation_z_im_m Λ hΛ z hz).1
  have hA6 := hCA ι Λ hΛ hℓ htr z hzn hz 1 1 (by norm_num) (by norm_num)
  rw [pow_one, pow_one, pow_one, pow_one, hEq] at hA6
  have hmm : m * star m = ((‖m‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hmm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hA6
  have hA6' := (abs_le.1 hA6).2
  have hyη : 0 < y + z.im := by linarith
  have hfrac : z.im / (y + z.im) ≤ C₁ ^ 2 * y := by
    rw [div_le_iff₀ hyη]
    nlinarith [sq_nonneg C₁, mul_nonneg (sq_nonneg C₁) hy0, hz]
  have hone : 1 - ‖m‖ ^ 2 ≤ C₁ ^ 2 * y + CA * avgSq Λ := by
    have : y / (y + z.im) = 1 - z.im / (y + z.im) := by field_simp; ring
    linarith
  have U4 : ‖1 - m ^ 2‖ ≤ (C₁ ^ 2 + 2) * y + CA * avgSq Λ := by
    have := Tay_one_sub_sq_le m hm1.le hy0
    linarith
  -- the comparison `⟨M²⟩` vs `m²`
  have hA6b := hCA ι Λ hΛ hℓ htr z hzn hz 2 0 (by norm_num) (by norm_num)
  rw [pow_zero, pow_zero, mul_one, mul_one] at hA6b
  have U2 : ‖1 - ntr (MSol Λ z ^ 2)‖ ≤ (C₁ ^ 2 + 2) * y + 2 * (CA * avgSq Λ) := by
    calc ‖1 - ntr (MSol Λ z ^ 2)‖ = ‖(1 - m ^ 2) + (m ^ 2 - ntr (MSol Λ z ^ 2))‖ := by
          congr 1; ring
      _ ≤ ‖1 - m ^ 2‖ + ‖m ^ 2 - ntr (MSol Λ z ^ 2)‖ := norm_add_le _ _
      _ ≤ _ := by
          rw [norm_sub_rev (m ^ 2)] at *
          linarith
  refine ⟨L1', ?_, L3, ?_⟩
  · calc _ ≤ (C₁ ^ 2 + 2) * y + 2 * (CA * avgSq Λ) := U2
      _ ≤ C * (y + avgSq Λ) := by
        rw [hCdef]
        have h1 : 0 < 1 / c₀ := by positivity
        nlinarith [mul_nonneg h1.le hy0, mul_nonneg h1.le hav, mul_nonneg hCA0.le hav,
          mul_nonneg (sq_nonneg C₁) hav, mul_nonneg hCA0.le hy0]
  · calc _ ≤ (C₁ ^ 2 + 2) * y + CA * avgSq Λ := U4
      _ ≤ C * (y + avgSq Λ) := by
        rw [hCdef]
        have h1 : 0 < 1 / c₀ := by positivity
        nlinarith [mul_nonneg h1.le hy0, mul_nonneg h1.le hav, mul_nonneg hCA0.le hav,
          mul_nonneg (sq_nonneg C₁) hav, mul_nonneg hCA0.le hy0]

section Examples

end Examples

end RBMTransitionEdge

end
