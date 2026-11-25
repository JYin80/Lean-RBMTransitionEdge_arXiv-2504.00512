module

public import RBMTransitionEdge.Edge.CountFlow
public import RBMTransitionEdge.Edge.SpecSum
public import RBMTransitionEdge.LocalLaw.Wigner

@[expose] public section

/-!
# The local-law bounds of Lemma 4.3 and the form of `ℱ₂`

Bounds (4.12) [single_resolvent_local_law_bound], (4.13) [single_resolvent_local_law_bound2] on
the entries of `G` and `Im G` at the edge, the rough bound (4.8) [rough_estimate_A_t] on the edge
count, the integrand of `ℱ₂` in block traces after the subtraction of `M`, and (4.16)
[eq:roughXY] (proof of Lemma 4.3 [rescomY]).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

/-! ### The Cauchy–Schwarz bound (4.16) [eq:roughXY] without `F''` -/

section XTerm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Cauchy–Schwarz for the trace of a product: `|tr(AB)| ≤ ‖A‖_{HS} ‖B‖_{HS}`. -/
private lemma CBnd_trace_mul_le (A B : Matrix ι ι ℂ) :
    ‖(A * B).trace‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) * Real.sqrt (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  have h1 : (A * B).trace = ∑ p : ι × ι, A p.1 p.2 * B p.2 p.1 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  have h2 : ∑ i, ∑ j, ‖A i j‖ ^ 2 = ∑ p : ι × ι, ‖A p.1 p.2‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  have h3 : ∑ i, ∑ j, ‖B i j‖ ^ 2 = ∑ p : ι × ι, ‖B p.2 p.1‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [h1, h2, h3]
  calc ‖∑ p : ι × ι, A p.1 p.2 * B p.2 p.1‖ ≤ ∑ p : ι × ι, ‖A p.1 p.2‖ * ‖B p.2 p.1‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => norm_mul _ _))
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- Right multiplication by a diagonal contraction does not increase the Hilbert–Schmidt norm. -/
private lemma CBnd_fro_mul_diag (A : Matrix ι ι ℂ) (b : ι → ℂ) (hb : ∀ j, ‖b j‖ ≤ 1) :
    ∑ i, ∑ j, ‖(A * Matrix.diagonal b) i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.mul_diagonal, norm_mul, mul_pow]
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) (hb j))

/-- The spectral form of `Im G` for Hermitian `X` and `Im z > 0`. -/
private lemma CBnd_imRes_eq (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    imRes X z = (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun k => ((z.im / ‖(hX.eigenvalues k : ℂ) - z‖ ^ 2 : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix ι ι ℂ) := by
  ext i j
  have h := imRes_eq_sum_eig X hX z hz i j
  change ((2 * Complex.I)⁻¹ • (res X z - (res X z)ᴴ)) i j = _
  rw [h, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply]
  simp only [Complex.star_def]
  ring

/-- The sum of the squared entries of `Im G` is at most `tr(Im G)/Im z`, and `tr(Im G) =
Im tr G` (the second-moment bound `⟨(Im G)²⟩ ≤ ⟨Im G⟩ / Im z` of (4.16) [eq:roughXY]). -/
private lemma CBnd_fro_imRes (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) :
    ∑ i, ∑ j, ‖imRes X z i j‖ ^ 2 ≤ (Matrix.trace (res X z)).im / z.im := by
  set U : Matrix ι ι ℂ := (hX.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : star U * U = 1 := by
    have := (Matrix.UnitaryGroup.star_mul_self hX.eigenvectorUnitary)
    simp [hU]
  set p : ι → ℝ := fun k => z.im / ‖(hX.eigenvalues k : ℂ) - z‖ ^ 2 with hp
  have hnorm : ∀ k, z.im ^ 2 ≤ ‖(hX.eigenvalues k : ℂ) - z‖ ^ 2 := by
    intro k
    have h1 : z.im ≤ ‖(hX.eigenvalues k : ℂ) - z‖ := by
      calc z.im = |((hX.eigenvalues k : ℂ) - z).im| := by simp [abs_of_pos hz]
        _ ≤ _ := Complex.abs_im_le_norm _
    exact pow_le_pow_left₀ hz.le h1 2
  have hp0 : ∀ k, 0 ≤ p k := fun k => by positivity
  have hp1 : ∀ k, p k ≤ z.im⁻¹ := by
    intro k
    have hk : 0 < ‖(hX.eigenvalues k : ℂ) - z‖ ^ 2 := lt_of_lt_of_le (by positivity) (hnorm k)
    rw [hp, div_le_iff₀ hk]
    have := hnorm k
    have h2 : z.im * z.im⁻¹ = 1 := mul_inv_cancel₀ hz.ne'
    nlinarith [hz]
  have hP : imRes X z = U * Matrix.diagonal (fun k => ((p k : ℝ) : ℂ)) * star U :=
    CBnd_imRes_eq X hX z hz
  -- `Σ_{ij} |P_{ij}|² = Σ_k p_k²`
  have hsq : ((∑ i, ∑ j, ‖imRes X z i j‖ ^ 2 : ℝ) : ℂ) = ((∑ k, p k ^ 2 : ℝ) : ℂ) := by
    have h1 : ((∑ i, ∑ j, ‖imRes X z i j‖ ^ 2 : ℝ) : ℂ) =
        (imRes X z * (imRes X z)ᴴ).trace := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.star_def, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.mul_conj']
      push_cast
      rfl
    rw [h1]
    have hH : (imRes X z)ᴴ = imRes X z := by
      rw [hP, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      have : (star fun k => ((p k : ℝ) : ℂ)) = fun k => ((p k : ℝ) : ℂ) := by
        funext k; simp
      rw [this, Matrix.mul_assoc]
    rw [hH, hP]
    have e : U * Matrix.diagonal (fun k => ((p k : ℝ) : ℂ)) * star U *
        (U * Matrix.diagonal (fun k => ((p k : ℝ) : ℂ)) * star U) =
        U * (Matrix.diagonal (fun k => ((p k : ℝ) : ℂ)) *
          (star U * U) * Matrix.diagonal (fun k => ((p k : ℝ) : ℂ))) * star U := by
      simp only [Matrix.mul_assoc]
    rw [e, hUU, Matrix.mul_one, Matrix.diagonal_mul_diagonal, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.trace_diagonal]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- `Im tr G = Σ_k p_k`
  have hsum : (((Matrix.trace (res X z)).im : ℝ) : ℂ) = ((∑ k, p k : ℝ) : ℂ) := by
    have h1 : (((Matrix.trace (res X z)).im : ℝ) : ℂ) = (imRes X z).trace := by
      unfold imRes
      rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose, Complex.star_def,
        Complex.sub_conj]
      simp only [smul_eq_mul]
      push_cast
      field_simp
    rw [h1, hP, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU,
      Matrix.one_mul, Matrix.trace_diagonal]
    push_cast
    rfl
  have hsq' : ∑ i, ∑ j, ‖imRes X z i j‖ ^ 2 = ∑ k, p k ^ 2 := by exact_mod_cast hsq
  have hsum' : (Matrix.trace (res X z)).im = ∑ k, p k := by exact_mod_cast hsum
  rw [hsq', hsum', le_div_iff₀ hz, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 : p k * z.im ≤ 1 := by
    have := mul_le_mul_of_nonneg_right (hp1 k) hz.le
    rwa [inv_mul_cancel₀ hz.ne'] at this
  calc p k ^ 2 * z.im = p k * (p k * z.im) := by ring
    _ ≤ p k * 1 := mul_le_mul_of_nonneg_left h1 (hp0 k)
    _ = p k := mul_one _

end XTerm

/-! ### Deterministic inputs of the local-law bounds -/

section Local

/-- `c ≤ N^a` for all large `N`, when `a > 0`. -/
private lemma CBnd_ev (c a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c ≤ (N : ℝ) ^ a := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop c)

/-- (A.1) [square_root_density] at `τ = 1/4`, in the form used for (4.8) and (4.12): for `|z| ≤ 4`,
`Im z > 0` and `|Re z - E⁺| ≤ w`, `Im z ≤ w` one has `Im m(z) ≤ C √w`. -/
private lemma CBnd_imm : ∃ Cm : ℝ, 0 < Cm ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ), Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → ∀ z : ℂ, ‖z‖ ≤ 4 → 0 < z.im →
    ∀ w : ℝ, |z.re - Eplus Λ| ≤ w → z.im ≤ w → (mExt Λ z).im ≤ Cm * Real.sqrt w := by
  obtain ⟨C, hC, H⟩ := square_root_density (1 / 4) (by norm_num)
  refine ⟨C * Real.sqrt 2, by positivity, ?_⟩
  intro ι _ _ _ Λ hΛ hℓ z hz hzi w hw hη
  obtain ⟨-, H2⟩ := H ι Λ hΛ hℓ
  have hz' : ‖z‖ ≤ (1 / 4 : ℝ)⁻¹ := by norm_num; exact hz
  obtain ⟨Hin, Hout⟩ := H2 z hz' hzi
  have hmE : mExt Λ z = mSol Λ z := by simp [mExt, hzi]
  rw [hmE]
  have hk : kappa Λ z.re ≤ w := (min_le_left _ _).trans (by rw [abs_sub_comm]; exact hw)
  have hk0 : 0 ≤ kappa Λ z.re := le_min (abs_nonneg _) (abs_nonneg _)
  have hw0 : 0 ≤ w := hzi.le.trans hη
  have key : (mSol Λ z).im ≤ C * Real.sqrt (2 * w) := by
    by_cases hmem : z.re ∈ Set.Icc (Eminus Λ) (Eplus Λ)
    · refine (Hin hmem).2.trans ?_
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hC.le
    · refine (Hout hmem).2.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hC.le
      calc z.im / Real.sqrt (kappa Λ z.re + z.im) ≤ z.im / Real.sqrt z.im := by
            apply div_le_div_of_nonneg_left hzi.le (Real.sqrt_pos.2 hzi)
            exact Real.sqrt_le_sqrt (by linarith)
        _ = Real.sqrt z.im := by
            rw [div_eq_iff (Real.sqrt_pos.2 hzi).ne']
            exact (Real.mul_self_sqrt hzi.le).symm
        _ ≤ Real.sqrt (2 * w) := Real.sqrt_le_sqrt (by linarith)
  calc (mSol Λ z).im ≤ C * Real.sqrt (2 * w) := key
    _ = C * Real.sqrt 2 * Real.sqrt w := by rw [Real.sqrt_mul (by norm_num)]; ring

/-- The parameters of `z = E + iη`, `η = N^{-2/3-σ}`: with `w = N^{-2/3+σ}` and `s = N^{-1/3+σ}`,
`η ≤ w ≤ s² `, `s ≤ 1`, `1/(Nη) = s`, `w ≤ 1/2` and `N^{-3/4} ≤ η` (`σ ≤ 1/12`). -/
private lemma CBnd_param (x σ : ℝ) (hx : 4 ≤ x) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 12) :
    0 < x ^ (-(2 / 3 : ℝ) - σ) ∧ x ^ (-(2 / 3 : ℝ) - σ) ≤ x ^ (-(2 / 3 : ℝ) + σ) ∧
    x ^ (-(2 / 3 : ℝ) + σ) ≤ (x ^ (-(1 / 3 : ℝ) + σ)) ^ 2 ∧ x ^ (-(1 / 3 : ℝ) + σ) ≤ 1 ∧
    (x * x ^ (-(2 / 3 : ℝ) - σ))⁻¹ = x ^ (-(1 / 3 : ℝ) + σ) ∧
    x ^ (-(2 / 3 : ℝ) + σ) ≤ 1 / 2 ∧ x ^ (-1 + 1 / 4 : ℝ) ≤ x ^ (-(2 / 3 : ℝ) - σ) ∧
    x * x ^ (-(2 / 3 : ℝ) + σ) * x ^ (-(1 / 3 : ℝ) + σ) = x ^ (2 * σ) := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  refine ⟨Real.rpow_pos_of_pos hx0 _, Real.rpow_le_rpow_of_exponent_le hx1 (by linarith), ?_,
    Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith), ?_, ?_,
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith), ?_⟩
  · rw [sq, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  · rw [← Real.rpow_one_add' hx0.le (by linarith)]
    rw [← Real.rpow_neg hx0.le]
    congr 1; ring
  · have h1 : x ^ (-(2 / 3 : ℝ) + σ) ≤ x ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : x ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
      have : (2 : ℝ) ≤ Real.sqrt x := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hx
      rw [one_div]
      exact inv_anti₀ (by norm_num) this
    exact h1.trans h2
  · rw [← Real.rpow_one_add' hx0.le (by linarith), ← Real.rpow_add hx0]
    congr 1; ring

/-- `M(z) = (Λ - z - m(z))⁻¹` is the solution `MSol` for `Im z > 0`. -/
private lemma CBnd_MExt_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : 0 < z.im) : MExt Λ z = MSol Λ z := by
  have h : mExt Λ z = mSol Λ z := by simp [mExt, hz]
  unfold MExt MSol
  rw [h]

/-- `‖A*‖ = ‖A‖` for the operator norm. -/
private lemma CBnd_opNorm_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star]
  exact norm_star (Matrix.toEuclideanCLM (𝕜 := ℂ) A)

/-- `‖M(z)‖ ≤ 5/4` for `‖Λ‖ ≤ 1/10`, `Im z > 0` (`mSol_apriori`). -/
private lemma CBnd_M_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) :
    opNorm (MExt Λ z) ≤ 5 / 4 := by
  rw [CBnd_MExt_eq Λ z hz]
  have h := (mSol_apriori Λ hΛ hℓ z hz).2.2
  have h2 : (1 - 2 * opNorm Λ)⁻¹ ≤ 5 / 4 := by
    have h3 : (4 / 5 : ℝ) ≤ 1 - 2 * opNorm Λ := by linarith
    calc (1 - 2 * opNorm Λ)⁻¹ ≤ (4 / 5 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h3
      _ = 5 / 4 := by norm_num
  linarith

/-- The entries of `Im M(z) = (M - M*)/(2i)` are at most `(25/16)(η + Im m)`: the deterministic
part of (4.12) [single_resolvent_local_law_bound] (through `MExt_imPart_eq`, not `mSol_apriori`
alone). -/
private lemma CBnd_imM_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (a b : ι) :
    ‖((2 * Complex.I)⁻¹ • (MExt Λ z - (MExt Λ z)ᴴ)) a b‖ ≤ 25 / 16 * (z.im + (mExt Λ z).im) := by
  have hM := CBnd_M_le Λ hΛ hℓ z hz
  have hm : 0 < (mExt Λ z).im := by
    have : mExt Λ z = mSol Λ z := by simp [mExt, hz]
    rw [this]; exact (mSol_spec Λ hΛ z hz).1
  rw [MExt_imPart_eq Λ hΛ z hz, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.add_im]
  have h1 : ‖(MExt Λ z * (MExt Λ z)ᴴ) a b‖ ≤ 25 / 16 := by
    calc _ ≤ opNorm (MExt Λ z * (MExt Λ z)ᴴ) := norm_apply_le_opNorm _ a b
      _ ≤ opNorm (MExt Λ z) * opNorm (MExt Λ z)ᴴ := opNorm_mul_le _ _
      _ = opNorm (MExt Λ z) * opNorm (MExt Λ z) := by rw [CBnd_opNorm_conj]
      _ ≤ 5 / 4 * (5 / 4) := mul_le_mul hM hM (norm_nonneg _) (by norm_num)
      _ = 25 / 16 := by norm_num
  rw [abs_of_nonneg (by linarith)]
  calc (z.im + (mExt Λ z).im) * ‖(MExt Λ z * (MExt Λ z)ᴴ) a b‖
      ≤ (z.im + (mExt Λ z).im) * (25 / 16) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = _ := by ring

/-- `|G_{ab}| ≤ 5/4 + ε` when `|(G - M)_{ab}| ≤ ε`. -/
private lemma CBnd_res_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ X : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (z : ℂ) (hz : 0 < z.im) (a b : ι) (ε : ℝ)
    (h1 : ‖(res X z - MExt Λ z) a b‖ ≤ ε) : ‖res X z a b‖ ≤ 5 / 4 + ε := by
  have hM := (norm_apply_le_opNorm (MExt Λ z) a b).trans (CBnd_M_le Λ hΛ hℓ z hz)
  have e : res X z a b = (res X z - MExt Λ z) a b + MExt Λ z a b := by
    simp
  rw [e]
  calc _ ≤ ‖(res X z - MExt Λ z) a b‖ + ‖MExt Λ z a b‖ := norm_add_le _ _
    _ ≤ ε + 5 / 4 := add_le_add h1 hM
    _ = _ := by ring

/-- `|(Im G)_{ab}| ≤ (25/16)(η + Im m) + ε` for Hermitian `X` when the entries of `G - M` at `z` and
`z̄` are at most `ε`: `(Im G)_{ab} = (Im M)_{ab} + ½[(G - M)(z) - (G - M)(z̄)]_{ab}`. -/
private lemma CBnd_imRes_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ X : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (hX : X.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (a b : ι) (ε : ℝ)
    (h1 : ‖(res X z - MExt Λ z) a b‖ ≤ ε)
    (h2 : ‖(res X (star z) - MExt Λ (star z)) a b‖ ≤ ε) :
    ‖imRes X z a b‖ ≤ 25 / 16 * (z.im + (mExt Λ z).im) + ε := by
  have hc : res X (star z) = (res X z)ᴴ := res_conj X hX z hz
  have hMc : MExt Λ (star z) = (MExt Λ z)ᴴ := (mExt_conj Λ hΛ z hz.ne').2
  have e : imRes X z a b = ((2 * Complex.I)⁻¹ • (MExt Λ z - (MExt Λ z)ᴴ)) a b +
      (2 * Complex.I)⁻¹ * ((res X z - MExt Λ z) a b - (res X (star z) - MExt Λ (star z)) a b) := by
    rw [hc, hMc]
    unfold imRes
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  rw [e]
  have h3 : ‖(2 * Complex.I)⁻¹ *
      ((res X z - MExt Λ z) a b - (res X (star z) - MExt Λ (star z)) a b)‖ ≤ ε := by
    rw [norm_mul, norm_inv, norm_mul, Complex.norm_I]
    have h2' : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2']
    have := norm_sub_le ((res X z - MExt Λ z) a b) ((res X (star z) - MExt Λ (star z)) a b)
    calc ((2 : ℝ) * 1)⁻¹ * ‖(res X z - MExt Λ z) a b - (res X (star z) - MExt Λ (star z)) a b‖
        ≤ ((2 : ℝ) * 1)⁻¹ * (ε + ε) := by
          refine mul_le_mul_of_nonneg_left (this.trans (by linarith)) (by norm_num)
      _ = ε := by ring
  exact (norm_add_le _ _).trans (add_le_add (CBnd_imM_le Λ hΛ hℓ z hz a b) h3)

/-- `psiIso` at `z̄` equals `psiIso` at `z` for `Im z ≠ 0`. -/
private lemma CBnd_psi_conj {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (N : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    psiIso Λ N (star z) = psiIso Λ N z := by
  unfold psiIso
  rw [(mExt_conj Λ hΛ z hz).1]
  simp

/-- The control parameter at `z = E + iη`, `η = N^{-2/3-σ}`: with `Im m ≤ C_m s`, `s = N^{-1/3+σ}`
and `1/(Nη) = s`, `ψ ≤ (√C_m + 1) s`. -/
private lemma CBnd_psi_le {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (N : ℕ)
    (z : ℂ) (Cm s : ℝ) (hCm : 0 ≤ Cm) (hs : 0 < s) (hz : 0 < z.im)
    (hN : (1 : ℝ) / ((N : ℝ) * |z.im|) = s) (him : 0 ≤ (mExt Λ z).im)
    (hm : (mExt Λ z).im ≤ Cm * s) :
    psiIso Λ N z ≤ (Real.sqrt Cm + 1) * s := by
  unfold psiIso
  rw [hN, abs_of_nonneg him, abs_of_pos hz]
  have e : (mExt Λ z).im / ((N : ℝ) * z.im) = (mExt Λ z).im * s := by
    rw [abs_of_pos hz] at hN
    rw [← hN]; ring
  rw [e]
  have h1 : Real.sqrt ((mExt Λ z).im * s) ≤ Real.sqrt Cm * s := by
    calc Real.sqrt ((mExt Λ z).im * s) ≤ Real.sqrt (Cm * s * s) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hm hs.le)
      _ = Real.sqrt Cm * s := by
          rw [mul_assoc, ← sq, Real.sqrt_mul hCm, Real.sqrt_sq hs.le]
  linarith

/-- The coupling `Λ = lam D N A` is small and `E⁺` is close to `2` for large `N`
(`opNorm_lam_le`, (A.2) [edge_close_to_edge_sc]): `‖Λ‖ ≤ 1/10` and `|E⁺| ≤ 3`. -/
private lemma CBnd_small (D N : ℕ) [Nonempty (Idx D N)] (A : Matrix (Fin N) (Fin N) ℂ)
    (δA Ce : ℝ) (hCe : 0 < Ce) (hA : opNorm A ≤ (N : ℝ) ^ (-δA))
    (hN : 20 + 2 * Ce ≤ (N : ℝ) ^ δA)
    (HCe : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → |2 - Eplus Λ| + |2 + Eminus Λ| ≤ Ce * opNorm Λ) :
    opNorm (lam D N A) ≤ 1 / 10 ∧ |Eplus (lam D N A)| ≤ 3 := by
  have hpos : (0 : ℝ) < 20 + 2 * Ce := by linarith
  have hx0 : (0 : ℝ) < (N : ℝ) ^ δA := lt_of_lt_of_le hpos hN
  have h1 : (20 + 2 * Ce) * (N : ℝ) ^ (-δA) ≤ 1 := by
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    calc (20 + 2 * Ce) * ((N : ℝ) ^ δA)⁻¹ ≤ (N : ℝ) ^ δA * ((N : ℝ) ^ δA)⁻¹ :=
          mul_le_mul_of_nonneg_right hN (inv_nonneg.mpr hx0.le)
      _ = 1 := mul_inv_cancel₀ hx0.ne'
  have hn0 : 0 ≤ (N : ℝ) ^ (-δA) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : opNorm (lam D N A) ≤ 2 * (N : ℝ) ^ (-δA) := (opNorm_lam_le D N A).trans (by linarith)
  have hℓ : opNorm (lam D N A) ≤ 1 / 10 := by nlinarith
  refine ⟨hℓ, ?_⟩
  have hop0 : 0 ≤ opNorm (lam D N A) := norm_nonneg _
  have h3 : Ce * opNorm (lam D N A) ≤ 1 := by nlinarith
  have h4 := HCe (Idx D N) (lam D N A) (lam_isHermitian D N A) hℓ
  have h5 : |2 - Eplus (lam D N A)| ≤ 1 := by
    have := abs_nonneg (2 + Eminus (lam D N A))
    linarith
  have h6 := abs_le.1 h5
  rw [abs_le]
  constructor <;> linarith [h6.1, h6.2]

end Local

set_option maxHeartbeats 1000000 in
/-- (4.12) [single_resolvent_local_law_bound] and (4.13) [single_resolvent_local_law_bound2]
for the entries themselves: outside probability `N^{-D'}`, uniformly in `t ≥ 0` and in `E` within
`N^{-2/3+σ}` of `E⁺`, every entry of `G_t(E + iη)`, `η = N^{-2/3-σ}`, is at most `2` and every
entry of `Im G_t(E + iη)` is at most `K N^{-1/3+σ+τ'}`. -/
theorem edgeRes_entry_le (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ : ℝ, 0 < σ → σ < 1 / 12 → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
        ouMatLaw D N L t {h | ∃ E : ℝ, |E - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ∧
          ∃ a b : Idx D N,
            2 < ‖res (Matrix.of h + lam D N A)
              ((E : ℂ) + (((N : ℝ) ^ (-(2 / 3 : ℝ) - σ) : ℝ) : ℂ) * Complex.I) a b‖ ∨
            K * (N : ℝ) ^ (-(1 / 3 : ℝ) + σ + τ') < ‖imRes (Matrix.of h + lam D N A)
              ((E : ℂ) + (((N : ℝ) ^ (-(2 / 3 : ℝ) - σ) : ℝ) : ℂ) * Complex.I) a b‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨Cm, hCm, HCm⟩ := CBnd_imm
  obtain ⟨Ce, hCe, HCe⟩ := edge_close_to_edge_sc
  refine ⟨25 / 16 * (1 + Cm) + Real.sqrt Cm + 1, by positivity, ?_⟩
  intro σ hσ0 hσ1 τ' hτ' D' hD'
  set τ'' : ℝ := min τ' (1 / 8) with hτ''
  have hτ''0 : 0 < τ'' := lt_min hτ' (by norm_num)
  have hτ''1 : τ'' ≤ τ' := min_le_left _ _
  have hτ''2 : τ'' ≤ 1 / 8 := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := samefort_local D (by omega) δA (1 / 4) hδA (by norm_num) C τ'' hτ''0
    (D' + 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := CBnd_ev (20 + 2 * Ce) δA hδA
  obtain ⟨N₃, hN₃⟩ := CBnd_ev (2 * (Real.sqrt Cm + 1)) (1 / 8) (by norm_num)
  refine ⟨max (max (max N₁ N₂) (max N₃ 4)) (D ^ 2), ?_⟩
  intro N hN L t ht A hA
  have hNa : N₁ ≤ N := by
    refine le_trans ?_ hN
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hNb : N₂ ≤ N := by
    refine le_trans ?_ hN
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hNc : N₃ ≤ N := by
    refine le_trans ?_ hN
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hN4 : 4 ≤ N := by
    refine le_trans ?_ hN
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hND : D ^ 2 ≤ N := le_trans (le_max_right _ _) hN
  have hx : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hx0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  obtain ⟨hsA, -, -⟩ := hN₁ N hNa L t ht A hA
  -- the parameters
  set Λ := lam D N A with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N A
  obtain ⟨hℓ, hE3⟩ := CBnd_small D N A δA Ce hCe hA (hN₂ N hNb) HCe
  have hq := hN₃ N hNc
  set x : ℝ := (N : ℝ) with hxdef
  obtain ⟨hη0, hηw, hws, hs1, hNη, hw12, hspec, -⟩ := CBnd_param x σ hx hσ0 hσ1.le
  set η : ℝ := x ^ (-(2 / 3 : ℝ) - σ) with hη
  set w : ℝ := x ^ (-(2 / 3 : ℝ) + σ) with hw
  set s : ℝ := x ^ (-(1 / 3 : ℝ) + σ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  have hw0 : 0 < w := Real.rpow_pos_of_pos hx0 _
  have hsw : Real.sqrt w ≤ s := by
    calc Real.sqrt w ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt hws
      _ = s := Real.sqrt_sq hs0.le
  have hηs : η ≤ s := by nlinarith
  have hτ1 : (1 : ℝ) ≤ x ^ τ' := Real.one_le_rpow hx1 hτ'.le
  have hτ''x : x ^ τ'' ≤ x ^ τ' := Real.rpow_le_rpow_of_exponent_le hx1 hτ''1
  have hτs : x ^ (-(1 / 3 : ℝ) + σ + τ') = s * x ^ τ' := by
    rw [Real.rpow_add hx0]
  -- `x^{τ''} s x^{1/8} ≤ 1`
  have hεq : x ^ τ'' * s * x ^ (1 / 8 : ℝ) ≤ 1 := by
    rw [hs, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  -- the exceptional events, one for every pair of indices
  set Spq : Idx D N × Idx D N → Set (Idx D N → Idx D N → ℂ) := fun p =>
    {h | ∃ z ∈ specDom (1 / 4) N, x ^ τ'' * psiIso Λ N z <
      ‖star (Pi.single p.1 (1 : ℂ) : Idx D N → ℂ) ⬝ᵥ
        ((res (Matrix.of h + Λ) z - MExt Λ z) *ᵥ (Pi.single p.2 (1 : ℂ) : Idx D N → ℂ))‖}
    with hSpq
  have hprob : ∀ p : Idx D N × Idx D N,
      ouMatLaw D N L t (Spq p) ≤ ENNReal.ofReal (x ^ (-(D' + 3))) := by
    intro p
    refine hsA (Pi.single p.1 1) (Pi.single p.2 1) ?_ ?_
    · rw [Finset.sum_eq_single p.1]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · rw [Finset.sum_eq_single p.2]
      · simp
      · intro b _ hb; simp [hb]
      · simp
  -- the pointwise bounds off the exceptional events
  have hdet : ∀ h : Idx D N → Idx D N → ℂ, (Matrix.of h).IsHermitian → (∀ p, h ∉ Spq p) →
      ∀ E : ℝ, |E - Eplus Λ| ≤ w → ∀ a b : Idx D N,
        ‖res (Matrix.of h + Λ) ((E : ℂ) + (η : ℂ) * Complex.I) a b‖ ≤ 2 ∧
        ‖imRes (Matrix.of h + Λ) ((E : ℂ) + (η : ℂ) * Complex.I) a b‖ ≤
          (25 / 16 * (1 + Cm) + Real.sqrt Cm + 1) * x ^ (-(1 / 3 : ℝ) + σ + τ') := by
    intro h hh hno E hE a b
    have hX : (Matrix.of h + Λ).IsHermitian := hh.add hΛ
    set z : ℂ := (E : ℂ) + (η : ℂ) * Complex.I with hz
    have hzim : z.im = η := by simp [hz]
    have hzre : z.re = E := by simp [hz]
    have hz0 : 0 < z.im := by rw [hzim]; exact hη0
    have hzn : ‖z‖ ≤ 4 := by
      have : ‖z‖ ≤ ‖(E : ℂ)‖ + ‖(η : ℂ) * Complex.I‖ := norm_add_le _ _
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hη0] at this
      have h7 := abs_le.1 hE
      have h8 := abs_le.1 hE3
      have h9 : |E| ≤ 3 + w := by
        rw [abs_le]; constructor <;> linarith [h7.1, h7.2, h8.1, h8.2]
      linarith
    have hzs : z ∈ specDom (1 / 4) N := by
      refine ⟨by norm_num; exact hzn, ?_⟩
      rw [hzim, abs_of_pos hη0]
      exact hspec
    have hzs' : star z ∈ specDom (1 / 4) N := by
      refine ⟨by rw [norm_star]; norm_num; exact hzn, ?_⟩
      have : (star z).im = -η := by simp [hz]
      rw [this, abs_neg, abs_of_pos hη0]
      exact hspec
    have e1 : ∀ M : Matrix (Idx D N) (Idx D N) ℂ,
        star (Pi.single a (1 : ℂ) : Idx D N → ℂ) ⬝ᵥ (M *ᵥ (Pi.single b (1 : ℂ) : Idx D N → ℂ)) =
          M a b := by
      intro M
      rw [Matrix.mulVec_single_one]
      simp
    have hno' : ∀ z' ∈ specDom (1 / 4) N,
        ‖(res (Matrix.of h + Λ) z' - MExt Λ z') a b‖ ≤ x ^ τ'' * psiIso Λ N z' := by
      intro z' hz'
      by_contra hlt
      rw [not_le] at hlt
      exact hno (a, b) ⟨z', hz', by rw [e1]; exact hlt⟩
    have hden : (1 : ℝ) / (x * |z.im|) = s := by
      rw [hzim, abs_of_pos hη0, one_div]; exact hNη
    have him : 0 ≤ (mExt Λ z).im := by
      have : mExt Λ z = mSol Λ z := by simp [mExt, hz0]
      rw [this]; exact (mSol_spec Λ hΛ z hz0).1.le
    have hm : (mExt Λ z).im ≤ Cm * s := by
      have := HCm (Idx D N) Λ hΛ hℓ z hzn hz0 w (by rw [hzre]; exact hE) (by rw [hzim]; exact hηw)
      exact this.trans (mul_le_mul_of_nonneg_left hsw hCm.le)
    have hψ : psiIso Λ N z ≤ (Real.sqrt Cm + 1) * s :=
      CBnd_psi_le Λ N z Cm s hCm.le hs0 hz0 hden him hm
    have hψ' : psiIso Λ N (star z) ≤ (Real.sqrt Cm + 1) * s := by
      rw [CBnd_psi_conj Λ hΛ N z hz0.ne']; exact hψ
    have hx0' : 0 ≤ x ^ τ'' := Real.rpow_nonneg hx0.le _
    have hG1 : ‖(res (Matrix.of h + Λ) z - MExt Λ z) a b‖ ≤ x ^ τ'' * ((Real.sqrt Cm + 1) * s) :=
      (hno' z hzs).trans (mul_le_mul_of_nonneg_left hψ hx0')
    have hG2 : ‖(res (Matrix.of h + Λ) (star z) - MExt Λ (star z)) a b‖ ≤
        x ^ τ'' * ((Real.sqrt Cm + 1) * s) :=
      (hno' (star z) hzs').trans (mul_le_mul_of_nonneg_left hψ' hx0')
    have hε1 : x ^ τ'' * ((Real.sqrt Cm + 1) * s) ≤ 3 / 4 := by
      have hsq0 : 0 ≤ Real.sqrt Cm + 1 := by positivity
      have h1 : 2 * (Real.sqrt Cm + 1) * (x ^ τ'' * s) ≤ x ^ (1 / 8 : ℝ) * (x ^ τ'' * s) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
      nlinarith
    refine ⟨?_, ?_⟩
    · have := CBnd_res_le Λ (Matrix.of h + Λ) hΛ hℓ z hz0 a b _ hG1
      linarith
    · have := CBnd_imRes_le Λ (Matrix.of h + Λ) hΛ hℓ hX z hz0 a b _ hG1 hG2
      rw [hzim] at this
      rw [hτs]
      have h1 : x ^ τ'' * ((Real.sqrt Cm + 1) * s) ≤ (Real.sqrt Cm + 1) * (s * x ^ τ') := by
        calc x ^ τ'' * ((Real.sqrt Cm + 1) * s) = (Real.sqrt Cm + 1) * (s * x ^ τ'') := by ring
          _ ≤ (Real.sqrt Cm + 1) * (s * x ^ τ') :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτ''x hs0.le) (by positivity)
      have h2 : 25 / 16 * (η + (mExt Λ z).im) ≤ 25 / 16 * (1 + Cm) * (s * x ^ τ') := by
        have h3 : η + (mExt Λ z).im ≤ (1 + Cm) * s :=
          calc η + (mExt Λ z).im ≤ s + Cm * s := add_le_add hηs hm
            _ = (1 + Cm) * s := by ring
        have h4 : (1 + Cm) * s ≤ (1 + Cm) * (s * x ^ τ') :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hs0.le hτ1) (by positivity)
        calc 25 / 16 * (η + (mExt Λ z).im) ≤ 25 / 16 * ((1 + Cm) * (s * x ^ τ')) :=
              mul_le_mul_of_nonneg_left (h3.trans h4) (by norm_num)
          _ = 25 / 16 * (1 + Cm) * (s * x ^ τ') := by ring
      have h5 : (25 / 16 * (1 + Cm) + Real.sqrt Cm + 1) * (s * x ^ τ') =
          25 / 16 * (1 + Cm) * (s * x ^ τ') + (Real.sqrt Cm + 1) * (s * x ^ τ') := by ring
      rw [h5]
      linarith
  -- the Hermitian event has probability one
  have hherm_ae : ouMatLaw D N L t {h | ¬ (Matrix.of h).IsHermitian} = 0 := by
    obtain ⟨C', hC'⟩ := llClass_ouLaw D C
    exact ae_iff.1 (hC' N L t ht).herm
  refine le_trans (measure_mono (t := {h | ¬ (Matrix.of h).IsHermitian} ∪ ⋃ p, Spq p) ?_) ?_
  · intro h hh
    by_cases hherm : (Matrix.of h).IsHermitian
    · right
      by_contra hno
      simp only [Set.mem_iUnion, not_exists] at hno
      obtain ⟨E, hE, a, b, hbad⟩ := hh
      obtain ⟨h1, h2⟩ := hdet h hherm hno E hE a b
      rcases hbad with hbad | hbad <;> linarith
    · left; exact hherm
  · calc ouMatLaw D N L t ({h | ¬ (Matrix.of h).IsHermitian} ∪ ⋃ p, Spq p)
        ≤ ouMatLaw D N L t {h | ¬ (Matrix.of h).IsHermitian} + ouMatLaw D N L t (⋃ p, Spq p) :=
          measure_union_le _ _
      _ ≤ 0 + ∑ p : Idx D N × Idx D N, ouMatLaw D N L t (Spq p) := by
          rw [hherm_ae]; exact add_le_add le_rfl (measure_iUnion_fintype_le _ _)
      _ ≤ 0 + ∑ p : Idx D N × Idx D N, ENNReal.ofReal (x ^ (-(D' + 3))) :=
          add_le_add le_rfl (Finset.sum_le_sum fun p _ => hprob p)
      _ = ENNReal.ofReal ((Fintype.card (Idx D N × Idx D N) : ℝ) * x ^ (-(D' + 3))) := by
          rw [zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (x ^ (-D')) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hcard : (Fintype.card (Idx D N × Idx D N) : ℝ) = ((D : ℝ) * x) * ((D : ℝ) * x) := by
            simp [Idx, hxdef]
          have hND' : (D : ℝ) ^ 2 ≤ x := by rw [hxdef]; exact_mod_cast hND
          have h3 : x ^ (-(D' + 3)) = x ^ (-D') * (x ^ 3)⁻¹ := by
            rw [show -(D' + 3) = -D' + -(3 : ℝ) by ring, Real.rpow_add hx0, Real.rpow_neg hx0.le]
            norm_cast
          have h4 : ((D : ℝ) * x) * ((D : ℝ) * x) ≤ x ^ 3 := by
            calc ((D : ℝ) * x) * ((D : ℝ) * x) = (D : ℝ) ^ 2 * x ^ 2 := by ring
              _ ≤ x * x ^ 2 := mul_le_mul_of_nonneg_right hND' (by positivity)
              _ = x ^ 3 := by ring
          have h5 : ((D : ℝ) * x) * ((D : ℝ) * x) * (x ^ 3)⁻¹ ≤ 1 := by
            rw [← div_eq_mul_inv]
            exact (div_le_one (by positivity)).2 h4
          rw [hcard, h3]
          have h6 : 0 ≤ x ^ (-D') := Real.rpow_nonneg hx0.le _
          calc ((D : ℝ) * x) * ((D : ℝ) * x) * (x ^ (-D') * (x ^ 3)⁻¹)
              = x ^ (-D') * (((D : ℝ) * x) * ((D : ℝ) * x) * (x ^ 3)⁻¹) := by ring
            _ ≤ x ^ (-D') * 1 := mul_le_mul_of_nonneg_left h5 h6
            _ = x ^ (-D') := mul_one _

set_option maxHeartbeats 1000000 in
/-- (4.8) [rough_estimate_A_t]: outside probability `N^{-D'}`, uniformly in `t ≥ 0` and in the
windows within `N^{-2/3+σ}` of `E⁺`, `|A_t| ≤ K N^{2σ+τ'}`, `η = N^{-2/3-σ}`. -/
theorem edgeCount_rough (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ : ℝ, 0 < σ → σ < 1 / 12 → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (L : EntryLaws C) (t : ℝ), 0 ≤ t →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
        ouMatLaw D N L t {h | ∃ E₁ E₂ : ℝ,
          |E₁ - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ∧
          |E₂ - Eplus (lam D N A)| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + σ) ∧
          K * (N : ℝ) ^ (2 * σ + τ') <
            |edgeCount D N A ((N : ℝ) ^ (-(2 / 3 : ℝ) - σ)) E₁ E₂ h|} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  obtain ⟨Cm, hCm, HCm⟩ := CBnd_imm
  obtain ⟨Ce, hCe, HCe⟩ := edge_close_to_edge_sc
  refine ⟨2 * D * (Cm + 1), by positivity, ?_⟩
  intro σ hσ0 hσ1 τ' hτ' D' hD'
  obtain ⟨N₁, hN₁⟩ := samefort_local D (by omega) δA (1 / 4) hδA (by norm_num) C τ' hτ' D' hD'
  obtain ⟨N₂, hN₂⟩ := CBnd_ev (20 + 2 * Ce) δA hδA
  refine ⟨max (max N₁ N₂) 4, ?_⟩
  intro N hN L t ht A hA
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN4 : 4 ≤ N := le_trans (le_max_right _ _) hN
  have hx : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hx0 : (0 : ℝ) < (N : ℝ) := by linarith
  have : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  obtain ⟨-, hB, -⟩ := hN₁ N hNa L t ht A hA
  have hB1 := hB 1 (by unfold opNorm; rw [map_one]; exact ContinuousLinearMap.norm_id_le)
  refine le_trans (measure_mono ?_) hB1
  intro h hh
  obtain ⟨E₁, E₂, hE₁, hE₂, hbig⟩ := hh
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hcon
  -- the parameters
  set Λ := lam D N A with hΛdef
  have hΛ : Λ.IsHermitian := lam_isHermitian D N A
  obtain ⟨hℓ, hE3⟩ := CBnd_small D N A δA Ce hCe hA (hN₂ N hNb) HCe
  set x : ℝ := (N : ℝ) with hxdef
  obtain ⟨hη0, hηw, hws, hs1, hNη, hw12, hspec, hmul⟩ := CBnd_param x σ hx hσ0 hσ1.le
  set η : ℝ := x ^ (-(2 / 3 : ℝ) - σ) with hη
  set w : ℝ := x ^ (-(2 / 3 : ℝ) + σ) with hw
  set s : ℝ := x ^ (-(1 / 3 : ℝ) + σ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  have hw0 : 0 < w := Real.rpow_pos_of_pos hx0 _
  have hsw : Real.sqrt w ≤ s := by
    calc Real.sqrt w ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt hws
      _ = s := Real.sqrt_sq hs0.le
  have hτ1 : (1 : ℝ) ≤ x ^ τ' := Real.one_le_rpow (by linarith) hτ'.le
  -- the integrand
  have hpt : ∀ y ∈ Set.uIoc E₁ E₂,
      ‖(ntr (res (Matrix.of h + Λ) ((y : ℂ) + (η : ℂ) * Complex.I))).im‖ ≤ (Cm + x ^ τ') * s := by
    intro y hy
    have hy' : |y - Eplus Λ| ≤ w := by
      have hy2 := Set.uIoc_subset_uIcc hy
      rw [Set.mem_uIcc] at hy2
      have a1 := abs_le.1 hE₁
      have a2 := abs_le.1 hE₂
      rw [abs_le]
      rcases hy2 with ⟨u1, u2⟩ | ⟨u1, u2⟩ <;> constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    set z : ℂ := (y : ℂ) + (η : ℂ) * Complex.I with hz
    have hzim : z.im = η := by simp [hz]
    have hzre : z.re = y := by simp [hz]
    have hz0 : 0 < z.im := by rw [hzim]; exact hη0
    have hzn : ‖z‖ ≤ 4 := by
      have : ‖z‖ ≤ ‖(y : ℂ)‖ + ‖(η : ℂ) * Complex.I‖ := norm_add_le _ _
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hη0] at this
      have h7 := abs_le.1 hy'
      have h8 := abs_le.1 hE3
      have h9 : |y| ≤ 3 + w := by
        rw [abs_le]; constructor <;> linarith [h7.1, h7.2, h8.1, h8.2]
      linarith
    have hzs : z ∈ specDom (1 / 4) N := by
      refine ⟨by norm_num; exact hzn, ?_⟩
      rw [hzim, abs_of_pos hη0]
      exact hspec
    have hc := hcon z hzs
    rw [Matrix.mul_one] at hc
    have hden : (1 : ℝ) / ((N : ℝ) * |z.im|) = s := by
      rw [hzim, abs_of_pos hη0, one_div]; exact hNη
    rw [hden] at hc
    have hMn : ntr (MExt Λ z) = mExt Λ z := by
      rw [CBnd_MExt_eq Λ z hz0]
      have : mExt Λ z = mSol Λ z := by simp [mExt, hz0]
      rw [this]; exact (mSol_spec Λ hΛ z hz0).2.1.symm
    have hsplit : ntr (res (Matrix.of h + Λ) z) =
        mExt Λ z + ntr (res (Matrix.of h + Λ) z - MExt Λ z) := by
      have : ntr (res (Matrix.of h + Λ) z - MExt Λ z) =
          ntr (res (Matrix.of h + Λ) z) - ntr (MExt Λ z) := by
        simp [ntr, Matrix.trace_sub, mul_sub]
      rw [this, hMn]; ring
    have hm1 : (mExt Λ z).im ≤ Cm * Real.sqrt w :=
      HCm (Idx D N) Λ hΛ hℓ z hzn hz0 w (by rw [hzre]; exact hy') (by rw [hzim]; exact hηw)
    have hm0 : 0 ≤ (mExt Λ z).im := by
      have : mExt Λ z = mSol Λ z := by simp [mExt, hz0]
      rw [this]; exact (mSol_spec Λ hΛ z hz0).1.le
    rw [hsplit, Complex.add_im, Real.norm_eq_abs, abs_le]
    have hnn : |(ntr (res (Matrix.of h + Λ) z - MExt Λ z)).im| ≤ x ^ τ' * s :=
      (Complex.abs_im_le_norm _).trans hc
    have hnn' := abs_le.1 hnn
    have hmm : Cm * Real.sqrt w ≤ Cm * s := mul_le_mul_of_nonneg_left hsw hCm.le
    constructor <;> nlinarith [hnn'.1, hnn'.2]
  -- the integral
  have hint : ‖∫ y in E₁..E₂, (ntr (res (Matrix.of h + Λ) ((y : ℂ) + (η : ℂ) * Complex.I))).im‖ ≤
      (Cm + x ^ τ') * s * |E₂ - E₁| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have hE12 : |E₂ - E₁| ≤ 2 * w := by
    have a1 := abs_le.1 hE₁
    have a2 := abs_le.1 hE₂
    rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have hcount : |edgeCount D N A η E₁ E₂ h| ≤
      ((D * N : ℕ) : ℝ) * ((Cm + x ^ τ') * s * (2 * w)) := by
    unfold edgeCount
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    rw [Real.norm_eq_abs] at hint
    refine mul_le_mul_of_nonneg_left (hint.trans ?_) (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_left hE12 (by positivity)
  -- the arithmetic
  have hfin : ((D * N : ℕ) : ℝ) * ((Cm + x ^ τ') * s * (2 * w)) ≤
      2 * D * (Cm + 1) * x ^ (2 * σ + τ') := by
    rw [Real.rpow_add hx0, ← hmul]
    push_cast
    have hCx : Cm + x ^ τ' ≤ (Cm + 1) * x ^ τ' := by nlinarith
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    calc (D : ℝ) * x * ((Cm + x ^ τ') * s * (2 * w))
        = 2 * D * (Cm + x ^ τ') * (x * w * s) := by ring
      _ ≤ 2 * D * ((Cm + 1) * x ^ τ') * (x * w * s) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCx (by positivity))
            (by positivity)
      _ = 2 * D * (Cm + 1) * (x * w * s * x ^ τ') := by ring
      _ = _ := by ring
  have := hbig
  linarith [hcount, hfin]

/-! ### The form of `ℱ₂` -/

section F2

variable {D N : ℕ}

/-- One-entry substitution keeps a Hermitian array Hermitian. -/
private lemma CBnd_slice_herm (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) (w : ℂ) : (Matrix.of (setEntry h i j w)).IsHermitian := by
  have e : symArr (setEntry h i j w) = setEntry h i j w := by
    rw [symArr_setEntry, symArr_of_isHermitian h hh]
  rw [← e]
  exact symArr_isHermitian _

/-- A Hermitian array is unchanged by writing its own entry `(i, j)` back. -/
private lemma CBnd_setEntry_self (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j : Idx D N) : setEntry h i j (h i j) = h := by
  funext k l
  have h1 : ∀ k l, starRingEnd ℂ (h l k) = h k l := fun k l => by
    simpa [Complex.star_def] using hh.apply k l
  by_cases hd : i = j
  · subst hd
    by_cases hkl : k = i ∧ l = i
    · obtain ⟨hk, hl⟩ := hkl
      rw [hk, hl]
      have hre : (((h i i).re : ℝ) : ℂ) = h i i := Complex.conj_eq_iff_re.mp (h1 i i)
      simp [setEntry, hre]
    · simp [setEntry, hkl]
  · by_cases h1' : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1'
      simp [setEntry, hd]
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp [setEntry, hd, Ne.symm hd, h1 k l]
      · simp [setEntry, hd, h1', h2]

/-- The substitution is real-affine in the value: `setEntry h i j (w + s u) =
setEntry h i j w + s • setEntry 0 i j u` for real `s`. -/
private lemma CBnd_setEntry_line (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) (w u : ℂ) (s : ℝ) :
    setEntry h i j (w + s • u) = setEntry h i j w + s • setEntry 0 i j u := by
  funext k l
  simp only [setEntry, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, Complex.real_smul]
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = i ∧ l = i
    · simp [hkl]
    · simp [hkl]
  · by_cases h1 : k = i ∧ l = j
    · simp [hij, h1]
    · by_cases h2 : k = j ∧ l = i
      · simp [hij, h2]
      · simp [hij, h1, h2]

/-- The substitution is smooth in the value. -/
private lemma CBnd_contDiff_slice (h : Idx D N → Idx D N → ℂ) (i j : Idx D N)
    (n : WithTop ℕ∞) : ContDiff ℝ n (fun w : ℂ => setEntry h i j w) := by
  refine contDiff_pi.mpr fun p => contDiff_pi.mpr fun m => ?_
  by_cases hij : i = j
  · subst hij
    by_cases hpm : p = i ∧ m = i
    · have e : (fun x => setEntry h i i x p m) = fun x => ((x.re : ℝ) : ℂ) := by
        funext x; simp [setEntry, hpm]
      change ContDiff ℝ n (fun x => setEntry h i i x p m)
      rw [e]
      exact Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff
    · have e : (fun x => setEntry h i i x p m) = fun _ => h p m := by
        funext x; simp [setEntry, hpm]
      change ContDiff ℝ n (fun x => setEntry h i i x p m)
      rw [e]
      exact contDiff_const
  · by_cases h1 : p = i ∧ m = j
    · have e : (fun x => setEntry h i j x p m) = fun x => x := by
        funext x; simp [setEntry, hij, h1]
      change ContDiff ℝ n (fun x => setEntry h i j x p m)
      rw [e]
      exact contDiff_id
    · by_cases h2 : p = j ∧ m = i
      · have e : (fun x => setEntry h i j x p m) = fun x => starRingEnd ℂ x := by
          funext x; simp [setEntry, hij, h2]
        change ContDiff ℝ n (fun x => setEntry h i j x p m)
        rw [e]
        exact Complex.conjCLE.contDiff
      · have e : (fun x => setEntry h i j x p m) = fun _ => h p m := by
          funext x; simp [setEntry, hij, h1, h2]
        change ContDiff ℝ n (fun x => setEntry h i j x p m)
        rw [e]
        exact contDiff_const


/-- `Im G(E₂ + iη) - Im G(E₁ + iη)` at the array `h`: the matrix of (4.10) [partial_xy_F_A_t]. -/
private def CBnd_Pm (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ)
    (h : Idx D N → Idx D N → ℂ) : Matrix (Idx D N) (Idx D N) ℂ :=
  imRes (Matrix.of h + lam D N A) ((E₂ : ℂ) + (η : ℂ) * Complex.I) -
    imRes (Matrix.of h + lam D N A) ((E₁ : ℂ) + (η : ℂ) * Complex.I)

/-- `Im G` is Hermitian entrywise: `conj (Im G)_{ji} = (Im G)_{ij}`. -/
private lemma CBnd_imRes_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (z : ℂ)
    (i j : ι) : starRingEnd ℂ (imRes X z j i) = imRes X z i j := by
  unfold imRes
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Complex.star_def,
    smul_eq_mul, map_mul, map_inv₀, map_sub, Complex.conj_conj]
  have h2 : starRingEnd ℂ (2 : ℂ) = 2 := map_ofNat _ 2
  rw [h2, Complex.conj_I]
  field_simp
  ring

/-- `(Im G)_{ij} = (G(z)_{ij} - G(z̄)_{ij})/(2i)` for Hermitian `X` and `Im z > 0`. -/
private lemma CBnd_imRes_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (z : ℂ) (hz : 0 < z.im) (i j : ι) :
    imRes X z i j = (2 * Complex.I)⁻¹ * (res X z i j - res X (star z) i j) := by
  have hc : res X (star z) = (res X z)ᴴ := res_conj X hX z hz
  unfold imRes
  rw [hc]
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]

/-- `Pm` is Hermitian entrywise. -/
private lemma CBnd_Pm_conj (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ)
    (h : Idx D N → Idx D N → ℂ) (i j : Idx D N) :
    starRingEnd ℂ (CBnd_Pm D N A η E₁ E₂ h j i) = CBnd_Pm D N A η E₁ E₂ h i j := by
  unfold CBnd_Pm
  simp only [Matrix.sub_apply, map_sub, CBnd_imRes_conj]

/-- The trace of `P` against the one-entry array `setEntry 0 i j u`. -/
private lemma CBnd_trace_slice (P : Matrix (Idx D N) (Idx D N) ℂ) (i j : Idx D N) (u : ℂ) :
    (P * Matrix.of (setEntry 0 i j u)).trace =
      if i = j then P i i * ((u.re : ℝ) : ℂ) else P j i * u + P i j * starRingEnd ℂ u := by
  by_cases hij : i = j
  · subst hij
    simp [Matrix.trace, Matrix.mul_apply, setEntry, ite_and, mul_ite]
  · simp only [hij, ite_false]
    have hV : ∀ l k, setEntry (0 : Idx D N → Idx D N → ℂ) i j u l k =
        (if l = i ∧ k = j then u else 0) + (if l = j ∧ k = i then starRingEnd ℂ u else 0) := by
      intro l k
      by_cases h1 : l = i ∧ k = j
      · obtain ⟨rfl, rfl⟩ := h1
        simp [setEntry, hij, Ne.symm hij]
      · by_cases h2 : l = j ∧ k = i
        · obtain ⟨rfl, rfl⟩ := h2
          simp [setEntry, hij, Ne.symm hij]
        · simp [setEntry, hij, h1, h2]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, hV, mul_add,
      Finset.sum_add_distrib, ite_and, mul_ite, mul_zero]
    simp [Finset.sum_ite_eq']

/-- The edge count is differentiable along the slice. -/
private lemma CBnd_diff_edge (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ) (hη : 0 < η)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    DifferentiableAt ℝ (fun w' : ℂ => edgeCount D N A η E₁ E₂ (setEntry h i j w')) w := by
  have hsm : (fun w' : ℂ => edgeCount D N A η E₁ E₂ (setEntry h i j w')) =
      (fun h' => edgeCount D N A η E₁ E₂ (symArr h')) ∘ (fun w' => setEntry h i j w') := by
    funext w'
    simp only [Function.comp, symArr_setEntry, symArr_of_isHermitian h hh]
  rw [hsm]
  exact ((edgeCount_contDiff D N A η E₁ E₂ hη).comp
    (CBnd_contDiff_slice h i j ∞)).differentiable (by simp) w

/-- The first derivative of `w ↦ A(setEntry h i j w)` in the direction `u` is `-tr(P(w) V_u)`,
`V_u = setEntry 0 i j u` (4.10) [partial_xy_F_A_t]. -/
private lemma CBnd_fderiv_edge (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ) (hη : 0 < η)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w u : ℂ) :
    fderiv ℝ (fun w' : ℂ => edgeCount D N A η E₁ E₂ (setEntry h i j w')) w u =
      -((CBnd_Pm D N A η E₁ E₂ (setEntry h i j w) * Matrix.of (setEntry 0 i j u)).trace.re) := by
  have hdiff := CBnd_diff_edge A η E₁ E₂ hη h hh i j w
  have hV : (Matrix.of (setEntry (0 : Idx D N → Idx D N → ℂ) i j u)).IsHermitian :=
    CBnd_slice_herm 0 Matrix.isHermitian_zero i j u
  have h1 := edgeCount_hasDerivAt D N A η E₁ E₂ hη (setEntry h i j w) (setEntry 0 i j u)
    (CBnd_slice_herm h hh i j w) hV
  have hline : HasDerivAt (fun s : ℝ => w + s • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have hw0 : w + (0 : ℝ) • u = w := by simp
  have hF : HasFDerivAt (fun w' : ℂ => edgeCount D N A η E₁ E₂ (setEntry h i j w'))
      (fderiv ℝ (fun w' : ℂ => edgeCount D N A η E₁ E₂ (setEntry h i j w')) w)
      ((fun s : ℝ => w + s • u) 0) := by
    simp only [hw0]
    exact hdiff.hasFDerivAt
  have h2 := hF.comp_hasDerivAt (0 : ℝ) hline
  have hfun : (fun w' : ℂ => edgeCount D N A η E₁ E₂ (setEntry h i j w')) ∘
      (fun s : ℝ => w + s • u) =
      fun s : ℝ => edgeCount D N A η E₁ E₂ (setEntry h i j w + s • setEntry 0 i j u) := by
    funext s
    simp only [Function.comp, CBnd_setEntry_line]
  rw [hfun] at h2
  exact h2.unique h1

/-- The Wirtinger derivatives of `A` along the slice (4.10) [partial_xy_F_A_t]: `∂_w A = -c P_{ji}`
and `∂_{w̄} A = -c P_{ij}`, `c = 1` off the diagonal and `1/2` on it. -/
private lemma CBnd_dW_edge (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ) (hη : 0 < η)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    dWbar (fun w' : ℂ => ((edgeCount D N A η E₁ E₂ (setEntry h i j w') : ℝ) : ℂ)) w =
      -(if i = j then (1 / 2 : ℂ) else 1) * CBnd_Pm D N A η E₁ E₂ (setEntry h i j w) i j ∧
    dW (fun w' : ℂ => ((edgeCount D N A η E₁ E₂ (setEntry h i j w') : ℝ) : ℂ)) w =
      -(if i = j then (1 / 2 : ℂ) else 1) * CBnd_Pm D N A η E₁ E₂ (setEntry h i j w) j i := by
  set g : ℂ → ℂ := fun w' => ((edgeCount D N A η E₁ E₂ (setEntry h i j w') : ℝ) : ℂ) with hgdef
  set P := CBnd_Pm D N A η E₁ E₂ (setEntry h i j w) with hP
  have hdiff := CBnd_diff_edge A η E₁ E₂ hη h hh i j w
  have hfd := CBnd_fderiv_edge A η E₁ E₂ hη h hh i j w
  have hg : ∀ v : ℂ, fderiv ℝ g w v =
      ((fderiv ℝ (fun w' : ℂ => edgeCount D N A η E₁ E₂ (setEntry h i j w')) w v : ℝ) : ℂ) := by
    intro v
    have h1 : HasFDerivAt g (Complex.ofRealCLM.comp (fderiv ℝ
        (fun w' : ℂ => edgeCount D N A η E₁ E₂ (setEntry h i j w')) w)) w :=
      Complex.ofRealCLM.hasFDerivAt.comp w hdiff.hasFDerivAt
    rw [h1.fderiv]
    rfl
  have hc1 : starRingEnd ℂ (P j i) = P i j := CBnd_Pm_conj D N A η E₁ E₂ _ i j
  have hc2 : starRingEnd ℂ (P i j) = P j i := by
    have := CBnd_Pm_conj D N A η E₁ E₂ (setEntry h i j w) j i
    exact this
  have hc3 : starRingEnd ℂ (P i i) = P i i := CBnd_Pm_conj D N A η E₁ E₂ _ i i
  by_cases hij : i = j
  · subst hij
    have hv : ∀ v : ℂ, fderiv ℝ g w v = -(P i i * ((v.re : ℝ) : ℂ)) := by
      intro v
      rw [hg, hfd, CBnd_trace_slice]
      simp only [ite_true]
      have : ((P i i * ((v.re : ℝ) : ℂ)).re : ℂ) = P i i * ((v.re : ℝ) : ℂ) := by
        apply Complex.conj_eq_iff_re.1
        rw [map_mul, hc3, Complex.conj_ofReal]
      push_cast
      rw [this]
    simp only [dW, dWbar, hv]
    simp
    ring
  · have hv : ∀ v : ℂ, fderiv ℝ g w v =
        -(P j i * v + P i j * starRingEnd ℂ v) := by
      intro v
      rw [hg, hfd, CBnd_trace_slice]
      simp only [hij, ite_false]
      have : ((P j i * v + P i j * starRingEnd ℂ v).re : ℂ) =
          P j i * v + P i j * starRingEnd ℂ v := by
        apply Complex.conj_eq_iff_re.1
        rw [map_add, map_mul, map_mul, hc1, hc2, Complex.conj_conj]
        ring
      push_cast
      rw [this]
    simp only [dW, dWbar, hv, hij, ite_false]
    simp
    constructor
    · linear_combination (-(P j i - P i j) / 2) * Complex.I_sq
    · linear_combination ((P j i - P i j) / 2) * Complex.I_sq

/-- Every resolvent entry is differentiable along the slice. -/
private lemma CBnd_diff_res (Λ : Matrix (Idx D N) (Idx D N) ℂ) (hΛ : Λ.IsHermitian) (ξ : ℂ)
    (hξ : ξ.im ≠ 0) (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian)
    (i j k l : Idx D N) (w : ℂ) :
    DifferentiableAt ℝ (fun w' : ℂ => res (Matrix.of (setEntry h i j w') + Λ) ξ k l) w := by
  have e : (fun w' : ℂ => res (Matrix.of (setEntry h i j w') + Λ) ξ k l) =
      (fun h' : Idx D N → Idx D N → ℂ => res (Matrix.of (symArr h') + Λ) ξ k l) ∘
        (fun w' => setEntry h i j w') := by
    funext w'
    simp only [Function.comp, symArr_setEntry, symArr_of_isHermitian h hh]
  rw [e]
  exact ((contDiff_res_symArr Λ hΛ ξ hξ k l 1).comp
    (CBnd_contDiff_slice h i j 1)).differentiable (by norm_num) w

/-- `∂_w` of a constant times a combination of four differentiable functions. -/
private lemma CBnd_dW_comb (α : ℂ) {f₁ f₂ f₃ f₄ : ℂ → ℂ} {w : ℂ} (h₁ : DifferentiableAt ℝ f₁ w)
    (h₂ : DifferentiableAt ℝ f₂ w) (h₃ : DifferentiableAt ℝ f₃ w) (h₄ : DifferentiableAt ℝ f₄ w) :
    dW (fun x => α * ((f₁ x - f₂ x) - (f₃ x - f₄ x))) w =
      α * ((dW f₁ w - dW f₂ w) - (dW f₃ w - dW f₄ w)) := by
  have h : fderiv ℝ (fun x => α * ((f₁ x - f₂ x) - (f₃ x - f₄ x))) w =
      α • (fderiv ℝ f₁ w - fderiv ℝ f₂ w - (fderiv ℝ f₃ w - fderiv ℝ f₄ w)) :=
    (((h₁.hasFDerivAt.sub h₂.hasFDerivAt).sub (h₃.hasFDerivAt.sub h₄.hasFDerivAt)).const_mul
      α).fderiv
  simp only [dW]
  rw [h]
  simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul]
  ring

/-- `∂_{w̄} A` along the slice as a combination of resolvent entries (4.10)
[partial_xy_F_A_t]: `-c ((G_2 - G_2^*) - (G_1 - G_1^*))_{ij}/(2i)`. -/
private lemma CBnd_dWbar_fun (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ) (hη : 0 < η)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    (fun w' : ℂ => dWbar (fun w'' : ℂ =>
        ((edgeCount D N A η E₁ E₂ (setEntry h i j w'') : ℝ) : ℂ)) w') =
      fun w' => (-(if i = j then (1 / 2 : ℂ) else 1) * (2 * Complex.I)⁻¹) *
        (((res (Matrix.of (setEntry h i j w') + lam D N A)
              ((E₂ : ℂ) + (η : ℂ) * Complex.I) i j -
            res (Matrix.of (setEntry h i j w') + lam D N A)
              (star ((E₂ : ℂ) + (η : ℂ) * Complex.I)) i j) -
          (res (Matrix.of (setEntry h i j w') + lam D N A)
              ((E₁ : ℂ) + (η : ℂ) * Complex.I) i j -
            res (Matrix.of (setEntry h i j w') + lam D N A)
              (star ((E₁ : ℂ) + (η : ℂ) * Complex.I)) i j))) := by
  have hΛh : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hz₁i : 0 < (((E₁ : ℂ) + (η : ℂ) * Complex.I)).im := by simp [hη]
  have hz₂i : 0 < (((E₂ : ℂ) + (η : ℂ) * Complex.I)).im := by simp [hη]
  funext w'
  rw [(CBnd_dW_edge A η E₁ E₂ hη h hh i j w').1]
  have hX := (CBnd_slice_herm h hh i j w').add hΛh
  unfold CBnd_Pm
  simp only [Matrix.sub_apply]
  rw [CBnd_imRes_entry _ hX _ hz₂i, CBnd_imRes_entry _ hX _ hz₁i]
  ring

/-- `∂_{w̄} A` is differentiable along the slice. -/
private lemma CBnd_diff_dWbar_edge (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ) (hη : 0 < η)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    DifferentiableAt ℝ (fun w' : ℂ => dWbar (fun w'' : ℂ =>
        ((edgeCount D N A η E₁ E₂ (setEntry h i j w'') : ℝ) : ℂ)) w') w := by
  have hΛh : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hz₁i : 0 < (((E₁ : ℂ) + (η : ℂ) * Complex.I)).im := by simp [hη]
  have hz₂i : 0 < (((E₂ : ℂ) + (η : ℂ) * Complex.I)).im := by simp [hη]
  have hs₁ : (star ((E₁ : ℂ) + (η : ℂ) * Complex.I)).im ≠ 0 := by simp [hη.ne']
  have hs₂ : (star ((E₂ : ℂ) + (η : ℂ) * Complex.I)).im ≠ 0 := by simp [hη.ne']
  rw [CBnd_dWbar_fun A η E₁ E₂ hη h hh i j]
  exact (differentiableAt_const _).mul
    (((CBnd_diff_res _ hΛh _ hz₂i.ne' h hh i j i j w).sub
      (CBnd_diff_res _ hΛh _ hs₂ h hh i j i j w)).sub
      ((CBnd_diff_res _ hΛh _ hz₁i.ne' h hh i j i j w).sub
      (CBnd_diff_res _ hΛh _ hs₁ h hh i j i j w)))

/-- (4.11) [partial_xy_partial_yx_F_A_t]: the second Wirtinger derivative of `A` along the slice,
`∂_w ∂_{w̄} A = c² Σ_e ε_e (G_{ii} G_{jj} - G*_{ii} G*_{jj})/(2i)`, `ε_2 = 1`, `ε_1 = -1`,
`G = G(E_e + iη)`, `G* = G(E_e - iη)`, `c = 1` off the diagonal and `1/2` on it. -/
private lemma CBnd_dWdWbar_edge (A : Matrix (Fin N) (Fin N) ℂ) (η E₁ E₂ : ℝ) (hη : 0 < η)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) (w : ℂ) :
    dW (fun w' : ℂ => dWbar (fun w'' : ℂ =>
        ((edgeCount D N A η E₁ E₂ (setEntry h i j w'') : ℝ) : ℂ)) w') w =
      (if i = j then (1 / 2 : ℂ) else 1) ^ 2 * (2 * Complex.I)⁻¹ *
        (((res (Matrix.of (setEntry h i j w) + lam D N A) ((E₂ : ℂ) + (η : ℂ) * Complex.I) i i *
            res (Matrix.of (setEntry h i j w) + lam D N A) ((E₂ : ℂ) + (η : ℂ) * Complex.I) j j) -
          (res (Matrix.of (setEntry h i j w) + lam D N A)
              (star ((E₂ : ℂ) + (η : ℂ) * Complex.I)) i i *
            res (Matrix.of (setEntry h i j w) + lam D N A)
              (star ((E₂ : ℂ) + (η : ℂ) * Complex.I)) j j)) -
        ((res (Matrix.of (setEntry h i j w) + lam D N A) ((E₁ : ℂ) + (η : ℂ) * Complex.I) i i *
            res (Matrix.of (setEntry h i j w) + lam D N A) ((E₁ : ℂ) + (η : ℂ) * Complex.I) j j) -
          (res (Matrix.of (setEntry h i j w) + lam D N A)
              (star ((E₁ : ℂ) + (η : ℂ) * Complex.I)) i i *
            res (Matrix.of (setEntry h i j w) + lam D N A)
              (star ((E₁ : ℂ) + (η : ℂ) * Complex.I)) j j))) := by
  set Λ := lam D N A with hΛ
  have hΛh : Λ.IsHermitian := lam_isHermitian D N A
  set z₁ : ℂ := (E₁ : ℂ) + (η : ℂ) * Complex.I with hz₁
  set z₂ : ℂ := (E₂ : ℂ) + (η : ℂ) * Complex.I with hz₂
  have hz₁i : 0 < z₁.im := by simp [hz₁, hη]
  have hz₂i : 0 < z₂.im := by simp [hz₂, hη]
  have hs₁ : (star z₁).im ≠ 0 := by simp [hz₁, hη.ne']
  have hs₂ : (star z₂).im ≠ 0 := by simp [hz₂, hη.ne']
  set c : ℂ := if i = j then (1 / 2 : ℂ) else 1 with hc
  rw [CBnd_dWbar_fun A η E₁ E₂ hη h hh i j, CBnd_dW_comb _
    (CBnd_diff_res Λ hΛh z₂ hz₂i.ne' h hh i j i j w)
    (CBnd_diff_res Λ hΛh (star z₂) hs₂ h hh i j i j w)
    (CBnd_diff_res Λ hΛh z₁ hz₁i.ne' h hh i j i j w)
    (CBnd_diff_res Λ hΛh (star z₁) hs₁ h hh i j i j w)]
  have hd := fun (ξ : ℂ) (hξ : ξ.im ≠ 0) =>
    congrFun (res_dW Λ hΛh ξ hξ h hh i j i j).1 w
  rw [hd z₂ hz₂i.ne', hd (star z₂) hs₂, hd z₁ hz₁i.ne', hd (star z₁) hs₁]
  ring

/-- `fderiv` of `ofReal ∘ φ`. -/
private lemma CBnd_fderiv_ofReal {φ : ℂ → ℝ} {w : ℂ} (hφ : DifferentiableAt ℝ φ w) (v : ℂ) :
    fderiv ℝ (fun x : ℂ => ((φ x : ℝ) : ℂ)) w v = ((fderiv ℝ φ w v : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun x : ℂ => ((φ x : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ φ w)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w hφ.hasFDerivAt
  rw [h1.fderiv]
  rfl

/-- A linear functional on `Fin n → ℝ` is the sum of its values on the coordinate vectors. -/
private lemma CBnd_clm_pi {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (u : Fin n → ℝ) :
    L u = ∑ m, u m * L (Pi.single m 1) := by
  conv_lhs => rw [← Finset.univ_sum_single u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (Pi.single m (u m) : Fin n → ℝ) = u m • Pi.single m (1 : ℝ) := by
    rw [← Pi.single_smul]; simp
  rw [this, map_smul, smul_eq_mul]

/-- The chain rule for the Wirtinger derivatives of `w ↦ F(g_1(w), …, g_n(w))`, real `g_m`. -/
private lemma CBnd_chain {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : Differentiable ℝ F)
    (g : Fin n → ℂ → ℝ) (w : ℂ) (hg : ∀ m, DifferentiableAt ℝ (g m) w) :
    dW (fun x : ℂ => ((F (fun m => g m x) : ℝ) : ℂ)) w =
        ∑ m, ((fderiv ℝ F (fun m' => g m' w) (Pi.single m 1) : ℝ) : ℂ) *
          dW (fun x : ℂ => ((g m x : ℝ) : ℂ)) w ∧
      dWbar (fun x : ℂ => ((F (fun m => g m x) : ℝ) : ℂ)) w =
        ∑ m, ((fderiv ℝ F (fun m' => g m' w) (Pi.single m 1) : ℝ) : ℂ) *
          dWbar (fun x : ℂ => ((g m x : ℝ) : ℂ)) w := by
  have hA : HasFDerivAt (fun x : ℂ => (fun m => g m x))
      (ContinuousLinearMap.pi (fun m => fderiv ℝ (g m) w)) w :=
    hasFDerivAt_pi'.2 fun m => (hg m).hasFDerivAt
  have hφ : HasFDerivAt (fun x : ℂ => F (fun m => g m x))
      ((fderiv ℝ F (fun m' => g m' w)).comp (ContinuousLinearMap.pi (fun m => fderiv ℝ (g m) w)))
      w := (hF _).hasFDerivAt.comp w hA
  have hφd : DifferentiableAt ℝ (fun x : ℂ => F (fun m => g m x)) w := hφ.differentiableAt
  have hv : ∀ v : ℂ, fderiv ℝ (fun x : ℂ => F (fun m => g m x)) w v =
      ∑ m, fderiv ℝ (g m) w v * fderiv ℝ F (fun m' => g m' w) (Pi.single m 1) := by
    intro v
    rw [hφ.fderiv]
    exact CBnd_clm_pi _ _
  constructor
  · simp only [dW, CBnd_fderiv_ofReal hφd, hv, CBnd_fderiv_ofReal (hg _)]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun m _ => by ring
  · simp only [dWbar, CBnd_fderiv_ofReal hφd, hv, CBnd_fderiv_ofReal (hg _)]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun m _ => by ring

/-- `∂_w` of a finite sum. -/
private lemma CBnd_dW_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (w : ℂ)
    (hf : ∀ m ∈ s, DifferentiableAt ℝ (f m) w) :
    dW (fun x => ∑ m ∈ s, f m x) w = ∑ m ∈ s, dW (f m) w := by
  have h : fderiv ℝ (fun x => ∑ m ∈ s, f m x) w = ∑ m ∈ s, fderiv ℝ (f m) w :=
    fderiv_fun_sum hf
  simp only [dW]
  rw [h]
  simp only [_root_.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

/-- The partial derivative `y ↦ DF(y) e_m` of a smooth `F` is smooth. -/
private lemma CBnd_contDiff_partial {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (m : Fin n) : ContDiff ℝ ∞ (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1)) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The scalar identity behind `CBnd_wirt11`: `κ c² = 1` removes the weights. -/
private lemma CBnd_alg {ι : Type*} (s : Finset ι) (κ c p f W S T : ℂ) (a p' : ι → ℂ)
    (hk : κ * c ^ 2 = 1) (hT : W * S = T) :
    κ * ((∑ x ∈ s, a x * (-c * p' x)) * (-c * p) + f * (c ^ 2 * W * S)) =
      (∑ x ∈ s, a x * (p' x * p)) + f * T := by
  rw [Finset.sum_mul, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun x _ => by linear_combination (a x * p' x * p) * hk
  · rw [← hT]; linear_combination (f * W * S) * hk

/-- The chain and product rules for `∂_w ∂_{w̄} F(A_1, …, A_n)` along the slice, before the
derivatives of the counts `A_m` are inserted. -/
private lemma CBnd_wirt11a {n : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (E₁ E₂ : Fin n → ℝ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    wirt 1 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) (h i j) =
      ∑ m, ((∑ m', ((fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1))
          (fun k => edgeCount D N A η (E₁ k) (E₂ k) (setEntry h i j (h i j))) (Pi.single m' 1) :
            ℝ) : ℂ) *
          dW (fun x : ℂ => ((edgeCount D N A η (E₁ m') (E₂ m') (setEntry h i j x) : ℝ) : ℂ))
            (h i j)) *
        dWbar (fun x : ℂ => ((edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j x) : ℝ) : ℂ))
          (h i j) +
      ((fderiv ℝ F (fun k => edgeCount D N A η (E₁ k) (E₂ k) (setEntry h i j (h i j)))
          (Pi.single m 1) : ℝ) : ℂ) *
        dW (fun w' : ℂ => dWbar (fun w'' : ℂ =>
          ((edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j w'') : ℝ) : ℂ)) w') (h i j)) := by
  set g : Fin n → ℂ → ℝ := fun m w => edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j w) with hgdef
  have hgd : ∀ w m, DifferentiableAt ℝ (g m) w := fun w m =>
    CBnd_diff_edge A η (E₁ m) (E₂ m) hη h hh i j w
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hF1 : ∀ m, Differentiable ℝ (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1)) :=
    fun m => (CBnd_contDiff_partial F hF m).differentiable (by simp)
  have hA' : ∀ w, DifferentiableAt ℝ (fun x : ℂ => (fun m => g m x)) w := fun w =>
    differentiableAt_pi.2 (hgd w)
  have h1 : dWbar (fun w : ℂ => ((F (fun m => g m w) : ℝ) : ℂ)) = fun w =>
      ∑ m, ((fderiv ℝ F (fun m' => g m' w) (Pi.single m 1) : ℝ) : ℂ) *
        dWbar (fun x : ℂ => ((g m x : ℝ) : ℂ)) w := by
    funext w; exact (CBnd_chain F hFd g w (hgd w)).2
  have e1 : wirt 1 1 (fun w : ℂ => ((F (fun m => g m w) : ℝ) : ℂ)) =
      dW (dWbar (fun w : ℂ => ((F (fun m => g m w) : ℝ) : ℂ))) := by
    simp [wirt]
  change wirt 1 1 (fun w : ℂ => ((F (fun m => g m w) : ℝ) : ℂ)) (h i j) = _
  have hfm : ∀ m, DifferentiableAt ℝ (fun w : ℂ =>
      ((fderiv ℝ F (fun m' => g m' w) (Pi.single m 1) : ℝ) : ℂ)) (h i j) := fun m =>
    Complex.ofRealCLM.differentiableAt.comp (h i j)
      (DifferentiableAt.comp (h i j) (hF1 m _) (hA' (h i j)))
  have hgm : ∀ m, DifferentiableAt ℝ (fun w' : ℂ => dWbar (fun w'' : ℂ =>
      ((g m w'' : ℝ) : ℂ)) w') (h i j) := fun m =>
    CBnd_diff_dWbar_edge A η (E₁ m) (E₂ m) hη h hh i j (h i j)
  have hsum := CBnd_dW_sum (Finset.univ : Finset (Fin n)) (fun (m : Fin n) (w : ℂ) =>
    ((fderiv ℝ F (fun m' => g m' w) (Pi.single m 1) : ℝ) : ℂ) *
      dWbar (fun x : ℂ => ((g m x : ℝ) : ℂ)) w) (h i j) (fun m _ => (hfm m).mul (hgm m))
  rw [e1, h1, hsum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [(dW_mul (hfm m) (hgm m)).1,
    (CBnd_chain (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1)) (hF1 m) g (h i j)
      (hgd _)).1]

/-- The Wirtinger derivative `∂_w ∂_{w̄}` of `F(A_1, …, A_n)` along the slice, at the point
`h_{ij}` of a Hermitian array, times the weight `genWt`: the display before (4.16) [eq:roughXY]
(proof of Lemma 4.3 [rescomY]) with `F_{mm'} = D²F(e_{m'}, e_m)`, `P_m = Im G(E₂(m) + iη) -
Im G(E₁(m) + iη)` and the traces of `Im G` and `G` at the points `E_e(m) ± iη`. -/
private lemma CBnd_wirt11 {n : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (hη : 0 < η)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (E₁ E₂ : Fin n → ℝ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) (i j : Idx D N) :
    genWt i j * wirt 1 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) (h i j) =
      (∑ m, ∑ m', ((fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1))
          (fun k => edgeCount D N A η (E₁ k) (E₂ k) h) (Pi.single m' 1) : ℝ) : ℂ) *
        (CBnd_Pm D N A η (E₁ m') (E₂ m') h j i * CBnd_Pm D N A η (E₁ m) (E₂ m) h i j)) +
      (∑ m, ((fderiv ℝ F (fun k => edgeCount D N A η (E₁ k) (E₂ k) h) (Pi.single m 1) : ℝ) : ℂ) *
        ((imRes (Matrix.of h + lam D N A) ((E₂ m : ℂ) + (η : ℂ) * Complex.I) i i *
            res (Matrix.of h + lam D N A) ((E₂ m : ℂ) + (η : ℂ) * Complex.I) j j +
          res (Matrix.of h + lam D N A) (star ((E₂ m : ℂ) + (η : ℂ) * Complex.I)) i i *
            imRes (Matrix.of h + lam D N A) ((E₂ m : ℂ) + (η : ℂ) * Complex.I) j j) -
          (imRes (Matrix.of h + lam D N A) ((E₁ m : ℂ) + (η : ℂ) * Complex.I) i i *
            res (Matrix.of h + lam D N A) ((E₁ m : ℂ) + (η : ℂ) * Complex.I) j j +
          res (Matrix.of h + lam D N A) (star ((E₁ m : ℂ) + (η : ℂ) * Complex.I)) i i *
            imRes (Matrix.of h + lam D N A) ((E₁ m : ℂ) + (η : ℂ) * Complex.I) j j))) := by
  have hsub := CBnd_setEntry_self h hh i j
  have hΛh : (lam D N A).IsHermitian := lam_isHermitian D N A
  have hX : (Matrix.of h + lam D N A).IsHermitian := hh.add hΛh
  rw [CBnd_wirt11a A η hη F hF E₁ E₂ h hh i j, hsub]
  have hdW : ∀ m, dW (fun x : ℂ => ((edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j x) : ℝ) : ℂ))
      (h i j) = -(if i = j then (1 / 2 : ℂ) else 1) * CBnd_Pm D N A η (E₁ m) (E₂ m) h j i := by
    intro m
    rw [(CBnd_dW_edge A η (E₁ m) (E₂ m) hη h hh i j (h i j)).2, hsub]
  have hdWbar : ∀ m, dWbar (fun x : ℂ =>
      ((edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j x) : ℝ) : ℂ)) (h i j) =
      -(if i = j then (1 / 2 : ℂ) else 1) * CBnd_Pm D N A η (E₁ m) (E₂ m) h i j := by
    intro m
    rw [(CBnd_dW_edge A η (E₁ m) (E₂ m) hη h hh i j (h i j)).1, hsub]
  have hdd : ∀ m, dW (fun w' : ℂ => dWbar (fun w'' : ℂ =>
      ((edgeCount D N A η (E₁ m) (E₂ m) (setEntry h i j w'') : ℝ) : ℂ)) w') (h i j) =
      (if i = j then (1 / 2 : ℂ) else 1) ^ 2 * (2 * Complex.I)⁻¹ *
        (((res (Matrix.of h + lam D N A) ((E₂ m : ℂ) + (η : ℂ) * Complex.I) i i *
            res (Matrix.of h + lam D N A) ((E₂ m : ℂ) + (η : ℂ) * Complex.I) j j) -
          (res (Matrix.of h + lam D N A) (star ((E₂ m : ℂ) + (η : ℂ) * Complex.I)) i i *
            res (Matrix.of h + lam D N A) (star ((E₂ m : ℂ) + (η : ℂ) * Complex.I)) j j)) -
        ((res (Matrix.of h + lam D N A) ((E₁ m : ℂ) + (η : ℂ) * Complex.I) i i *
            res (Matrix.of h + lam D N A) ((E₁ m : ℂ) + (η : ℂ) * Complex.I) j j) -
          (res (Matrix.of h + lam D N A) (star ((E₁ m : ℂ) + (η : ℂ) * Complex.I)) i i *
            res (Matrix.of h + lam D N A) (star ((E₁ m : ℂ) + (η : ℂ) * Complex.I)) j j))) := by
    intro m
    rw [CBnd_dWdWbar_edge A η (E₁ m) (E₂ m) hη h hh i j (h i j), hsub]
  have hY : ∀ (z : ℂ), 0 < z.im → ∀ k, imRes (Matrix.of h + lam D N A) z k k =
      (2 * Complex.I)⁻¹ * (res (Matrix.of h + lam D N A) z k k -
        res (Matrix.of h + lam D N A) (star z) k k) :=
    fun z hz k => CBnd_imRes_entry _ hX z hz k k
  have hz1 : ∀ m, 0 < (((E₁ m : ℂ) + (η : ℂ) * Complex.I)).im := fun m => by simp [hη]
  have hz2 : ∀ m, 0 < (((E₂ m : ℂ) + (η : ℂ) * Complex.I)).im := fun m => by simp [hη]
  set c : ℂ := if i = j then (1 / 2 : ℂ) else 1 with hc
  have hc0 : c ≠ 0 := by by_cases hij : i = j <;> simp [hc, hij]
  have hgw : genWt i j = (c ^ 2)⁻¹ := by
    by_cases hij : i = j <;> simp [genWt, hc, hij]; norm_num
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hdd m, hdWbar m]
  simp only [hdW]
  rw [hY _ (hz2 m) i, hY _ (hz2 m) j, hY _ (hz1 m) i, hY _ (hz1 m) j]
  exact CBnd_alg Finset.univ _ c _ _ _ _ _ _ _ (by rw [hgw]; field_simp) (by ring)

/-! ### Block traces -/

/-- The weight `(DN)⁻¹ - s_{xy}` of (4.9) [eq:prodnGt] with `s_{xy}` of (2.14) [eq:sij]:
`N⁻¹ (D⁻¹ - 1(block x = block y))`. -/
private lemma CBnd_sprime (i j : Idx D N) :
    (((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ) =
      (N : ℂ)⁻¹ * ((D : ℂ)⁻¹ - if i.1 = j.1 then 1 else 0) := by
  by_cases h : i.1 = j.1
  · simp [varProf, h, Nat.cast_mul]
    ring
  · simp [varProf, h, Nat.cast_mul]

/-- The weight is symmetric. -/
private lemma CBnd_sprime_symm (i j : Idx D N) :
    (((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 j i : ℂ) =
      (((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ) := by
  rw [CBnd_sprime, CBnd_sprime]
  by_cases h : i.1 = j.1
  · simp [h]
  · have h' : ¬ j.1 = i.1 := fun e => h e.symm
    simp [h, h']

/-- The block projections sum to the identity. -/
private lemma CBnd_sum_Ea : ∑ a : Fin D, Ea D N a = 1 := by
  ext p q
  simp only [Ea, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : p = q
  · simp [h]
  · simp [h]

/-- `Σ_a (D⁻¹ - E_a) = 0` for `D ≥ 1`. -/
private lemma CBnd_sum_B (hD : 1 ≤ D) :
    ∑ a : Fin D, (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) = 0 := by
  rw [Finset.sum_sub_distrib, CBnd_sum_Ea, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  rw [mul_inv_cancel₀ this, one_smul, sub_self]

/-- `Σ_a (D⁻¹ - 1(i ∈ a)) 1(j ∈ a) = D⁻¹ - 1(block i = block j)`. -/
private lemma CBnd_sum_blocks (i j : Idx D N) :
    ∑ a : Fin D, ((D : ℂ)⁻¹ - (if i.1 = a then 1 else 0)) * (if j.1 = a then 1 else 0) =
      (D : ℂ)⁻¹ - if i.1 = j.1 then 1 else 0 := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- The trace `tr(P B Q E)` for diagonal `B`, `E`. -/
private lemma CBnd_trace4 (P Q : Matrix (Idx D N) (Idx D N) ℂ) (b e : Idx D N → ℂ) :
    (P * Matrix.diagonal b * Q * Matrix.diagonal e).trace =
      ∑ j, ∑ i, P j i * b i * Q i j * e j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, Finset.sum_mul]
  simp

/-- `Σ_{x,y} ((DN)⁻¹ - s_{xy}) P_{yx} Q_{xy} = D Σ_a ⟨P (D⁻¹ - E_a) Q E_a⟩`, with `s_{xy}` of
(2.14) [eq:sij]. -/
private lemma CBnd_B1 (hD : 1 ≤ D) (P Q : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i, ∑ j, ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) * (P j i * Q i j) =
      (D : ℂ) * ∑ a : Fin D, ntr (P * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) -
        Ea D N a) * Q * Ea D N a) := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hdiag : ∀ a : Fin D, ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a =
      Matrix.diagonal (fun p : Idx D N => (D : ℂ)⁻¹ - if p.1 = a then 1 else 0) := by
    intro a
    rw [Matrix.smul_one_eq_diagonal, Ea, ← Matrix.diagonal_sub]
  have hcard : (Fintype.card (Idx D N) : ℂ) = ((D * N : ℕ) : ℂ) := by simp [Idx]
  have hntr : ∀ a : Fin D, ntr (P * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) -
        Ea D N a) * Q * Ea D N a) = (((D * N : ℕ) : ℂ))⁻¹ * ∑ j, ∑ i,
          P j i * ((D : ℂ)⁻¹ - if i.1 = a then 1 else 0) * Q i j * (if j.1 = a then 1 else 0) := by
    intro a
    rw [ntr, hdiag a, Ea, CBnd_trace4, hcard]
  have hsum : ∀ j i : Idx D N, ∑ a : Fin D, P j i * ((D : ℂ)⁻¹ - if i.1 = a then 1 else 0) * Q i j *
      (if j.1 = a then 1 else 0) =
      P j i * Q i j * ((D : ℂ)⁻¹ - if i.1 = j.1 then 1 else 0) := by
    intro j i
    rw [← CBnd_sum_blocks i j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hR : (D : ℂ) * ∑ a : Fin D, ntr (P * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) -
        Ea D N a) * Q * Ea D N a) = (D : ℂ) * ((((D * N : ℕ) : ℂ))⁻¹ * ∑ j, ∑ i,
          P j i * Q i j * ((D : ℂ)⁻¹ - if i.1 = j.1 then 1 else 0)) := by
    simp only [hntr]
    rw [← Finset.mul_sum]
    congr 2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => hsum j i
  rw [hR, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [CBnd_sprime]
  push_cast
  field_simp

/-- `Σ_{x,y} ((DN)⁻¹ - s_{xy}) Y_{xx} G_{yy} = D² N Σ_a ⟨Y (D⁻¹ - E_a)⟩ ⟨G E_a⟩`, with `s_{xy}` of
(2.14) [eq:sij]. -/
private lemma CBnd_B2 (hD : 1 ≤ D) (hN : 1 ≤ N) (Y G : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i, ∑ j, ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) * (Y i i * G j j) =
      (D : ℂ) ^ 2 * N * ∑ a : Fin D, ntr (Y * (((D : ℂ))⁻¹ •
        (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a)) * ntr (G * Ea D N a) := by
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hdiag : ∀ a : Fin D, ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a =
      Matrix.diagonal (fun p : Idx D N => (D : ℂ)⁻¹ - if p.1 = a then 1 else 0) := by
    intro a
    rw [Matrix.smul_one_eq_diagonal, Ea, ← Matrix.diagonal_sub]
  have hcard : (Fintype.card (Idx D N) : ℂ) = ((D * N : ℕ) : ℂ) := by simp [Idx]
  have hY : ∀ a : Fin D, ntr (Y * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) -
      Ea D N a)) = (((D * N : ℕ) : ℂ))⁻¹ *
        ∑ i, Y i i * ((D : ℂ)⁻¹ - if i.1 = a then 1 else 0) := by
    intro a
    rw [ntr, hdiag a, hcard]
    congr 1
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]
  have hG : ∀ a : Fin D, ntr (G * Ea D N a) = (((D * N : ℕ) : ℂ))⁻¹ *
      ∑ j, G j j * (if j.1 = a then 1 else 0) := by
    intro a
    rw [ntr, Ea, hcard]
    congr 1
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]
  have key : ∀ i j : Idx D N, ∑ a : Fin D, (Y i i * ((D : ℂ)⁻¹ - if i.1 = a then 1 else 0)) *
      (G j j * (if j.1 = a then 1 else 0)) =
      Y i i * G j j * ((D : ℂ)⁻¹ - if i.1 = j.1 then 1 else 0) := by
    intro i j
    rw [← CBnd_sum_blocks i j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hsum : ∑ a : Fin D, (∑ i, Y i i * ((D : ℂ)⁻¹ - if i.1 = a then 1 else 0)) *
      (∑ j, G j j * (if j.1 = a then 1 else 0)) =
      ∑ i, ∑ j, Y i i * G j j * ((D : ℂ)⁻¹ - if i.1 = j.1 then 1 else 0) := by
    simp only [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => key i j
  calc ∑ i, ∑ j, ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) * (Y i i * G j j)
      = (N : ℂ)⁻¹ * ∑ i, ∑ j, Y i i * G j j * ((D : ℂ)⁻¹ - if i.1 = j.1 then 1 else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [CBnd_sprime]
        ring
    _ = (D : ℂ) ^ 2 * N * ∑ a : Fin D, ntr (Y * (((D : ℂ))⁻¹ •
        (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a)) * ntr (G * Ea D N a) := by
        simp only [hY, hG]
        have e1 : ∀ a : Fin D, (((D * N : ℕ) : ℂ))⁻¹ *
            (∑ i, Y i i * ((D : ℂ)⁻¹ - if i.1 = a then 1 else 0)) *
            ((((D * N : ℕ) : ℂ))⁻¹ * ∑ j, G j j * (if j.1 = a then 1 else 0)) =
            ((((D * N : ℕ) : ℂ))⁻¹) ^ 2 * ((∑ i, Y i i * ((D : ℂ)⁻¹ - if i.1 = a then 1 else 0)) *
              (∑ j, G j j * (if j.1 = a then 1 else 0))) := fun a => by ring
        rw [Finset.sum_congr rfl (fun a _ => e1 a), ← Finset.mul_sum, hsum]
        push_cast
        field_simp

/-- `Σ_a ⟨Y (D⁻¹ - E_a)⟩ = 0`. -/
private lemma CBnd_sum_Y (hD : 1 ≤ D) (Y : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ a : Fin D, ntr (Y * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a)) = 0 := by
  unfold ntr
  rw [← Finset.mul_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, CBnd_sum_B hD, Matrix.mul_zero,
    Matrix.trace_zero, mul_zero]

/-- The `M`-subtraction of the proof of Lemma 4.3 [rescomY]: `D⟨M E_a⟩ = m` for every `a`
((2.13) [def_M], `def_M_scalar`) and `Σ_a ⟨Y (D⁻¹ - E_a)⟩ = 0` give
`Σ_a ⟨Y (D⁻¹ - E_a)⟩ ⟨G E_a⟩ = Σ_a ⟨Y (D⁻¹ - E_a)⟩ ⟨(G - M) E_a⟩`. -/
private lemma CBnd_Msub (hD : 2 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : z.im ≠ 0) (Y G : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ a : Fin D, ntr (Y * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a)) *
        ntr (G * Ea D N a) =
      ∑ a : Fin D, ntr (Y * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a)) *
        ntr ((G - MExt (lam D N A) z) * Ea D N a) := by
  have hM := (def_M_scalar D hD N hN A z hz).1
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have e : ∀ a : Fin D, ntr ((G - MExt (lam D N A) z) * Ea D N a) =
      ntr (G * Ea D N a) - (D : ℂ)⁻¹ * mExt (lam D N A) z := by
    intro a
    have h1 : ntr (MExt (lam D N A) z * Ea D N a) = (D : ℂ)⁻¹ * mExt (lam D N A) z := by
      rw [← hM a]; field_simp
    rw [← h1, Matrix.sub_mul]
    unfold ntr
    rw [Matrix.trace_sub, mul_sub]
  have e2 : ∀ a : Fin D, ntr (Y * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) -
        Ea D N a)) * ntr ((G - MExt (lam D N A) z) * Ea D N a) =
      ntr (Y * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a)) *
        ntr (G * Ea D N a) -
      ntr (Y * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a)) *
        ((D : ℂ)⁻¹ * mExt (lam D N A) z) := fun a => by rw [e a]; ring
  simp only [e2]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, CBnd_sum_Y (by omega : 1 ≤ D), zero_mul, sub_zero]

/-- The first partial derivative of a function with `‖D F‖ ≤ B` is at most `B`. -/
private lemma CBnd_F1_le {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (BF : ℝ)
    (hB : ‖iteratedFDeriv ℝ 1 F x‖ ≤ BF) (m : Fin n) :
    ‖fderiv ℝ F x (Pi.single m 1)‖ ≤ BF := by
  rw [norm_iteratedFDeriv_one] at hB
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  have : ‖(Pi.single m (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
    rw [Pi.norm_single]; simp
  rw [this, mul_one]
  exact hB

/-- The second partial derivatives of a smooth function with `‖D² F‖ ≤ B` are at most `B`. -/
private lemma CBnd_F2_le {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (x : Fin n → ℝ) (BF : ℝ) (hB : ‖iteratedFDeriv ℝ 2 F x‖ ≤ BF) (m m' : Fin n) :
    ‖fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1)) x (Pi.single m' 1)‖ ≤ BF := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have h1 : HasFDerivAt (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1))
      ((ContinuousLinearMap.apply ℝ ℝ (Pi.single m 1 : Fin n → ℝ)).comp
        (fderiv ℝ (fderiv ℝ F) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single m 1 : Fin n → ℝ)).hasFDerivAt.comp x hd.hasFDerivAt
  rw [h1.fderiv]
  have h2 : fderiv ℝ (fderiv ℝ F) x (Pi.single m' 1) (Pi.single m 1) =
      iteratedFDeriv ℝ 2 F x ![Pi.single m' 1, Pi.single m 1] := by
    rw [iteratedFDeriv_two_apply]; rfl
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [h2]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have h3 : ∏ i, ‖(![Pi.single m' 1, Pi.single m 1] : Fin 2 → (Fin n → ℝ)) i‖ = 1 := by
    simp [Fin.prod_univ_two, Pi.norm_single]
  rw [h3, mul_one]
  exact hB


/-- The spectral point `E₁(m) + iη` of `edgePt`. -/
private lemma CBnd_edgePt_zero (η : ℝ) {n : ℕ} (E₁ E₂ : Fin n → ℝ) (m : Fin n) :
    edgePt η E₁ E₂ (m, 0) = (E₁ m : ℂ) + (η : ℂ) * Complex.I := by simp [edgePt]

/-- The spectral point `E₂(m) + iη` of `edgePt`. -/
private lemma CBnd_edgePt_one (η : ℝ) {n : ℕ} (E₁ E₂ : Fin n → ℝ) (m : Fin n) :
    edgePt η E₁ E₂ (m, 1) = (E₂ m : ℂ) + (η : ℂ) * Complex.I := by simp [edgePt]

/-- The sum over `(i, j)` of the `Y`-part: `Σ s_{ij} (Y_{ii} G_{jj} + G*_{ii} Y_{jj}) =
D² N Σ_a ⟨Y (D⁻¹ - E_a)⟩ (⟨(G - M) E_a⟩ + ⟨(G* - M*) E_a⟩)`: the block-trace form with the
`M`-subtraction of the proof of Lemma 4.3 [rescomY]. -/
private lemma CBnd_Q (hD : 2 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hz : z.im ≠ 0) (Y G Gs : Matrix (Idx D N) (Idx D N) ℂ) :
    ∑ i, ∑ j, ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
        (Y i i * G j j + Gs i i * Y j j) =
      (D : ℂ) ^ 2 * N * ∑ a : Fin D, ntr (Y * (((D : ℂ))⁻¹ •
        (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a)) *
        (ntr ((G - MExt (lam D N A) z) * Ea D N a) +
          ntr ((Gs - MExt (lam D N A) (star z)) * Ea D N a)) := by
  have hsz : (star z).im ≠ 0 := by simpa using hz
  have e2 : ∑ i, ∑ j, ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) * (Gs i i * Y j j) =
      ∑ i, ∑ j, ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) * (Y i i * Gs j j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [CBnd_sprime_symm]
    ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [e2, CBnd_B2 (by omega) hN Y G, CBnd_B2 (by omega) hN Y Gs,
    CBnd_Msub hD hN A z hz Y G, CBnd_Msub hD hN A (star z) hsz Y Gs, ← mul_add,
    ← Finset.sum_add_distrib]

/-- The expansion of a bilinear trace in the differences. -/
private lemma CBnd_ntr_diff {ι : Type*} [Fintype ι] (P₁ P₀ Q₁ Q₀ B E : Matrix ι ι ℂ) :
    ‖ntr ((P₁ - P₀) * B * (Q₁ - Q₀) * E)‖ ≤ ‖ntr (P₁ * B * Q₁ * E)‖ + ‖ntr (P₁ * B * Q₀ * E)‖ +
      ‖ntr (P₀ * B * Q₁ * E)‖ + ‖ntr (P₀ * B * Q₀ * E)‖ := by
  have e : ntr ((P₁ - P₀) * B * (Q₁ - Q₀) * E) = ntr (P₁ * B * Q₁ * E) - ntr (P₁ * B * Q₀ * E) -
      ntr (P₀ * B * Q₁ * E) + ntr (P₀ * B * Q₀ * E) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, ntr, Matrix.trace_sub]
    ring
  rw [e]
  have h1 := norm_add_le (ntr (P₁ * B * Q₁ * E) - ntr (P₁ * B * Q₀ * E) - ntr (P₀ * B * Q₁ * E))
    (ntr (P₀ * B * Q₀ * E))
  have h2 := norm_sub_le (ntr (P₁ * B * Q₁ * E) - ntr (P₁ * B * Q₀ * E)) (ntr (P₀ * B * Q₁ * E))
  have h3 := norm_sub_le (ntr (P₁ * B * Q₁ * E)) (ntr (P₁ * B * Q₀ * E))
  linarith

/-- Interchange of four finite sums. -/
private lemma CBnd_sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- Interchange of three finite sums. -/
private lemma CBnd_sum3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm


/-- The sum over `r₁, r₂ : Fin n × Fin 2` written over the pairs `(m', e')`, `(m, e)`, with the
outer order `m, m', e', e`. -/
private lemma CBnd_sumX {n D : ℕ} (g : Fin n × Fin 2 → Fin n × Fin 2 → Fin D → ℝ) :
    ∑ r₁ : Fin n × Fin 2, ∑ r₂ : Fin n × Fin 2, ∑ a : Fin D, g r₁ r₂ a =
      ∑ m : Fin n, ∑ m' : Fin n, ∑ e' : Fin 2, ∑ e : Fin 2, ∑ a : Fin D, g (m', e') (m, e) a := by
  simp only [Fintype.sum_prod_type]
  calc ∑ m' : Fin n, ∑ e' : Fin 2, ∑ m : Fin n, ∑ e : Fin 2, ∑ a : Fin D, g (m', e') (m, e) a
      = ∑ m' : Fin n, ∑ m : Fin n, ∑ e' : Fin 2, ∑ e : Fin 2, ∑ a : Fin D, g (m', e') (m, e) a :=
        Finset.sum_congr rfl fun m' _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The expansion of `ℱ₂` in block traces (proof of Lemma 4.3 [rescomY], before (4.16)
[eq:roughXY]): for a Hermitian array, the `(i, j)`-sum of the integrand of `entryF2` equals
`Σ_{m,m'} F_{mm'} D Σ_a ⟨P_{m'} (D⁻¹ - E_a) P_m E_a⟩ + Σ_m F_m D² N (Q(m, 2) - Q(m, 1))`,
`P_m = Im G(E₂(m) + iη) - Im G(E₁(m) + iη)` and `Q(r) = Σ_a ⟨Im G(z_r) (D⁻¹ - E_a)⟩
(⟨(G - M)(z_r) E_a⟩ + ⟨(G - M)(z̄_r) E_a⟩)`. -/
private lemma CBnd_F2_eq {n : ℕ} (hD : 2 ≤ D) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (η : ℝ) (hη : 0 < η) (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) (E₁ E₂ : Fin n → ℝ)
    (h : Idx D N → Idx D N → ℂ) (hh : (Matrix.of h).IsHermitian) :
    ∑ i, ∑ j, genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
        wirt 1 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) (h i j) =
      (∑ m, ∑ m', ((fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1))
          (fun k => edgeCount D N A η (E₁ k) (E₂ k) h) (Pi.single m' 1) : ℝ) : ℂ) *
        ((D : ℂ) * ∑ a : Fin D, ntr ((imRes (Matrix.of h + lam D N A) (edgePt η E₁ E₂ (m', 1)) -
            imRes (Matrix.of h + lam D N A) (edgePt η E₁ E₂ (m', 0))) *
          (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) *
          (imRes (Matrix.of h + lam D N A) (edgePt η E₁ E₂ (m, 1)) -
            imRes (Matrix.of h + lam D N A) (edgePt η E₁ E₂ (m, 0))) * Ea D N a))) +
      (∑ m, ((fderiv ℝ F (fun k => edgeCount D N A η (E₁ k) (E₂ k) h) (Pi.single m 1) : ℝ) : ℂ) *
        ((D : ℂ) ^ 2 * N *
          ((∑ a : Fin D, edgeYterm D N (Matrix.of h + lam D N A) (edgePt η E₁ E₂ (m, 1)) a *
              (ntr ((res (Matrix.of h + lam D N A) (edgePt η E₁ E₂ (m, 1)) -
                  MExt (lam D N A) (edgePt η E₁ E₂ (m, 1))) * Ea D N a) +
                ntr ((res (Matrix.of h + lam D N A) (star (edgePt η E₁ E₂ (m, 1))) -
                  MExt (lam D N A) (star (edgePt η E₁ E₂ (m, 1)))) * Ea D N a))) -
            (∑ a : Fin D, edgeYterm D N (Matrix.of h + lam D N A) (edgePt η E₁ E₂ (m, 0)) a *
              (ntr ((res (Matrix.of h + lam D N A) (edgePt η E₁ E₂ (m, 0)) -
                  MExt (lam D N A) (edgePt η E₁ E₂ (m, 0))) * Ea D N a) +
                ntr ((res (Matrix.of h + lam D N A) (star (edgePt η E₁ E₂ (m, 0))) -
                  MExt (lam D N A) (star (edgePt η E₁ E₂ (m, 0)))) * Ea D N a)))))) := by
  have hD1 : 1 ≤ D := by omega
  have hterm : ∀ i j : Idx D N, genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
      wirt 1 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) (h i j) =
      ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
        (genWt i j * wirt 1 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) (h i j)) :=
    fun i j => by ring
  simp only [hterm, CBnd_wirt11 A η hη F hF E₁ E₂ h hh]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.mul_sum]
    refine (CBnd_sum4 (fun i j (m m' : Fin n) =>
      ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
        (((fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1))
          (fun k => edgeCount D N A η (E₁ k) (E₂ k) h) (Pi.single m' 1) : ℝ) : ℂ) *
        (CBnd_Pm D N A η (E₁ m') (E₂ m') h j i * CBnd_Pm D N A η (E₁ m) (E₂ m) h i j)))).trans ?_
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    have e : ∀ i j : Idx D N, ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
        (((fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1))
          (fun k => edgeCount D N A η (E₁ k) (E₂ k) h) (Pi.single m' 1) : ℝ) : ℂ) *
        (CBnd_Pm D N A η (E₁ m') (E₂ m') h j i * CBnd_Pm D N A η (E₁ m) (E₂ m) h i j)) =
        ((fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1))
          (fun k => edgeCount D N A η (E₁ k) (E₂ k) h) (Pi.single m' 1) : ℝ) : ℂ) *
        (((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
          (CBnd_Pm D N A η (E₁ m') (E₂ m') h j i * CBnd_Pm D N A η (E₁ m) (E₂ m) h i j)) :=
      fun i j => by ring
    simp only [e, ← Finset.mul_sum]
    rw [CBnd_B1 hD1 (CBnd_Pm D N A η (E₁ m') (E₂ m') h) (CBnd_Pm D N A η (E₁ m) (E₂ m) h),
      CBnd_edgePt_one, CBnd_edgePt_zero, CBnd_edgePt_one, CBnd_edgePt_zero]
    rfl
  · simp only [Finset.mul_sum]
    refine (CBnd_sum3 (fun i j (m : Fin n) =>
      ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
        (((fderiv ℝ F (fun k => edgeCount D N A η (E₁ k) (E₂ k) h) (Pi.single m 1) : ℝ) : ℂ) *
        ((imRes (Matrix.of h + lam D N A) ((E₂ m : ℂ) + (η : ℂ) * Complex.I) i i *
            res (Matrix.of h + lam D N A) ((E₂ m : ℂ) + (η : ℂ) * Complex.I) j j +
          res (Matrix.of h + lam D N A) (star ((E₂ m : ℂ) + (η : ℂ) * Complex.I)) i i *
            imRes (Matrix.of h + lam D N A) ((E₂ m : ℂ) + (η : ℂ) * Complex.I) j j) -
          (imRes (Matrix.of h + lam D N A) ((E₁ m : ℂ) + (η : ℂ) * Complex.I) i i *
            res (Matrix.of h + lam D N A) ((E₁ m : ℂ) + (η : ℂ) * Complex.I) j j +
          res (Matrix.of h + lam D N A) (star ((E₁ m : ℂ) + (η : ℂ) * Complex.I)) i i *
            imRes (Matrix.of h + lam D N A) ((E₁ m : ℂ) + (η : ℂ) * Complex.I) j j))))).trans ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [CBnd_edgePt_one, CBnd_edgePt_zero]
    set X := Matrix.of h + lam D N A with hX
    set z₂ : ℂ := (E₂ m : ℂ) + (η : ℂ) * Complex.I with hz₂
    set z₁ : ℂ := (E₁ m : ℂ) + (η : ℂ) * Complex.I with hz₁
    have hz₂i : z₂.im ≠ 0 := by simp [hz₂, hη.ne']
    have hz₁i : z₁.im ≠ 0 := by simp [hz₁, hη.ne']
    set a1 : ℂ := ((fderiv ℝ F (fun k => edgeCount D N A η (E₁ k) (E₂ k) h) (Pi.single m 1) : ℝ) :
      ℂ) with ha1
    have step : ∑ i, ∑ j, ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
        (a1 * ((imRes X z₂ i i * res X z₂ j j + res X (star z₂) i i * imRes X z₂ j j) -
          (imRes X z₁ i i * res X z₁ j j + res X (star z₁) i i * imRes X z₁ j j))) =
        a1 * ((∑ i, ∑ j, ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
          (imRes X z₂ i i * res X z₂ j j + res X (star z₂) i i * imRes X z₂ j j)) -
          ∑ i, ∑ j, ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
          (imRes X z₁ i i * res X z₁ j j + res X (star z₁) i i * imRes X z₁ j j)) := by
      simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [step]
    rw [CBnd_Q hD hN A z₂ hz₂i (imRes X z₂) (res X z₂) (res X (star z₂)),
      CBnd_Q hD hN A z₁ hz₁i (imRes X z₁) (res X z₁) (res X (star z₁))]
    unfold edgeYterm
    simp only [mul_add, Finset.sum_add_distrib]
    ring


/-- The triangle inequality for `Σ_a Y_a (⟨(G - M) E_a⟩ + ⟨(G* - M*) E_a⟩)`, the right side of
`CBnd_Q` with the factors of the bound before (4.16) [eq:roughXY]. -/
private lemma CBnd_Q_norm (X Λ : Matrix (Idx D N) (Idx D N) ℂ) (z : ℂ) :
    ‖∑ a : Fin D, edgeYterm D N X z a * (ntr ((res X z - MExt Λ z) * Ea D N a) +
        ntr ((res X (star z) - MExt Λ (star z)) * Ea D N a))‖ ≤
      ∑ a : Fin D, ‖edgeYterm D N X z a‖ * (‖ntr ((res X z - MExt Λ z) * Ea D N a)‖ +
        ‖ntr ((res X (star z) - MExt Λ (star z)) * Ea D N a)‖) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)

end F2

/-- `ℱ₂` in block traces, after the subtraction of `M` (proof of Lemma 4.3 [rescomY], before
(4.16) [eq:roughXY]): for a Hermitian array the integrand of `entryF2` is at most
`K B_F (D Σ |X(i, j; a)| + D² N Σ |⟨Im G_i (D⁻¹ - E_a)⟩| (|⟨(G - M)(z_i) E_a⟩| +
|⟨(G - M)(z̄_i) E_a⟩|))`, with `B_F` bounding the first two derivatives of `F` at `A`; `D ≥ 2`,
`N ≥ 1`. -/
theorem entryF2_integrand_le (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℕ, 2 ≤ D → ∀ N : ℕ, 1 ≤ N → ∀ (A : Matrix (Fin N) (Fin N) ℂ)
      (η : ℝ), 0 < η → ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ F → ∀ (E₁ E₂ : Fin n → ℝ)
      (h : Idx D N → Idx D N → ℂ), (Matrix.of h).IsHermitian → ∀ BF : ℝ,
      (∀ k : ℕ, 1 ≤ k → k ≤ 2 →
        ‖iteratedFDeriv ℝ k F (fun m => edgeCount D N A η (E₁ m) (E₂ m) h)‖ ≤ BF) →
      ‖∑ i, ∑ j, genWt i j * ((((D * N : ℕ) : ℂ))⁻¹ - (varProf D N 1 i j : ℂ)) *
          wirt 1 1 (fun w => (edgeFn D N A η F E₁ E₂ (setEntry h i j w) : ℂ)) (h i j)‖ ≤
        K * BF * ((D : ℝ) * (∑ r₁ : Fin n × Fin 2, ∑ r₂ : Fin n × Fin 2, ∑ a : Fin D,
            ‖edgeXterm D N (Matrix.of h + lam D N A) (edgePt η E₁ E₂ r₁)
              (edgePt η E₁ E₂ r₂) a‖) +
          (D : ℝ) ^ 2 * N * (∑ r : Fin n × Fin 2, ∑ a : Fin D,
            ‖edgeYterm D N (Matrix.of h + lam D N A) (edgePt η E₁ E₂ r) a‖ *
              (‖ntr ((res (Matrix.of h + lam D N A) (edgePt η E₁ E₂ r) -
                  MExt (lam D N A) (edgePt η E₁ E₂ r)) * Ea D N a)‖ +
                ‖ntr ((res (Matrix.of h + lam D N A) (star (edgePt η E₁ E₂ r)) -
                  MExt (lam D N A) (star (edgePt η E₁ E₂ r))) * Ea D N a)‖))) := by
  refine ⟨1, one_pos, ?_⟩
  intro D hD N hN A η hη F hF E₁ E₂ h hh BF hBF
  rw [CBnd_F2_eq hD hN A η hη F hF E₁ E₂ h hh]
  set X : Matrix (Idx D N) (Idx D N) ℂ := Matrix.of h + lam D N A with hX
  set x : Fin n → ℝ := fun k => edgeCount D N A η (E₁ k) (E₂ k) h with hx
  have hB1 := hBF 1 le_rfl (by norm_num)
  have hB2 := hBF 2 (by norm_num) le_rfl
  have hBF0 : 0 ≤ BF := (norm_nonneg _).trans hB1
  have hDn : ‖(D : ℂ)‖ = D := by simp
  -- the first part
  have hT1 : ‖∑ m, ∑ m', ((fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1)) x
      (Pi.single m' 1) : ℝ) : ℂ) * ((D : ℂ) * ∑ a : Fin D, ntr ((imRes X (edgePt η E₁ E₂ (m', 1)) -
            imRes X (edgePt η E₁ E₂ (m', 0))) *
          (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) *
          (imRes X (edgePt η E₁ E₂ (m, 1)) - imRes X (edgePt η E₁ E₂ (m, 0))) * Ea D N a))‖ ≤
      BF * ((D : ℝ) * ∑ r₁ : Fin n × Fin 2, ∑ r₂ : Fin n × Fin 2, ∑ a : Fin D,
        ‖edgeXterm D N X (edgePt η E₁ E₂ r₁) (edgePt η E₁ E₂ r₂) a‖) := by
    have ha2 : ∀ m m' : Fin n, ‖((fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ F y (Pi.single m 1)) x
        (Pi.single m' 1) : ℝ) : ℂ)‖ ≤ BF := by
      intro m m'
      rw [Complex.norm_real]
      exact CBnd_F2_le F hF x BF hB2 m m'
    have hX4 : ∀ (m m' : Fin n) (a : Fin D),
        ‖ntr ((imRes X (edgePt η E₁ E₂ (m', 1)) - imRes X (edgePt η E₁ E₂ (m', 0))) *
          (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) *
          (imRes X (edgePt η E₁ E₂ (m, 1)) - imRes X (edgePt η E₁ E₂ (m, 0))) * Ea D N a)‖ ≤
        ∑ e' : Fin 2, ∑ e : Fin 2,
          ‖edgeXterm D N X (edgePt η E₁ E₂ (m', e')) (edgePt η E₁ E₂ (m, e)) a‖ := by
      intro m m' a
      refine (CBnd_ntr_diff _ _ _ _ _ _).trans ?_
      simp only [Fin.sum_univ_two, edgeXterm]
      linarith
    have hsum : ∀ m m' : Fin n,
        ∑ a : Fin D, ‖ntr ((imRes X (edgePt η E₁ E₂ (m', 1)) - imRes X (edgePt η E₁ E₂ (m', 0))) *
          (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) *
          (imRes X (edgePt η E₁ E₂ (m, 1)) - imRes X (edgePt η E₁ E₂ (m, 0))) * Ea D N a)‖ ≤
        ∑ e' : Fin 2, ∑ e : Fin 2, ∑ a : Fin D,
          ‖edgeXterm D N X (edgePt η E₁ E₂ (m', e')) (edgePt η E₁ E₂ (m, e)) a‖ := by
      intro m m'
      calc _ ≤ ∑ a : Fin D, ∑ e' : Fin 2, ∑ e : Fin 2,
            ‖edgeXterm D N X (edgePt η E₁ E₂ (m', e')) (edgePt η E₁ E₂ (m, e)) a‖ :=
            Finset.sum_le_sum fun a _ => hX4 m m' a
        _ = _ := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun e' _ => Finset.sum_comm
    calc _ ≤ ∑ m : Fin n, ∑ m' : Fin n, BF * ((D : ℝ) * ∑ e' : Fin 2, ∑ e : Fin 2, ∑ a : Fin D,
          ‖edgeXterm D N X (edgePt η E₁ E₂ (m', e')) (edgePt η E₁ E₂ (m, e)) a‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun m' _ => ?_))
          rw [norm_mul, norm_mul, hDn]
          refine mul_le_mul (ha2 m m') ?_ (by positivity) hBF0
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (hsum m m')) (Nat.cast_nonneg _)
      _ = _ := by
          rw [CBnd_sumX (fun r₁ r₂ a =>
            ‖edgeXterm D N X (edgePt η E₁ E₂ r₁) (edgePt η E₁ E₂ r₂) a‖)]
          simp only [Finset.mul_sum]
  -- the second part
  have hT2 : ‖∑ m, ((fderiv ℝ F x (Pi.single m 1) : ℝ) : ℂ) *
        ((D : ℂ) ^ 2 * N *
          ((∑ a : Fin D, edgeYterm D N X (edgePt η E₁ E₂ (m, 1)) a *
              (ntr ((res X (edgePt η E₁ E₂ (m, 1)) - MExt (lam D N A) (edgePt η E₁ E₂ (m, 1))) *
                  Ea D N a) +
                ntr ((res X (star (edgePt η E₁ E₂ (m, 1))) -
                  MExt (lam D N A) (star (edgePt η E₁ E₂ (m, 1)))) * Ea D N a))) -
            (∑ a : Fin D, edgeYterm D N X (edgePt η E₁ E₂ (m, 0)) a *
              (ntr ((res X (edgePt η E₁ E₂ (m, 0)) - MExt (lam D N A) (edgePt η E₁ E₂ (m, 0))) *
                  Ea D N a) +
                ntr ((res X (star (edgePt η E₁ E₂ (m, 0))) -
                  MExt (lam D N A) (star (edgePt η E₁ E₂ (m, 0)))) * Ea D N a)))))‖ ≤
      BF * ((D : ℝ) ^ 2 * N * ∑ r : Fin n × Fin 2, ∑ a : Fin D,
        ‖edgeYterm D N X (edgePt η E₁ E₂ r) a‖ *
          (‖ntr ((res X (edgePt η E₁ E₂ r) - MExt (lam D N A) (edgePt η E₁ E₂ r)) * Ea D N a)‖ +
            ‖ntr ((res X (star (edgePt η E₁ E₂ r)) - MExt (lam D N A) (star (edgePt η E₁ E₂ r))) *
              Ea D N a)‖)) := by
    have ha1 : ∀ m : Fin n, ‖((fderiv ℝ F x (Pi.single m 1) : ℝ) : ℂ)‖ ≤ BF := by
      intro m
      rw [Complex.norm_real]
      exact CBnd_F1_le F x BF hB1 m
    have hD2 : ‖(D : ℂ) ^ 2 * N‖ = (D : ℝ) ^ 2 * N := by simp
    set W : Fin n × Fin 2 → ℝ := fun r => ∑ a : Fin D,
      ‖edgeYterm D N X (edgePt η E₁ E₂ r) a‖ *
        (‖ntr ((res X (edgePt η E₁ E₂ r) - MExt (lam D N A) (edgePt η E₁ E₂ r)) * Ea D N a)‖ +
          ‖ntr ((res X (star (edgePt η E₁ E₂ r)) - MExt (lam D N A) (star (edgePt η E₁ E₂ r))) *
            Ea D N a)‖) with hW
    have hW0 : ∀ r, 0 ≤ W r := fun r => Finset.sum_nonneg fun a _ => by positivity
    calc _ ≤ ∑ m : Fin n, BF * ((D : ℝ) ^ 2 * N * (W (m, 1) + W (m, 0))) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
          rw [norm_mul, norm_mul, hD2]
          refine mul_le_mul (ha1 m) ?_ (by positivity) hBF0
          refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (by positivity)
          exact add_le_add (CBnd_Q_norm X (lam D N A) _) (CBnd_Q_norm X (lam D N A) _)
      _ = _ := by
          rw [Fintype.sum_prod_type]
          simp only [Fin.sum_univ_two, ← Finset.mul_sum]
          exact congrArg _ (congrArg _ (Finset.sum_congr rfl fun m _ => add_comm _ _))
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hT1 hT2
    _ = _ := by ring

/-- (4.16) [eq:roughXY] without `F''`: for Hermitian `X`,
`|X(i, j; a)| ≤ (⟨Im G(z₁)⟩ ⟨Im G(z₂)⟩ / (Im z₁ Im z₂))^{1/2}`, by Cauchy–Schwarz and
`⟨(Im G)²⟩ ≤ ⟨Im G⟩ / Im z`. -/
theorem edgeXterm_rough_le {D N : ℕ} (X : Matrix (Idx D N) (Idx D N) ℂ) (hX : X.IsHermitian)
    (z₁ z₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) (a : Fin D) :
    ‖edgeXterm D N X z₁ z₂ a‖ ≤
      Real.sqrt ((ntr (res X z₁)).im / z₁.im * ((ntr (res X z₂)).im / z₂.im)) := by
  set c : ℝ := ((Fintype.card (Idx D N) : ℝ))⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hcard : ((Fintype.card (Idx D N) : ℂ))⁻¹ = (c : ℂ) := by simp [hc]
  have hntr : ∀ B : Matrix (Idx D N) (Idx D N) ℂ, ntr B = (c : ℂ) * B.trace := by
    intro B; simp only [ntr, hcard]
  have hntr_im : ∀ z : ℂ, (ntr (res X z)).im = c * (Matrix.trace (res X z)).im := by
    intro z; rw [hntr]; simp
  set P := imRes X z₁ with hP
  set Q := imRes X z₂ with hQ
  have hB : ((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a =
      Matrix.diagonal (fun p : Idx D N => ((D : ℂ))⁻¹ - if p.1 = a then 1 else 0) := by
    rw [Ea, Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  have hbd : ∀ p : Idx D N, ‖((D : ℂ))⁻¹ - if p.1 = a then (1 : ℂ) else 0‖ ≤ 1 := by
    intro p
    have hD : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro h0; subst h0; exact a.elim0)
    have hDi : ((D : ℂ))⁻¹ = (((D : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    have hDi0 : 0 ≤ (D : ℝ)⁻¹ := by positivity
    have hDi1 : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
    split_ifs
    · rw [hDi, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_le]
      constructor <;> linarith
    · rw [hDi, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hDi0]
      exact hDi1
  have hbE : ∀ p : Idx D N, ‖(if p.1 = a then (1 : ℂ) else 0)‖ ≤ 1 := by
    intro p; split_ifs <;> simp
  have hE : Ea D N a = Matrix.diagonal (fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0) := rfl
  have e1 : P * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) * Q * Ea D N a =
      (P * Matrix.diagonal (fun p : Idx D N => ((D : ℂ))⁻¹ - if p.1 = a then 1 else 0)) *
        (Q * Matrix.diagonal (fun p : Idx D N => if p.1 = a then (1 : ℂ) else 0)) := by
    rw [hB, ← hE]; simp only [Matrix.mul_assoc]
  have hPf := CBnd_fro_imRes X hX z₁ hz₁
  have hQf := CBnd_fro_imRes X hX z₂ hz₂
  have hP0 : 0 ≤ (Matrix.trace (res X z₁)).im / z₁.im :=
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity).trans hPf
  have hQ0 : 0 ≤ (Matrix.trace (res X z₂)).im / z₂.im :=
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity).trans hQf
  have hmain : ‖(P * (((D : ℂ))⁻¹ • (1 : Matrix (Idx D N) (Idx D N) ℂ) - Ea D N a) * Q *
      Ea D N a).trace‖ ≤ Real.sqrt ((Matrix.trace (res X z₁)).im / z₁.im) *
        Real.sqrt ((Matrix.trace (res X z₂)).im / z₂.im) := by
    rw [e1]
    refine (CBnd_trace_mul_le _ _).trans ?_
    exact mul_le_mul
      (Real.sqrt_le_sqrt ((CBnd_fro_mul_diag P _ hbd).trans hPf))
      (Real.sqrt_le_sqrt ((CBnd_fro_mul_diag Q _ hbE).trans hQf)) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  unfold edgeXterm
  rw [hntr, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0, hntr_im, hntr_im]
  have e2 : c * (Matrix.trace (res X z₁)).im / z₁.im * (c * (Matrix.trace (res X z₂)).im / z₂.im) =
      c ^ 2 * ((Matrix.trace (res X z₁)).im / z₁.im * ((Matrix.trace (res X z₂)).im / z₂.im)) := by
    ring
  rw [e2, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0]
  rw [Real.sqrt_mul hP0]
  exact mul_le_mul_of_nonneg_left hmain hc0

end RBMTransitionEdge

end
