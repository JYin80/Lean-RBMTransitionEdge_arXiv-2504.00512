module

public import RBMTransitionEdge.Det.Block
public import RBMTransitionEdge.LocalLaw.Class

@[expose] public section

/-!
# The characteristic flow

The characteristic flow of Lemma 3.5 [lem_prop_flow] in closed form,
`z_s = e^{-s/2}(z + m) - e^{s/2}m`, its derivative, (3.14) [t_eta] and the flow of `M̂`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The characteristic flow (3.10) [eq:deterflow] in closed form, `s = t - t₀`:
`z_s = e^{-s/2} (z + m) - e^{s/2} m` with `m = m(z, Λ)`, for `Λ_s = e^{-s/2} Λ`. -/
def charFlowZ {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ) (s : ℝ) : ℂ :=
  (Real.exp (-s / 2) : ℂ) * (z + mExt Λ z) - (Real.exp (s / 2) : ℂ) * mExt Λ z

/-- Auxiliary: `m(z, Λ) = mSol Λ z` for `Im z > 0` (Definition 2.7 [defn_Mm]). -/
private lemma Flow_mExt_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : 0 < z.im) : mExt Λ z = mSol Λ z := by
  simp [mExt, hz]

/-- Auxiliary: `m(z, Λ) = conj (mSol Λ z̄)` for `Im z < 0` (Definition 2.7 [defn_Mm]). -/
private lemma Flow_mExt_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : z.im < 0) : mExt Λ z = star (mSol Λ (star z)) := by
  have h : ¬ 0 < z.im := not_lt.2 hz.le
  simp [mExt, h, hz]

/-- Auxiliary: `Im m > 0` for `m = m(z, Λ)` at `Im z > 0` ((2.16) [self_m], Definition 2.7). -/
private lemma Flow_im_m_pos {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) : 0 < (mExt Λ z).im := by
  obtain ⟨-, -, h⟩ := MExt_spec Λ hΛ z hz.ne'
  by_contra hneg
  exact absurd h (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hz.le))

/-- Auxiliary: the imaginary part of the closed form (3.10) [eq:deterflow]. -/
private lemma Flow_im {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ) (s : ℝ) :
    (charFlowZ Λ z s).im = Real.exp (-s / 2) * (z.im + (mExt Λ z).im) -
      Real.exp (s / 2) * (mExt Λ z).im := by
  simp only [charFlowZ, Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]

/-- Auxiliary: `exp(s/2) = exp(-s/2) exp(s)` and `exp(-s/2) exp(s/2) = 1`. -/
private lemma Flow_exp (s : ℝ) :
    Real.exp (s / 2) = Real.exp (-s / 2) * Real.exp s ∧
      Real.exp (-s / 2) * Real.exp (s / 2) = 1 := by
  refine ⟨by rw [← Real.exp_add]; ring_nf, ?_⟩
  rw [← Real.exp_add, show -s / 2 + s / 2 = 0 by ring, Real.exp_zero]

/-- Auxiliary: `Im z_s > 0` exactly in the range `s < log(1 + η/Im m)` of Lemma 3.5
[lem_prop_flow]. -/
private lemma Flow_im_pos {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s : ℝ)
    (hs : s < Real.log (1 + z.im / (mExt Λ z).im)) : 0 < (charFlowZ Λ z s).im := by
  have hm := Flow_im_m_pos Λ hΛ z hz
  have hq : 0 < 1 + z.im / (mExt Λ z).im := by have := div_pos hz hm; linarith
  have h1 : Real.exp s < 1 + z.im / (mExt Λ z).im := (Real.lt_log_iff_exp_lt hq).1 hs
  have h2 : Real.exp s * (mExt Λ z).im < z.im + (mExt Λ z).im := by
    have := mul_lt_mul_of_pos_right h1 hm
    rwa [add_mul, div_mul_cancel₀ _ hm.ne', one_mul, add_comm] at this
  rw [Flow_im, (Flow_exp s).1]
  have hc := Real.exp_pos (-s / 2)
  nlinarith [mul_pos hc (sub_pos.2 h2)]

/-- Auxiliary: a real scalar multiple of a Hermitian matrix is Hermitian. -/
private lemma Flow_herm {ι : Type*} (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (c : ℝ) :
    (((c : ℝ) : ℂ) • Λ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hΛ.eq]
  simp

/-- Auxiliary: `⟨c B⟩ = c ⟨B⟩`. -/
private lemma Flow_ntr_smul {ι : Type*} [Fintype ι] (c : ℂ) (B : Matrix ι ι ℂ) :
    ntr (c • B) = c * ntr B := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]
  ring

/-- Lemma 3.5 [lem_prop_flow], (3.15) [devM] in integrated form: for `s < t_c - t₀`,
`t_c - t₀ = log(1 + η/Im m)`, the flow stays in the upper half plane, `M_s = e^{s/2} M` and
`m_s = e^{s/2} m`; the time `s` may be negative (backward flow). -/
theorem charFlow_M {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s : ℝ)
    (hs : s < Real.log (1 + z.im / (mExt Λ z).im)) :
    0 < (charFlowZ Λ z s).im ∧
      MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s) =
        ((Real.exp (s / 2) : ℝ) : ℂ) • MExt Λ z ∧
      mExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s) =
        (Real.exp (s / 2) : ℂ) * mExt Λ z := by
  have hm := Flow_im_m_pos Λ hΛ z hz
  have hpos := Flow_im_pos Λ hΛ z hz s hs
  obtain ⟨hmM, hAM, -⟩ := MExt_spec Λ hΛ z hz.ne'
  have hce : ((Real.exp (-s / 2) : ℝ) : ℂ) * ((Real.exp (s / 2) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, (Flow_exp s).2, Complex.ofReal_one]
  have hsum : charFlowZ Λ z s + ((Real.exp (s / 2) : ℝ) : ℂ) * mExt Λ z =
      ((Real.exp (-s / 2) : ℝ) : ℂ) * (z + mExt Λ z) := by
    simp only [charFlowZ]; ring
  have hinv : (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ -
      (charFlowZ Λ z s + ((Real.exp (s / 2) : ℝ) : ℂ) * mExt Λ z) • (1 : Matrix ι ι ℂ))⁻¹ =
      ((Real.exp (s / 2) : ℝ) : ℂ) • MExt Λ z := by
    apply Matrix.inv_eq_right_inv
    rw [hsum, mul_smul, ← smul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hce, one_smul]
    exact hAM
  have hΛs := Flow_herm Λ hΛ (Real.exp (-s / 2))
  obtain ⟨w, -, huniq⟩ := mSol_existsUnique _ hΛs (charFlowZ Λ z s) hpos
  have hmt_sol : 0 < (((Real.exp (s / 2) : ℝ) : ℂ) * mExt Λ z).im ∧
      ((Real.exp (s / 2) : ℝ) : ℂ) * mExt Λ z = ntr ((((Real.exp (-s / 2) : ℝ) : ℂ) • Λ -
        (charFlowZ Λ z s + ((Real.exp (s / 2) : ℝ) : ℂ) * mExt Λ z) •
          (1 : Matrix ι ι ℂ))⁻¹) := by
    refine ⟨?_, ?_⟩
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_pos (Real.exp_pos (s / 2)) hm
    
    rw [hinv, Flow_ntr_smul, ← hmM]
  have hmsol := mSol_spec _ hΛs (charFlowZ Λ z s) hpos
  have h1 : mSol (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s) = w := by
    refine huniq _ ⟨hmsol.1, ?_⟩
    have := hmsol.2.1
    unfold MSol at this
    exact this
  have h2 : ((Real.exp (s / 2) : ℝ) : ℂ) * mExt Λ z = w := huniq _ hmt_sol
  have hmt : mExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s) =
      ((Real.exp (s / 2) : ℝ) : ℂ) * mExt Λ z := by
    rw [Flow_mExt_pos _ _ hpos, h1, h2]
  refine ⟨hpos, ?_, hmt⟩
  unfold MExt
  rw [hmt]
  exact hinv

/-- (3.10) [eq:deterflow] holds for the closed form: `dz_s/ds = -z_s/2 - m_s`. -/
theorem charFlow_deriv {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s : ℝ)
    (hs : s < Real.log (1 + z.im / (mExt Λ z).im)) :
    HasDerivAt (charFlowZ Λ z) (-(charFlowZ Λ z s) / 2 -
      mExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s)) s := by
  have hM := charFlow_M Λ hΛ z hz s hs
  rw [hM.2.2]
  have hz2 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ((Real.exp (x * y) : ℝ) : ℂ))
      ((x : ℂ) * ((Real.exp (x * s) : ℝ) : ℂ)) s := by
    intro x
    have h : HasDerivAt (fun y : ℝ => Real.exp (x * y)) (Real.exp (x * s) * x) s := by
      simpa using ((hasDerivAt_id s).const_mul x).exp
    simpa [mul_comm] using h.ofReal_comp
  have h1 := (hz2 (-1 / 2)).mul_const (z + mExt Λ z)
  have h2 := (hz2 (1 / 2)).mul_const (mExt Λ z)
  have h3 := h1.sub h2
  have e1 : ((fun y : ℝ => ((Real.exp (-1 / 2 * y) : ℝ) : ℂ) * (z + mExt Λ z)) -
      fun y : ℝ => ((Real.exp (1 / 2 * y) : ℝ) : ℂ) * mExt Λ z) = charFlowZ Λ z := by
    funext y
    simp only [Pi.sub_apply, charFlowZ]
    have a1 : -y / 2 = -1 / 2 * y := by ring
    have a2 : y / 2 = 1 / 2 * y := by ring
    rw [a1, a2]
  rw [e1] at h3
  convert h3 using 1
  have a1 : -s / 2 = -1 / 2 * s := by ring
  have a2 : s / 2 = 1 / 2 * s := by ring
  simp only [charFlowZ, a1, a2]
  push_cast
  ring

/-- (3.14) [t_eta] of Lemma 3.5 [lem_prop_flow] without error term:
`η_s / Im m_s = e^{(t_c - t₀) - s} - 1`. -/
theorem charFlow_teta {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s : ℝ)
    (hs : s < Real.log (1 + z.im / (mExt Λ z).im)) :
    (charFlowZ Λ z s).im / (mExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z s)).im =
      Real.exp (Real.log (1 + z.im / (mExt Λ z).im) - s) - 1 := by
  have hM := charFlow_M Λ hΛ z hz s hs
  have hm := Flow_im_m_pos Λ hΛ z hz
  have hq : 0 < 1 + z.im / (mExt Λ z).im := by have := div_pos hz hm; linarith
  rw [hM.2.2, Flow_im, Real.exp_sub, Real.exp_log hq]
  have hc : Real.exp (-s / 2) = (Real.exp (s / 2))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  have hs2 : Real.exp s = Real.exp (s / 2) * Real.exp (s / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hpe := Real.exp_pos (s / 2)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [hc, hs2]
  field_simp
  ring

/-- The conjugate flow of Lemma 3.5 [lem_prop_flow], (3.17) [Conflow]: the closed form started
at `z̄` is the conjugate of the closed form started at `z`. -/
theorem charFlowZ_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) (z : ℂ)
    (hz : 0 < z.im) (s : ℝ) :
    charFlowZ Λ (star z) s = star (charFlowZ Λ z s) := by
  have h : mExt Λ (star z) = star (mExt Λ z) := by
    have hz' : (star z).im < 0 := by simpa using hz
    rw [Flow_mExt_neg _ _ hz', Flow_mExt_pos _ _ hz, star_star]
  unfold charFlowZ
  rw [h]
  simp only [star_add, star_mul', star_sub, Complex.star_def, Complex.conj_ofReal]

/-- (3.18) [eq:whMK], first equation, in integrated form: `M̂_s = e^s M̂` along the flow, for
`z₁, z₂ ∈ {z, z̄}`. -/
theorem Mhat_flow {D N : ℕ} [NeZero D] [NeZero N] (Λ : Matrix (Idx D N) (Idx D N) ℂ)
    (hΛ : Λ.IsHermitian) (z : ℂ) (hz : 0 < z.im) (s : ℝ)
    (hs : s < Real.log (1 + z.im / (mExt Λ z).im)) (z₁ z₂ : ℂ)
    (h₁ : z₁ = z ∨ z₁ = star z) (h₂ : z₂ = z ∨ z₂ = star z) :
    Mhat (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ z₁ s) (charFlowZ Λ z₂ s) =
      ((Real.exp s : ℝ) : ℂ) • Mhat Λ z₁ z₂ := by
  have hN : Nonempty (Idx D N) := ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩,
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩)⟩
  have hΛs := Flow_herm Λ hΛ (Real.exp (-s / 2))
  obtain ⟨hpos, hMz, -⟩ := charFlow_M Λ hΛ z hz s hs
  have hnz : (charFlowZ Λ z s).im ≠ 0 := hpos.ne'
  have hcj := charFlowZ_conj Λ z hz s
  have key : ∀ w : ℂ, (w = z ∨ w = star z) →
      MExt (((Real.exp (-s / 2) : ℝ) : ℂ) • Λ) (charFlowZ Λ w s) =
        ((Real.exp (s / 2) : ℝ) : ℂ) • MExt Λ w := by
    rintro w (rfl | rfl)
    · exact hMz
    · rw [hcj, (mExt_conj _ hΛs _ hnz).2, hMz, (mExt_conj Λ hΛ z hz.ne').2,
        Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  have hexp : ((Real.exp (s / 2) : ℝ) : ℂ) * ((Real.exp (s / 2) : ℝ) : ℂ) =
      ((Real.exp s : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; ring_nf
  funext a b
  simp only [Mhat, key z₁ h₁, key z₂ h₂, Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Flow_ntr_smul]
  linear_combination (((D : ℂ)) * ntr (MExt Λ z₁ * Ea D N a * MExt Λ z₂ * Ea D N b)) * hexp

end RBMTransitionEdge

end
