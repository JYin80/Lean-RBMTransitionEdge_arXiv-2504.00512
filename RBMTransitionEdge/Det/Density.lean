module

public import RBMTransitionEdge.Model.Basic
public import RBMTransitionEdge.Model.Deterministic
public import RBMTransitionEdge.Det.Core
public import RBMTransitionEdge.Det.Edge

@[expose] public section

/-!
# The density ρ_N: Stieltjes representation, the case Λ = 0, continuity in t, (A.4), (2.21)

`m` is the Stieltjes transform of the probability density `ρ_N` of (2.19) [eq:density_rhoN]; the case `Λ = 0`;
continuity of the edges, quantiles and `m` along a continuous family (Definition 2.10 [def_moving_Lambda]); (A.4)
[equation_E_in_spectrum]; the quantile bounds (2.21) [eq:kappa_gamma_k].
-/

open MeasureTheory Matrix Filter Topology

noncomputable section
open Classical

universe u v

namespace RBMTransitionEdge

section Density_S1
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma Density_norm_apply_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  set T := toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  have h1 : ‖T (WithLp.toLp 2 (Pi.single j (1:ℂ)))‖ ≤ ‖T‖ * 1 := by
    grw [T.le_opNorm]; simp
  rw [toEuclideanCLM_toLp] at h1
  have h2 : ‖(WithLp.toLp 2 (A *ᵥ Pi.single j (1:ℂ)) : EuclideanSpace ℂ ι) i‖ ≤
      ‖(WithLp.toLp 2 (A *ᵥ Pi.single j (1:ℂ)) : EuclideanSpace ℂ ι)‖ := PiLp.norm_apply_le _ i
  have h3 : (WithLp.toLp 2 (A *ᵥ Pi.single j (1:ℂ)) : EuclideanSpace ℂ ι) i = A i j := by
    simp
  rw [h3] at h2
  have := h2.trans h1
  rw [mul_one] at this
  exact this


private lemma Density_norm_ntr_le [Nonempty ι] (B : Matrix ι ι ℂ) : ‖ntr B‖ ≤ ‖B‖ := by
  unfold ntr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [inv_mul_le_iff₀ hn]
  calc ‖B.trace‖ ≤ ∑ i, ‖B i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖B‖ := Finset.sum_le_sum fun i _ => Density_norm_apply_le B i i
    _ = _ := by simp

private lemma Density_ntr_conjTranspose (B : Matrix ι ι ℂ) : ntr Bᴴ = star (ntr B) := by
  unfold ntr
  rw [Matrix.trace_conjTranspose, star_mul', star_inv₀, star_natCast, mul_comm]

private lemma Density_ntr_mul_self (M : Matrix ι ι ℂ) :
    ntr (M * Mᴴ) = (((Fintype.card ι : ℝ)⁻¹ * ∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) := by
  unfold ntr
  have : (M * Mᴴ).trace = ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [this]
  push_cast
  rfl

private lemma Density_ntr_mul_self_facts [Nonempty ι] (M : Matrix ι ι ℂ) :
    ∃ t : ℝ, 0 ≤ t ∧ ntr (M * Mᴴ) = (t : ℂ) ∧ (M ≠ 0 → 0 < t) ∧ t ≤ ‖M‖ ^ 2 := by
  refine ⟨(Fintype.card ι : ℝ)⁻¹ * ∑ i, ∑ j, ‖M i j‖ ^ 2, by positivity, Density_ntr_mul_self M, ?_, ?_⟩
  · intro hM
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    apply mul_pos (inv_pos.2 hn)
    obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hM (by ext i j; exact h i j)
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i))
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hij) 2) (Finset.single_le_sum (f := fun j => ‖M i j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ j))
  · have h1 := Density_norm_ntr_le (M * Mᴴ)
    rw [Density_ntr_mul_self M] at h1
    have h2 : ‖M * Mᴴ‖ ≤ ‖M‖ ^ 2 := by
      rw [sq]
      refine (norm_mul_le _ _).trans ?_
      rw [Matrix.l2_opNorm_conjTranspose]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h1
    exact h1.trans h2

private lemma Density_inv_norm_le [Nonempty ι] {Λ M : Matrix ι ι ℂ} {ζ : ℂ} {ℓ : ℝ} (hΛ : ‖Λ‖ ≤ ℓ)
    (hM : (Λ - ζ • (1 : Matrix ι ι ℂ)) * M = 1) : (‖ζ‖ - ℓ) * ‖M‖ ≤ 1 := by
  have h1 : ζ • M = Λ * M - 1 := by
    have : Λ * M - ζ • M = 1 := by rwa [sub_mul, smul_mul_assoc, one_mul] at hM
    rw [← this]; abel
  have h2 : ‖ζ‖ * ‖M‖ ≤ ℓ * ‖M‖ + 1 := by
    calc ‖ζ‖ * ‖M‖ = ‖ζ • M‖ := (norm_smul _ _).symm
      _ = ‖Λ * M - 1‖ := by rw [h1]
      _ ≤ ‖Λ * M‖ + ‖(1 : Matrix ι ι ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖Λ‖ * ‖M‖ + 1 := by rw [norm_one]; gcongr; exact norm_mul_le _ _
      _ ≤ ℓ * ‖M‖ + 1 := by gcongr
  nlinarith

private lemma Density_im_identity {Λ M : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) {ζ : ℂ}
    (hM : (Λ - ζ • (1 : Matrix ι ι ℂ)) * M = 1) :
    M - Mᴴ = (2 * Complex.I * (ζ.im : ℂ)) • (M * Mᴴ) := by
  have hM' : M * (Λ - ζ • (1 : Matrix ι ι ℂ)) = 1 := mul_eq_one_comm.1 hM
  have hMt : (Λ - star ζ • (1 : Matrix ι ι ℂ)) * Mᴴ = 1 := by
    have := congrArg Matrix.conjTranspose hM'
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hΛ.eq] at this
    exact this
  have e1 : M * (Λ - star ζ • (1 : Matrix ι ι ℂ)) * Mᴴ = M := by rw [mul_assoc, hMt, mul_one]
  have e2 : M * (Λ - ζ • (1 : Matrix ι ι ℂ)) * Mᴴ = Mᴴ := by rw [hM', one_mul]
  have e3 : M * (Λ - star ζ • (1 : Matrix ι ι ℂ)) * Mᴴ - M * (Λ - ζ • (1 : Matrix ι ι ℂ)) * Mᴴ =
      (ζ - star ζ) • (M * Mᴴ) := by
    rw [← sub_mul, ← mul_sub]
    have : Λ - star ζ • (1 : Matrix ι ι ℂ) - (Λ - ζ • (1 : Matrix ι ι ℂ)) = (ζ - star ζ) • 1 := by
      rw [sub_smul]; abel
    rw [this, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [e1, e2] at e3
  rw [e3]
  congr 1
  rw [Complex.star_def, Complex.sub_conj]
  push_cast
  ring

end Density_S1

section Density_S2
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- the boundary value of `mExt` as a limit from the upper half plane. -/
private lemma Density_tendsto_mExt {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (x : ℝ) :
    Tendsto (fun η : ℝ => mExt Λ ((x : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
      (𝓝 (mExt Λ x)) := by
  have hc := (mExt_boundary Λ hΛ hℓ).1
  have h1 : ContinuousWithinAt (mExt Λ) {z : ℂ | 0 ≤ z.im} (x : ℂ) :=
    hc (x : ℂ) (by simp)
  refine h1.tendsto.comp ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have : Tendsto (fun η : ℝ => (x : ℂ) + (η : ℂ) * Complex.I) (𝓝 0)
        (𝓝 ((x : ℂ) + (0 : ℂ) * Complex.I)) := by
      apply Continuous.tendsto
      fun_prop
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with η hη
    simp at hη ⊢
    exact hη.le

private lemma Density_mExt_of_pos {Λ : Matrix ι ι ℂ} {z : ℂ} (hz : 0 < z.im) : mExt Λ z = mSol Λ z := by
  simp [mExt, hz]

/-- `ρ_N(x) = π⁻¹ Im m(x)`, with `m` the boundary value. -/
private lemma Density_rho_eq {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (x : ℝ) :
    rho Λ x = (mExt Λ x).im / Real.pi := by
  unfold rho
  congr 1
  have h1 := (Complex.continuous_im.tendsto _).comp (Density_tendsto_mExt hΛ hℓ x)
  refine Filter.Tendsto.limUnder_eq (h1.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with η hη
  have : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
  simp [Function.comp, Density_mExt_of_pos this]

private lemma Density_mExt_im_nonneg {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (x : ℝ) : 0 ≤ (mExt Λ x).im := by
  have h1 := (Complex.continuous_im.tendsto _).comp (Density_tendsto_mExt hΛ hℓ x)
  refine ge_of_tendsto h1 ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
  simp only [Function.comp, Density_mExt_of_pos this]
  exact (mSol_spec Λ hΛ _ this).1.le

private lemma Density_mExt_continuous {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    Continuous (fun x : ℝ => mExt Λ (x : ℂ)) :=
  (mExt_boundary Λ hΛ hℓ).1.comp_continuous Complex.continuous_ofReal (fun x => by simp)

private lemma Density_MSol_norm {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ}
    (hz : 0 < z.im) :
    ‖mSol Λ z‖ ≤ ‖MSol Λ z‖ ∧ ‖mSol Λ z‖ < 1 ∧ (‖z‖ - 11 / 10) * ‖MSol Λ z‖ ≤ 1 := by
  have hs := mSol_spec Λ hΛ z hz
  have ha := mSol_apriori Λ hΛ hℓ z hz
  set m := mSol Λ z with hm
  have hM := Density_inv_norm_le (Λ := Λ) (M := MSol Λ z) (ζ := z + m) (ℓ := 1 / 10) hℓ hs.2.2
  have h1 : ‖m‖ ≤ ‖MSol Λ z‖ := by
    rw [hs.2.1]; exact Density_norm_ntr_le _
  have h2 : ‖z‖ - 1 ≤ ‖z + m‖ := by
    have := norm_sub_norm_le z (-m)
    rw [sub_neg_eq_add, norm_neg] at this
    linarith [ha.2.1]
  refine ⟨h1, ha.2.1, ?_⟩
  calc (‖z‖ - 11 / 10) * ‖MSol Λ z‖ ≤ (‖z + m‖ - 1 / 10) * ‖MSol Λ z‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ 1 := hM

private lemma Density_mSol_norm {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ}
    (hz : 0 < z.im) : ‖mSol Λ z‖ ≤ 1 ∧ (‖z‖ - 11 / 10) * ‖mSol Λ z‖ ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := Density_MSol_norm hΛ hℓ hz
  refine ⟨h2.le, ?_⟩
  by_cases hzn : ‖z‖ - 11 / 10 ≤ 0
  · have : (‖z‖ - 11 / 10) * ‖mSol Λ z‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hzn (norm_nonneg _)
    linarith
  · push Not at hzn
    calc (‖z‖ - 11 / 10) * ‖mSol Λ z‖ ≤ (‖z‖ - 11 / 10) * ‖MSol Λ z‖ := by gcongr
      _ ≤ 1 := h3

private lemma Density_mExt_norm {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ}
    (hz : 0 ≤ z.im) : ‖mExt Λ z‖ ≤ 1 ∧ (‖z‖ - 11 / 10) * ‖mExt Λ z‖ ≤ 1 := by
  rcases hz.lt_or_eq with hz | hz
  · rw [Density_mExt_of_pos hz]
    exact Density_mSol_norm hΛ hℓ hz
  · obtain ⟨x, rfl⟩ : ∃ x : ℝ, z = (x : ℂ) := ⟨z.re, by apply Complex.ext <;> simp [hz]⟩
    have hT := Density_tendsto_mExt hΛ hℓ x
    have hpos : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), ((x : ℂ) + (η : ℂ) * Complex.I).im > 0 := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      simpa using hη
    have hlim1 : Tendsto (fun η : ℝ => ‖mExt Λ ((x : ℂ) + (η : ℂ) * Complex.I)‖) (𝓝[>] (0 : ℝ))
        (𝓝 ‖mExt Λ x‖) := hT.norm
    have hlim2 : Tendsto (fun η : ℝ => (‖(x : ℂ) + (η : ℂ) * Complex.I‖ - 11 / 10) *
        ‖mExt Λ ((x : ℂ) + (η : ℂ) * Complex.I)‖) (𝓝[>] (0 : ℝ))
        (𝓝 ((‖(x : ℂ)‖ - 11 / 10) * ‖mExt Λ x‖)) := by
      refine Tendsto.mul ?_ hlim1
      refine Tendsto.sub ?_ tendsto_const_nhds
      have : Tendsto (fun η : ℝ => ‖(x : ℂ) + (η : ℂ) * Complex.I‖) (𝓝 0)
          (𝓝 ‖(x : ℂ) + (0 : ℂ) * Complex.I‖) := by
        apply Continuous.tendsto
        fun_prop
      simpa using this.mono_left nhdsWithin_le_nhds
    refine ⟨le_of_tendsto hlim1 ?_, le_of_tendsto hlim2 ?_⟩
    · filter_upwards [hpos] with η hη
      exact by rw [Density_mExt_of_pos hη]; exact (Density_mSol_norm hΛ hℓ hη).1
    · filter_upwards [hpos] with η hη
      exact by rw [Density_mExt_of_pos hη]; exact (Density_mSol_norm hΛ hℓ hη).2


/-- At a real point the boundary value satisfies `Im m = Im m * ⟨M M^*⟩`. -/
private lemma Density_boundary_identity {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (x : ℝ) :
    ∃ t : ℝ, ntr (MExt Λ x * (MExt Λ x)ᴴ) = (t : ℂ) ∧ 0 ≤ t ∧ t ≤ ‖MExt Λ x‖ ^ 2 ∧
      (mExt Λ x).im = (mExt Λ x).im * t := by
  obtain ⟨-, hm, hinv⟩ := (mExt_boundary Λ hΛ hℓ).2 x
  obtain ⟨t, ht0, hte, -, htle⟩ := Density_ntr_mul_self_facts (MExt Λ x)
  refine ⟨t, hte, ht0, htle, ?_⟩
  have hid := Density_im_identity hΛ hinv
  have h1 := congrArg ntr hid
  have e1 : ntr (MExt Λ x - (MExt Λ x)ᴴ) = ntr (MExt Λ x) - star (ntr (MExt Λ x)) := by
    rw [← Density_ntr_conjTranspose]
    unfold ntr
    rw [Matrix.trace_sub, mul_sub]
  have e2 : ntr ((2 * Complex.I * (((x : ℂ) + mExt Λ x).im : ℂ)) • (MExt Λ x * (MExt Λ x)ᴴ)) =
      (2 * Complex.I * (((x : ℂ) + mExt Λ x).im : ℂ)) * ntr (MExt Λ x * (MExt Λ x)ᴴ) := by
    unfold ntr
    rw [Matrix.trace_smul, smul_eq_mul]
    ring
  rw [e1, e2, hte, ← hm, Complex.star_def, Complex.sub_conj] at h1
  simp only [Complex.add_im, Complex.ofReal_im, zero_add] at h1
  have h2 : (2 * Complex.I) * (((mExt Λ x).im : ℝ) : ℂ) = (2 * Complex.I) * ((mExt Λ x).im * t : ℝ) := by
    push_cast at h1 ⊢
    linear_combination h1
  have h3 := mul_left_cancel₀ (by simp : (2 * Complex.I : ℂ) ≠ 0) h2
  exact_mod_cast h3

/-- `ρ_N` vanishes for `|x| > 2.1`. -/
private lemma Density_rho_zero_outside {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    {x : ℝ} (hx : 21 / 10 < |x|) : rho Λ x = 0 := by
  rw [Density_rho_eq hΛ hℓ]
  obtain ⟨t, -, ht0, htle, hid⟩ := Density_boundary_identity hΛ hℓ x
  obtain ⟨hn, -, hinv⟩ := (mExt_boundary Λ hΛ hℓ).2 x
  have hM := Density_inv_norm_le (Λ := Λ) (M := MExt Λ x) (ζ := (x : ℂ) + mExt Λ x) (ℓ := 1 / 10)
    hℓ hinv
  have hb := Density_mExt_norm hΛ hℓ (z := (x : ℂ)) (by simp)
  have h2 : |x| - 1 ≤ ‖(x : ℂ) + mExt Λ x‖ := by
    have := norm_sub_norm_le (x : ℂ) (-mExt Λ x)
    rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_eq_abs] at this
    linarith [hb.1]
  have hM1 : ‖MExt Λ x‖ < 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (MExt Λ x)]
  have ht1 : t < 1 := by nlinarith [norm_nonneg (MExt Λ x)]
  have : (mExt Λ x).im = 0 := by
    have h5 : (mExt Λ x).im * (1 - t) = 0 := by linarith
    rcases mul_eq_zero.1 h5 with h | h
    · exact h
    · linarith
  rw [this, zero_div]


private lemma Density_rho_nonneg {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (x : ℝ) :
    0 ≤ rho Λ x := by
  rw [Density_rho_eq hΛ hℓ]
  exact div_nonneg (Density_mExt_im_nonneg hΛ hℓ x) Real.pi_pos.le

private lemma Density_rho_le {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (x : ℝ) :
    rho Λ x ≤ 1 / Real.pi := by
  rw [Density_rho_eq hΛ hℓ]
  refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
  exact (Complex.im_le_norm _).trans (Density_mExt_norm hΛ hℓ (z := (x : ℂ)) (by simp)).1

private lemma Density_rho_continuous {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    Continuous (rho Λ) := by
  have : rho Λ = fun x : ℝ => (mExt Λ (x : ℂ)).im / Real.pi := funext (Density_rho_eq hΛ hℓ)
  rw [this]
  exact (Complex.continuous_im.comp (Density_mExt_continuous hΛ hℓ)).div_const _

private lemma Density_edge_bounds {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    Eplus Λ ≤ 21 / 10 ∧ -(21 / 10) ≤ Eminus Λ := by
  obtain ⟨hlt, hsupp⟩ := rho_support Λ hΛ hℓ
  have hne : (Function.support (rho Λ)).Nonempty := by
    rw [hsupp]; exact Set.nonempty_Ioo.2 hlt
  have hb : ∀ x ∈ Function.support (rho Λ), |x| ≤ 21 / 10 := fun x hx => by
    by_contra h
    exact hx (Density_rho_zero_outside hΛ hℓ (not_le.1 h))
  constructor
  · exact csSup_le hne fun x hx => (abs_le.1 (hb x hx)).2
  · exact le_csInf hne fun x hx => (abs_le.1 (hb x hx)).1

private lemma Density_rho_integrable {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    Integrable (rho Λ) := by
  obtain ⟨hlt, hsupp⟩ := rho_support Λ hΛ hℓ
  refine (Density_rho_continuous hΛ hℓ).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := Eminus Λ) (b := Eplus Λ)) ?_
  intro x hx
  by_contra h
  have : x ∈ Function.support (rho Λ) := h
  rw [hsupp] at this
  exact hx (Set.Ioo_subset_Icc_self this)

private lemma Density_rho_pos {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {x : ℝ}
    (hx : x ∈ Set.Ioo (Eminus Λ) (Eplus Λ)) : 0 < rho Λ x := by
  obtain ⟨-, hsupp⟩ := rho_support Λ hΛ hℓ
  have : x ∈ Function.support (rho Λ) := by rw [hsupp]; exact hx
  exact lt_of_le_of_ne (Density_rho_nonneg hΛ hℓ x) (Ne.symm this)

private lemma Density_rho_eq_zero {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {x : ℝ}
    (hx : x ∉ Set.Ioo (Eminus Λ) (Eplus Λ)) : rho Λ x = 0 := by
  obtain ⟨-, hsupp⟩ := rho_support Λ hΛ hℓ
  by_contra h
  have : x ∈ Function.support (rho Λ) := h
  rw [hsupp] at this
  exact hx this

end Density_S2

section Density_S3
open scoped Matrix.Norms.L2Operator

/-- The boundary integral of `g` over the rectangle with corners `-R`, `R`, `R + iR`, `-R + iR`. -/
private def Density_rect (g : ℂ → ℂ) (R : ℝ) : ℂ :=
  (∫ x : ℝ in (-R)..R, g (x : ℂ)) - (∫ x : ℝ in (-R)..R, g ((x : ℂ) + (R : ℂ) * Complex.I)) +
    Complex.I • (∫ y : ℝ in (0 : ℝ)..R, g ((R : ℂ) + (y : ℂ) * Complex.I)) -
    Complex.I • (∫ y : ℝ in (0 : ℝ)..R, g (-(R : ℂ) + (y : ℂ) * Complex.I))

private lemma Density_rect_eq_zero {F : ℂ → ℂ} (hc : ContinuousOn F {z | 0 ≤ z.im})
    (hd : DifferentiableOn ℂ F {z | 0 < z.im}) {R : ℝ} (hR : 0 < R) : Density_rect F R = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F
    ⟨-R, 0⟩ ⟨R, R⟩ (hc.mono ?_) (hd.mono ?_)
  · simpa [Density_rect] using h
  · intro z hz
    have := hz.2
    simp only [Complex.mem_reProdIm] at hz
    simp [Set.uIcc_of_le hR.le] at hz ⊢
    exact hz.2.1
  · intro z hz
    simp only [Complex.mem_reProdIm] at hz
    simp [hR.le] at hz ⊢
    exact hz.2.1


private lemma Density_one_add_le {w ζ : ℂ} {b : ℝ} (hb : 0 < b) (hζ : b ≤ ‖ζ - w‖) :
    1 + ‖ζ‖ ≤ ‖ζ - w‖ * ((1 + ‖w‖) / b + 1) := by
  have h1 : ‖ζ‖ ≤ ‖ζ - w‖ + ‖w‖ := by
    have := norm_add_le (ζ - w) w
    simpa using this
  have h2 : 1 + ‖w‖ ≤ ‖ζ - w‖ * ((1 + ‖w‖) / b) := by
    rw [mul_div_assoc', le_div_iff₀ hb]
    nlinarith [norm_nonneg w]
  nlinarith

private lemma Density_integrable_Phi {f : ℂ → ℂ} {K : ℝ} (hc : ContinuousOn f {z | 0 ≤ z.im})
    (hK : ∀ z : ℂ, 0 ≤ z.im → (1 + ‖z‖) * ‖f z‖ ≤ K) {w : ℂ} (hw : w.im ≠ 0) :
    Integrable (fun x : ℝ => f x / ((x : ℂ) - w)) := by
  have hb : 0 < |w.im| := abs_pos.2 hw
  have hK0 : 0 ≤ K := by
    have := hK 0 (by simp)
    simp only [norm_zero, add_zero, one_mul] at this
    exact (norm_nonneg _).trans this
  set c : ℝ := (1 + ‖w‖) / |w.im| + 1 with hc'
  have hne : ∀ x : ℝ, (x : ℂ) - w ≠ 0 := fun x h => by
    have := congrArg Complex.im h
    simp at this
    exact hw this
  have hcont : Continuous (fun x : ℝ => f x / ((x : ℂ) - w)) := by
    have h1 : Continuous (fun x : ℝ => f (x : ℂ)) :=
      hc.comp_continuous Complex.continuous_ofReal (fun x => by simp)
    exact h1.div (by fun_prop) hne
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (K * c)) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hs : |w.im| ≤ ‖(x : ℂ) - w‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) - w)
    simpa using this
  have hspos : 0 < ‖(x : ℂ) - w‖ := lt_of_lt_of_le hb hs
  have h1 := hK (x : ℂ) (by simp)
  have h2 := Density_one_add_le (w := w) (ζ := (x : ℂ)) hb hs
  rw [Complex.norm_real, Real.norm_eq_abs] at h1 h2
  rw [norm_div, div_le_iff₀ hspos]
  have hxsq : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
  have hf0 := norm_nonneg (f x)
  have h3 : ‖f x‖ * (1 + x ^ 2) ≤ K * (‖(x : ℂ) - w‖ * c) := by
    calc ‖f x‖ * (1 + x ^ 2) ≤ ‖f x‖ * (1 + |x|) ^ 2 := by gcongr
      _ = (‖f x‖ * (1 + |x|)) * (1 + |x|) := by ring
      _ ≤ K * (‖(x : ℂ) - w‖ * c) := by
        refine mul_le_mul ?_ h2 (by positivity) hK0
        linarith
  have h4 : 0 < 1 + x ^ 2 := by positivity
  calc ‖f x‖ = ‖f x‖ * (1 + x ^ 2) * (1 + x ^ 2)⁻¹ := by field_simp
    _ ≤ K * (‖(x : ℂ) - w‖ * c) * (1 + x ^ 2)⁻¹ := by gcongr
    _ = K * c * (1 + x ^ 2)⁻¹ * ‖(x : ℂ) - w‖ := by ring


private lemma Density_rect_tendsto {f : ℂ → ℂ} {K : ℝ} (hc : ContinuousOn f {z | 0 ≤ z.im})
    (hK : ∀ z : ℂ, 0 ≤ z.im → (1 + ‖z‖) * ‖f z‖ ≤ K) {w : ℂ} (hw : w.im ≠ 0) :
    Tendsto (fun R : ℝ => Density_rect (fun ζ => f ζ / (ζ - w)) R) atTop
      (𝓝 (∫ x : ℝ, f x / ((x : ℂ) - w))) := by
  have hK0 : 0 ≤ K := by
    have := hK 0 (by simp)
    simp only [norm_zero, add_zero, one_mul] at this
    exact (norm_nonneg _).trans this
  have hint := Density_integrable_Phi hc hK hw
  have hbot : Tendsto (fun R : ℝ => ∫ x : ℝ in (-R)..R, f x / ((x : ℂ) - w)) atTop
      (𝓝 (∫ x : ℝ, f x / ((x : ℂ) - w))) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  -- pointwise bound far from the origin
  have hside : ∀ R : ℝ, 2 * ‖w‖ ≤ R → 0 < R → ∀ ζ : ℂ, 0 ≤ ζ.im → R ≤ ‖ζ‖ →
      ‖f ζ / (ζ - w)‖ ≤ 2 * K / R ^ 2 := by
    intro R hR hR0 ζ hζ hRζ
    have h1 : R / 2 ≤ ‖ζ - w‖ := by
      have := norm_sub_norm_le ζ w
      linarith
    have h2 : ‖f ζ‖ ≤ K / R := by
      have := hK ζ hζ
      rw [le_div_iff₀ hR0]
      nlinarith [norm_nonneg (f ζ), norm_nonneg ζ]
    rw [norm_div]
    calc ‖f ζ‖ / ‖ζ - w‖ ≤ (K / R) / (R / 2) := by
          gcongr
      _ = 2 * K / R ^ 2 := by field_simp
  have hbound : ∀ R : ℝ, 2 * ‖w‖ ≤ R → 0 < R →
      (∀ x : ℝ, x ∈ Set.uIoc (-R) R → ‖f ((x : ℂ) + (R : ℂ) * Complex.I) /
          (((x : ℂ) + (R : ℂ) * Complex.I) - w)‖ ≤ 2 * K / R ^ 2) ∧
      (∀ y : ℝ, y ∈ Set.uIoc (0 : ℝ) R → ‖f ((R : ℂ) + (y : ℂ) * Complex.I) /
          (((R : ℂ) + (y : ℂ) * Complex.I) - w)‖ ≤ 2 * K / R ^ 2) ∧
      (∀ y : ℝ, y ∈ Set.uIoc (0 : ℝ) R → ‖f (-(R : ℂ) + (y : ℂ) * Complex.I) /
          ((-(R : ℂ) + (y : ℂ) * Complex.I) - w)‖ ≤ 2 * K / R ^ 2) := by
    intro R hR hR0
    refine ⟨fun x _ => hside R hR hR0 _ (by simp [hR0.le]) ?_, fun y hy => ?_, fun y hy => ?_⟩
    · have := Complex.abs_im_le_norm ((x : ℂ) + (R : ℂ) * Complex.I)
      simpa [abs_of_pos hR0] using this
    · rw [Set.uIoc_of_le hR0.le] at hy
      refine hside R hR hR0 _ (by simp [hy.1.le]) ?_
      have := Complex.abs_re_le_norm ((R : ℂ) + (y : ℂ) * Complex.I)
      simpa [abs_of_pos hR0] using this
    · rw [Set.uIoc_of_le hR0.le] at hy
      refine hside R hR hR0 _ (by simp [hy.1.le]) ?_
      have := Complex.abs_re_le_norm (-(R : ℂ) + (y : ℂ) * Complex.I)
      simpa [abs_of_pos hR0] using this
  have hdec : Tendsto (fun R : ℝ => 4 * K / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have htop : Tendsto (fun R : ℝ => ∫ x : ℝ in (-R)..R,
      f ((x : ℂ) + (R : ℂ) * Complex.I) / (((x : ℂ) + (R : ℂ) * Complex.I) - w)) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hdec
    filter_upwards [eventually_ge_atTop (2 * ‖w‖), eventually_gt_atTop 0] with R hR hR0
    have := intervalIntegral.norm_integral_le_of_norm_le_const (hbound R hR hR0).1
    refine this.trans (le_of_eq ?_)
    rw [show |R - -R| = 2 * R by rw [abs_of_nonneg (by linarith)]; ring]
    field_simp
    ring
  have hright : Tendsto (fun R : ℝ => ∫ y : ℝ in (0 : ℝ)..R,
      f ((R : ℂ) + (y : ℂ) * Complex.I) / (((R : ℂ) + (y : ℂ) * Complex.I) - w)) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hdec
    filter_upwards [eventually_ge_atTop (2 * ‖w‖), eventually_gt_atTop 0] with R hR hR0
    have := intervalIntegral.norm_integral_le_of_norm_le_const (hbound R hR hR0).2.1
    refine this.trans ?_
    rw [show |R - 0| = R by rw [sub_zero, abs_of_pos hR0]]
    have : 2 * K / R ^ 2 * R = 2 * K / R := by field_simp
    rw [this]
    have h0 : 0 ≤ K / R := by positivity
    have e1 : 4 * K / R = 4 * (K / R) := by ring
    have e2 : 2 * K / R = 2 * (K / R) := by ring
    rw [e1, e2]
    linarith
  have hleft : Tendsto (fun R : ℝ => ∫ y : ℝ in (0 : ℝ)..R,
      f (-(R : ℂ) + (y : ℂ) * Complex.I) / ((-(R : ℂ) + (y : ℂ) * Complex.I) - w)) atTop
      (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hdec
    filter_upwards [eventually_ge_atTop (2 * ‖w‖), eventually_gt_atTop 0] with R hR hR0
    have := intervalIntegral.norm_integral_le_of_norm_le_const (hbound R hR hR0).2.2
    refine this.trans ?_
    rw [show |R - 0| = R by rw [sub_zero, abs_of_pos hR0]]
    have : 2 * K / R ^ 2 * R = 2 * K / R := by field_simp
    rw [this]
    have h0 : 0 ≤ K / R := by positivity
    have e1 : 4 * K / R = 4 * (K / R) := by ring
    have e2 : 2 * K / R = 2 * (K / R) := by ring
    rw [e1, e2]
    linarith
  have := ((hbot.sub htop).add (hright.const_smul Complex.I)).sub (hleft.const_smul Complex.I)
  simpa [Density_rect] using this


private lemma Density_rect_congr {F G : ℂ → ℂ} {w : ℂ} {R : ℝ} (hw : w.im ≠ 0) (hR : ‖w‖ < R)
    (h : ∀ ζ, ζ ≠ w → F ζ = G ζ) : Density_rect F R = Density_rect G R := by
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have him := Complex.abs_im_le_norm w
  have hre := Complex.abs_re_le_norm w
  have e1 : ∫ x : ℝ in (-R)..R, F (x : ℂ) = ∫ x : ℝ in (-R)..R, G (x : ℂ) := by
    refine intervalIntegral.integral_congr fun x _ => h _ ?_
    intro hx
    have := congrArg Complex.im hx
    simp at this
    exact hw this.symm
  have e2 : ∫ x : ℝ in (-R)..R, F ((x : ℂ) + (R : ℂ) * Complex.I) =
      ∫ x : ℝ in (-R)..R, G ((x : ℂ) + (R : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun x _ => h _ ?_
    intro hx
    have := congrArg Complex.im hx
    simp at this
    have h1 := (abs_le.1 him).2
    linarith
  have e3 : ∫ y : ℝ in (0 : ℝ)..R, F ((R : ℂ) + (y : ℂ) * Complex.I) =
      ∫ y : ℝ in (0 : ℝ)..R, G ((R : ℂ) + (y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun x _ => h _ ?_
    intro hx
    have := congrArg Complex.re hx
    simp at this
    have h1 := (abs_le.1 hre).2
    linarith
  have e4 : ∫ y : ℝ in (0 : ℝ)..R, F (-(R : ℂ) + (y : ℂ) * Complex.I) =
      ∫ y : ℝ in (0 : ℝ)..R, G (-(R : ℂ) + (y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun x _ => h _ ?_
    intro hx
    have := congrArg Complex.re hx
    simp at this
    have h1 := (abs_le.1 hre).1
    linarith
  unfold Density_rect
  rw [e1, e2, e3, e4]

/-- Cauchy's theorem on the half plane for a point `w` in the lower half plane. -/
private lemma Density_cauchy_outside {f : ℂ → ℂ} {K : ℝ} (hc : ContinuousOn f {z | 0 ≤ z.im})
    (hd : DifferentiableOn ℂ f {z | 0 < z.im})
    (hK : ∀ z : ℂ, 0 ≤ z.im → (1 + ‖z‖) * ‖f z‖ ≤ K) {w : ℂ} (hw : w.im < 0) :
    ∫ x : ℝ, f x / ((x : ℂ) - w) = 0 := by
  have hne : ∀ ζ : ℂ, 0 ≤ ζ.im → ζ - w ≠ 0 := fun ζ hζ h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hF : ContinuousOn (fun ζ => f ζ / (ζ - w)) {z | 0 ≤ z.im} :=
    hc.div (continuousOn_id.sub continuousOn_const) hne
  have hFd : DifferentiableOn ℂ (fun ζ => f ζ / (ζ - w)) {z | 0 < z.im} :=
    hd.div (differentiableOn_id.sub_const w) fun ζ hζ => hne ζ (le_of_lt hζ)
  have h1 := Density_rect_tendsto hc hK hw.ne
  have h2 : Tendsto (fun R : ℝ => Density_rect (fun ζ => f ζ / (ζ - w)) R) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact (Density_rect_eq_zero hF hFd hR).symm
  exact tendsto_nhds_unique h1 h2

/-- If `g(w) = 0` with `w` in the upper half plane then `∫ g(x)/(x - w) dx = 0`. -/
private lemma Density_cauchy_zero {g : ℂ → ℂ} {K : ℝ} (hc : ContinuousOn g {z | 0 ≤ z.im})
    (hd : DifferentiableOn ℂ g {z | 0 < z.im})
    (hK : ∀ z : ℂ, 0 ≤ z.im → (1 + ‖z‖) * ‖g z‖ ≤ K) {w : ℂ} (hw : 0 < w.im) (hgw : g w = 0) :
    ∫ x : ℝ, g x / ((x : ℂ) - w) = 0 := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hsub : {z : ℂ | 0 < z.im} ⊆ {z : ℂ | 0 ≤ z.im} :=
    fun z (hz : 0 < z.im) => (le_of_lt hz : 0 ≤ z.im)
  have hnhd : {z : ℂ | 0 ≤ z.im} ∈ 𝓝 w := Filter.mem_of_superset (hopen.mem_nhds hw) hsub
  have hnhd' : {z : ℂ | 0 < z.im} ∈ 𝓝 w := hopen.mem_nhds hw
  have hF : ContinuousOn (dslope g w) {z | 0 ≤ z.im} :=
    (continuousOn_dslope hnhd).2 ⟨hc, hd.differentiableAt hnhd'⟩
  have hFd : DifferentiableOn ℂ (dslope g w) {z | 0 < z.im} :=
    (Complex.differentiableOn_dslope hnhd').2 hd
  have h1 := Density_rect_tendsto hc hK hw.ne'
  have h2 : Tendsto (fun R : ℝ => Density_rect (fun ζ => g ζ / (ζ - w)) R) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ‖w‖] with R hR
    have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
    rw [← Density_rect_eq_zero hF hFd hR0]
    refine (Density_rect_congr hw.ne' hR fun ζ hζ => ?_).symm
    rw [dslope_of_ne _ hζ, slope_def_field, hgw, sub_zero]
  exact tendsto_nhds_unique h1 h2


private lemma Density_integral_kernel (w : ℂ) (hw : 0 < w.im) :
    ∫ x : ℝ, ((x : ℂ) - (starRingEnd ℂ) w)⁻¹ / ((x : ℂ) - w) = ((Real.pi / w.im : ℝ) : ℂ) := by
  have hb : w.im ≠ 0 := hw.ne'
  have h1 : ∀ x : ℝ, ((x : ℂ) - (starRingEnd ℂ) w)⁻¹ / ((x : ℂ) - w) =
      ((((x - w.re) ^ 2 + w.im ^ 2)⁻¹ : ℝ) : ℂ) := by
    intro x
    have hne1 : (x : ℂ) - (starRingEnd ℂ) w ≠ 0 := fun h => by
      have := congrArg Complex.im h
      simp at this
      linarith
    have hne2 : (x : ℂ) - w ≠ 0 := fun h => by
      have := congrArg Complex.im h
      simp at this
      linarith
    have key : ((x : ℂ) - (starRingEnd ℂ) w) * ((x : ℂ) - w) =
        (((x - w.re) ^ 2 + w.im ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
        ring
      · simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
        ring
    rw [div_eq_mul_inv, ← mul_inv, key]
    exact (Complex.ofReal_inv _).symm
  simp only [h1]
  rw [integral_complex_ofReal]
  congr 1
  have hγ : (0 : ℝ) ≤ w.im := hw.le
  have h2 := ProbabilityTheory.integral_cauchyPDFReal_eq_one w.re (γ := ⟨w.im, hγ⟩)
    (by intro h; apply hb; have := congrArg NNReal.toReal h; exact this)
  unfold ProbabilityTheory.cauchyPDFReal at h2
  have h2' : ∫ a : ℝ, (Real.pi⁻¹ * w.im) * ((a - w.re) ^ 2 + w.im ^ 2)⁻¹ = 1 := h2
  rw [integral_const_mul] at h2'
  have := eq_inv_of_mul_eq_one_right h2'
  rw [this]
  field_simp


/-- Cauchy's integral formula on the half plane for a point `w` in the upper half plane. -/
private lemma Density_cauchy_inside {f : ℂ → ℂ} {K : ℝ} (hc : ContinuousOn f {z | 0 ≤ z.im})
    (hd : DifferentiableOn ℂ f {z | 0 < z.im})
    (hK : ∀ z : ℂ, 0 ≤ z.im → (1 + ‖z‖) * ‖f z‖ ≤ K) {w : ℂ} (hw : 0 < w.im) :
    ∫ x : ℝ, f x / ((x : ℂ) - w) = 2 * Real.pi * Complex.I * f w := by
  set wb := (starRingEnd ℂ) w with hwb
  set f₀ : ℂ → ℂ := fun ζ => (ζ - wb)⁻¹ with hf₀
  have hne : ∀ ζ : ℂ, 0 ≤ ζ.im → ζ - wb ≠ 0 := fun ζ hζ h => by
    have := congrArg Complex.im h
    simp [hwb] at this
    linarith
  have hf₀c : ContinuousOn f₀ {z | 0 ≤ z.im} :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  have hf₀d : DifferentiableOn ℂ f₀ {z | 0 < z.im} :=
    (differentiableOn_id.sub_const wb).inv fun ζ hζ => hne ζ (le_of_lt hζ)
  set K₀ : ℝ := (1 + ‖w‖) / w.im + 1 with hK₀def
  have hK₀ : ∀ z : ℂ, 0 ≤ z.im → (1 + ‖z‖) * ‖f₀ z‖ ≤ K₀ := by
    intro z hz
    have hs : w.im ≤ ‖z - wb‖ := by
      have := Complex.abs_im_le_norm (z - wb)
      have h2 : (z - wb).im = z.im + w.im := by simp [hwb]
      rw [h2] at this
      rw [abs_of_nonneg (by linarith)] at this
      linarith
    have := Density_one_add_le (w := wb) (ζ := z) hw (by simpa using hs)
    have hwn : ‖wb‖ = ‖w‖ := by simp [hwb]
    rw [hwn] at this
    have hspos : 0 < ‖z - wb‖ := lt_of_lt_of_le hw hs
    simp only [hf₀, norm_inv]
    rw [← div_eq_mul_inv, div_le_iff₀ hspos]
    linarith
  have hfw0 : f₀ w ≠ 0 := by
    simp only [hf₀]
    apply inv_ne_zero
    intro h
    have := congrArg Complex.im h
    simp [hwb] at this
    linarith
  set g : ℂ → ℂ := fun ζ => f₀ w * f ζ - f w * f₀ ζ with hg
  have hgc : ContinuousOn g {z | 0 ≤ z.im} :=
    (continuousOn_const.mul hc).sub (continuousOn_const.mul hf₀c)
  have hgd : DifferentiableOn ℂ g {z | 0 < z.im} :=
    (differentiableOn_const _ |>.mul hd).sub (differentiableOn_const _ |>.mul hf₀d)
  have hgK : ∀ z : ℂ, 0 ≤ z.im → (1 + ‖z‖) * ‖g z‖ ≤ ‖f₀ w‖ * K + ‖f w‖ * K₀ := by
    intro z hz
    have h1 := hK z hz
    have h2 := hK₀ z hz
    have h3 : ‖g z‖ ≤ ‖f₀ w‖ * ‖f z‖ + ‖f w‖ * ‖f₀ z‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    calc (1 + ‖z‖) * ‖g z‖ ≤ (1 + ‖z‖) * (‖f₀ w‖ * ‖f z‖ + ‖f w‖ * ‖f₀ z‖) := by gcongr
      _ = ‖f₀ w‖ * ((1 + ‖z‖) * ‖f z‖) + ‖f w‖ * ((1 + ‖z‖) * ‖f₀ z‖) := by ring
      _ ≤ ‖f₀ w‖ * K + ‖f w‖ * K₀ := by gcongr
  have hgw : g w = 0 := by simp only [hg]; ring
  have h0 := Density_cauchy_zero hgc hgd hgK hw hgw
  have hif := Density_integrable_Phi hc hK hw.ne'
  have hif₀ := Density_integrable_Phi hf₀c hK₀ hw.ne'
  have hlin : ∫ x : ℝ, g x / ((x : ℂ) - w) =
      f₀ w * (∫ x : ℝ, f x / ((x : ℂ) - w)) - f w * (∫ x : ℝ, f₀ x / ((x : ℂ) - w)) := by
    have e : ∀ x : ℝ, g x / ((x : ℂ) - w) =
        f₀ w * (f x / ((x : ℂ) - w)) - f w * (f₀ x / ((x : ℂ) - w)) := by
      intro x
      simp only [hg]
      ring
    simp_rw [e]
    rw [integral_sub (hif.const_mul _) (hif₀.const_mul _), integral_const_mul, integral_const_mul]
  have hker : ∫ x : ℝ, f₀ x / ((x : ℂ) - w) = ((Real.pi / w.im : ℝ) : ℂ) :=
    Density_integral_kernel w hw
  rw [h0, hker] at hlin
  have hfw : f₀ w = ((2 * w.im : ℝ) * Complex.I)⁻¹ := by
    simp only [hf₀, hwb]
    rw [Complex.sub_conj]
  have hb : (w.im : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have h5 : f₀ w * (∫ x : ℝ, f x / ((x : ℂ) - w)) = f w * ((Real.pi / w.im : ℝ) : ℂ) := by
    linear_combination -hlin
  rw [hfw] at h5
  push_cast at h5
  field_simp at h5 ⊢
  linear_combination h5

end Density_S3

section Density_S4
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Density_mExt_bdd {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    ContinuousOn (mExt Λ) {z : ℂ | 0 ≤ z.im} ∧ DifferentiableOn ℂ (mExt Λ) {z : ℂ | 0 < z.im} ∧
      ∀ z : ℂ, 0 ≤ z.im → (1 + ‖z‖) * ‖mExt Λ z‖ ≤ 4 := by
  refine ⟨(mExt_boundary Λ hΛ hℓ).1, ?_, ?_⟩
  · have h1 : DifferentiableOn ℂ (mSol Λ) {z : ℂ | 0 < z.im} :=
      (mSol_analyticOnNhd Λ hΛ).differentiableOn
    exact h1.congr (fun x hx => Density_mExt_of_pos hx)
  · intro z hz
    obtain ⟨h1, h2⟩ := Density_mExt_norm hΛ hℓ hz
    nlinarith [norm_nonneg (mExt Λ z), norm_nonneg z]

/-- The representation `m(z) = ∫ ρ_N(x) / (x - z) dx` for `Im z > 0`. -/
private lemma Density_rep {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ}
    (hz : 0 < z.im) : mSol Λ z = ∫ x : ℝ, (rho Λ x : ℂ) / ((x : ℂ) - z) := by
  obtain ⟨hc, hd, hK⟩ := Density_mExt_bdd hΛ hℓ
  have hin := Density_cauchy_inside hc hd hK hz
  have hzb : (starRingEnd ℂ z).im < 0 := by simpa using hz
  have hout := Density_cauchy_outside hc hd hK hzb
  have hint1 := Density_integrable_Phi hc hK hz.ne'
  have hint2 := Density_integrable_Phi hc hK hzb.ne
  have hout' : ∫ x : ℝ, (starRingEnd ℂ) (mExt Λ x) / ((x : ℂ) - z) = 0 := by
    have h := congrArg (starRingEnd ℂ) hout
    rw [map_zero, ← integral_conj] at h
    rw [← h]
    congr 1
    funext x
    simp
  have hint3 : Integrable (fun x : ℝ => (starRingEnd ℂ) (mExt Λ x) / ((x : ℂ) - z)) := by
    have := (Complex.conjCLE.integrable_comp_iff).2 hint2
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hdiff : ∀ x : ℝ, (mExt Λ x - (starRingEnd ℂ) (mExt Λ x)) / ((x : ℂ) - z) =
      (2 * Real.pi * Complex.I) * ((rho Λ x : ℂ) / ((x : ℂ) - z)) := by
    intro x
    rw [Complex.sub_conj, Density_rho_eq hΛ hℓ x]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    push_cast
    field_simp
  have h1 : ∫ x : ℝ, (mExt Λ x - (starRingEnd ℂ) (mExt Λ x)) / ((x : ℂ) - z) =
      2 * Real.pi * Complex.I * mExt Λ z := by
    simp_rw [sub_div]
    rw [integral_sub hint1 hint3, hin, hout', sub_zero]
  simp_rw [hdiff] at h1
  rw [integral_const_mul] at h1
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    simp [this]
  rw [← Density_mExt_of_pos hz]
  exact (mul_left_cancel₀ hne h1).symm


private lemma Density_ntr_one : ntr (1 : Matrix ι ι ℂ) = 1 := by
  unfold ntr
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [Matrix.trace_one, hn]

/-- `z m(z) + 1 = ⟨Λ M⟩ - m²`, bounded in terms of `‖z‖`. -/
private lemma Density_zm_bound {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {z : ℂ}
    (hz : 0 < z.im) (hzn : 11 / 10 ≤ ‖z‖) :
    (‖z‖ - 11 / 10) ^ 2 * ‖z * mSol Λ z + 1‖ ≤ (‖z‖ - 11 / 10) / 10 + 1 := by
  obtain ⟨h1, h2, h3⟩ := Density_MSol_norm hΛ hℓ hz
  have hs := mSol_spec Λ hΛ z hz
  set m := mSol Λ z with hm
  set M := MSol Λ z with hM
  have e1 : (z + m) • M = Λ * M - 1 := by
    have : Λ * M - (z + m) • M = 1 := by
      have := hs.2.2
      rwa [sub_mul, smul_mul_assoc, one_mul] at this
    rw [← this]; abel
  have e2 : (z + m) * m = ntr (Λ * M) - 1 := by
    have := congrArg ntr e1
    have e3 : ntr ((z + m) • M) = (z + m) * ntr M := by
      unfold ntr; rw [Matrix.trace_smul, smul_eq_mul]; ring
    have e4 : ntr (Λ * M - 1) = ntr (Λ * M) - 1 := by
      rw [← Density_ntr_one (ι := ι)]
      unfold ntr; rw [Matrix.trace_sub, mul_sub]
    rw [e3, e4, ← hs.2.1] at this
    exact this
  have e5 : z * m + 1 = ntr (Λ * M) - m ^ 2 := by linear_combination e2
  have hℓ' : ‖Λ‖ ≤ 1 / 10 := hℓ
  have h4 : ‖ntr (Λ * M)‖ ≤ (1 / 10) * ‖M‖ := by
    refine (Density_norm_ntr_le _).trans ?_
    refine (norm_mul_le _ _).trans ?_
    gcongr
  have h5 : ‖z * m + 1‖ ≤ (1 / 10) * ‖M‖ + ‖M‖ ^ 2 := by
    rw [e5]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow]
    gcongr
  have hd : 0 ≤ ‖z‖ - 11 / 10 := by linarith
  set d := ‖z‖ - 11 / 10 with hdd
  have hdM : d * ‖M‖ ≤ 1 := h3
  have hdM0 : 0 ≤ d * ‖M‖ := by positivity
  calc d ^ 2 * ‖z * m + 1‖ ≤ d ^ 2 * ((1 / 10) * ‖M‖ + ‖M‖ ^ 2) := by gcongr
    _ = (d / 10) * (d * ‖M‖) + (d * ‖M‖) ^ 2 := by ring
    _ ≤ d / 10 + 1 := by nlinarith

private lemma Density_zm_tendsto {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    Tendsto (fun η : ℝ => -(((η : ℂ) * Complex.I) * mSol Λ ((η : ℂ) * Complex.I))) atTop
      (𝓝 1) := by
  have hg : Tendsto (fun η : ℝ => ((η - 11 / 10) / 10 + 1) / (η - 11 / 10) ^ 2) atTop (𝓝 0) := by
    have hd : Tendsto (fun η : ℝ => η - 11 / 10) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
    have h1 : Tendsto (fun η : ℝ => (η - 11 / 10)⁻¹) atTop (𝓝 0) := hd.inv_tendsto_atTop
    have h2 : Tendsto (fun η : ℝ => 1 / 10 * (η - 11 / 10)⁻¹ + ((η - 11 / 10)⁻¹) ^ 2) atTop (𝓝 0) := by
      have := (h1.const_mul (1 / 10)).add (h1.pow 2)
      simpa using this
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (11 / 10 : ℝ)] with η hη
    have : η - 11 / 10 ≠ 0 := by linarith
    field_simp
  have hlim : Tendsto (fun η : ℝ => ((η : ℂ) * Complex.I) * mSol Λ ((η : ℂ) * Complex.I) + 1) atTop
      (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    refine squeeze_zero' (Eventually.of_forall fun η => norm_nonneg _) ?_ hg
    filter_upwards [eventually_gt_atTop (11 / 10 : ℝ)] with η hη
    have hzim : 0 < (((η : ℂ) * Complex.I)).im := by simp; linarith
    have hznorm : ‖(η : ℂ) * Complex.I‖ = η := by
      simp [abs_of_pos (by linarith : (0 : ℝ) < η)]
    have := Density_zm_bound hΛ hℓ hzim (by rw [hznorm]; linarith)
    rw [hznorm] at this
    have hpos : 0 < (η - 11 / 10) ^ 2 := by nlinarith
    rw [le_div_iff₀ hpos, mul_comm]
    exact this
  have := (hlim.sub_const 1).neg
  simpa using this


private lemma Density_mass {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    ∫ x : ℝ, rho Λ x = 1 := by
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ → ℂ, F = fun (η x : ℝ) =>
      (rho Λ x : ℂ) * (-((η : ℂ) * Complex.I) / ((x : ℂ) - (η : ℂ) * Complex.I)) := ⟨_, rfl⟩
  have hne : ∀ (η x : ℝ), 0 < η → (x : ℂ) - (η : ℂ) * Complex.I ≠ 0 := fun η x hη h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hn : ∀ (η x : ℝ), 0 < η → η ≤ ‖(x : ℂ) - (η : ℂ) * Complex.I‖ := by
    intro η x hη
    have := Complex.abs_im_le_norm ((x : ℂ) - (η : ℂ) * Complex.I)
    simpa [abs_of_pos hη] using this
  have hbound : ∀ η x : ℝ, 0 < η → ‖F η x‖ ≤ rho Λ x := by
    intro η x hη
    have hρ := Density_rho_nonneg hΛ hℓ x
    have hpos : 0 < ‖(x : ℂ) - (η : ℂ) * Complex.I‖ := lt_of_lt_of_le hη (hn η x hη)
    have h2 : η / ‖(x : ℂ) - (η : ℂ) * Complex.I‖ ≤ 1 := by rw [div_le_one hpos]; exact hn η x hη
    rw [hF]
    simp only [norm_mul, norm_div, norm_neg, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hη, abs_of_nonneg hρ]
    calc rho Λ x * (η / ‖(x : ℂ) - (η : ℂ) * Complex.I‖) ≤ rho Λ x * 1 := by gcongr
      _ = rho Λ x := mul_one _
  have hlim : ∀ x : ℝ, Tendsto (fun η : ℝ => F η x) atTop (𝓝 (rho Λ x : ℂ)) := by
    intro x
    have h1 : Tendsto (fun η : ℝ => -((η : ℂ) * Complex.I) / ((x : ℂ) - (η : ℂ) * Complex.I)) atTop
        (𝓝 1) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hx : Tendsto (fun η : ℝ => |x| / η) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      refine squeeze_zero' (Eventually.of_forall fun η => norm_nonneg _) ?_ hx
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with η hη
      have e : -((η : ℂ) * Complex.I) / ((x : ℂ) - (η : ℂ) * Complex.I) - 1 =
          -(x : ℂ) / ((x : ℂ) - (η : ℂ) * Complex.I) := by
        field_simp [hne η x hη]
        ring
      rw [e, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_left (abs_nonneg x) hη (hn η x hη)
    have := h1.const_mul (rho Λ x : ℂ)
    rw [hF]
    simpa using this
  have hmeas : ∀ η : ℝ, 0 < η → AEStronglyMeasurable (F η) volume := by
    intro η hη
    have hc1 : Continuous (fun x : ℝ => (rho Λ x : ℂ)) :=
      Complex.continuous_ofReal.comp (Density_rho_continuous hΛ hℓ)
    have hc2 : Continuous (fun x : ℝ => -((η : ℂ) * Complex.I) / ((x : ℂ) - (η : ℂ) * Complex.I)) := by
      have h1 : Continuous (fun x : ℝ => ((x : ℂ) - (η : ℂ) * Complex.I)) :=
        Complex.continuous_ofReal.sub continuous_const
      have h2 : Continuous (fun x : ℝ => ((x : ℂ) - (η : ℂ) * Complex.I)⁻¹) :=
        h1.inv₀ (fun x => hne η x hη)
      have := h2.const_mul (-((η : ℂ) * Complex.I))
      simpa [div_eq_mul_inv] using this
    rw [hF]
    exact (hc1.mul hc2).aestronglyMeasurable
  have hm : ∀ᶠ η : ℝ in atTop, AEStronglyMeasurable (F η) volume := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with η hη using hmeas η hη
  have hb : ∀ᶠ η : ℝ in atTop, ∀ᵐ x : ℝ ∂volume, ‖F η x‖ ≤ rho Λ x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with η hη
    exact Filter.Eventually.of_forall fun x => hbound η x hη
  have hl : ∀ᵐ x : ℝ ∂volume, Tendsto (fun η : ℝ => F η x) atTop (𝓝 (rho Λ x : ℂ)) :=
    Filter.Eventually.of_forall hlim
  have hDCT : Tendsto (fun η : ℝ => ∫ x : ℝ, F η x) atTop (𝓝 (∫ x : ℝ, (rho Λ x : ℂ))) :=
    tendsto_integral_filter_of_dominated_convergence (rho Λ) hm hb (Density_rho_integrable hΛ hℓ) hl
  have hrep : ∀ η : ℝ, 0 < η → ∫ x : ℝ, F η x =
      -(((η : ℂ) * Complex.I) * mSol Λ ((η : ℂ) * Complex.I)) := by
    intro η hη
    have hz : 0 < (((η : ℂ) * Complex.I)).im := by simpa using hη
    rw [Density_rep hΛ hℓ hz, ← integral_const_mul, ← integral_neg]
    rw [hF]
    congr 1
    funext x
    beta_reduce
    ring
  have hlim2 : Tendsto (fun η : ℝ => ∫ x : ℝ, F η x) atTop (𝓝 1) := by
    refine (Density_zm_tendsto hΛ hℓ).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with η hη
    exact (hrep η hη).symm
  have := tendsto_nhds_unique hDCT hlim2
  rw [integral_complex_ofReal] at this
  exact_mod_cast this

end Density_S4

section Density_S5
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Density_ntr_inv_smul_one (c : ℂ) : ntr ((c • (1 : Matrix ι ι ℂ))⁻¹) = c⁻¹ := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hc : c = 0
  · subst hc
    simp [ntr]
  · have : (c • (1 : Matrix ι ι ℂ))⁻¹ = c⁻¹ • 1 :=
      Matrix.inv_eq_right_inv (by
        rw [Matrix.smul_mul, Matrix.mul_smul, mul_one, smul_smul, mul_inv_cancel₀ hc, one_smul])
    rw [this]
    unfold ntr
    simp [Matrix.trace_one, hn]
    field_simp

private lemma Density_pred_zero (z w : ℂ) :
    ntr (((0 : Matrix ι ι ℂ) - (z + w) • (1 : Matrix ι ι ℂ))⁻¹) = -(z + w)⁻¹ := by
  rw [zero_sub, ← neg_smul, Density_ntr_inv_smul_one, inv_neg]

private lemma Density_mSol_zero_eq {z : ℂ} (hz : 0 < z.im) :
    mSol (0 : Matrix ι ι ℂ) z = mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z := by
  have h1 := mSol_spec (0 : Matrix ι ι ℂ) Matrix.isHermitian_zero z hz
  have h2 := mSol_spec (0 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.isHermitian_zero z hz
  obtain ⟨w, hw, huniq⟩ := mSol_existsUnique (0 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.isHermitian_zero z hz
  have e1 : mSol (0 : Matrix ι ι ℂ) z = -(z + mSol (0 : Matrix ι ι ℂ) z)⁻¹ := by
    have := h1.2.1
    rw [MSol, Density_pred_zero] at this
    exact this
  have e2 : mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z = -(z + mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z)⁻¹ := by
    have := h2.2.1
    rw [MSol, Density_pred_zero] at this
    exact this
  have p1 : 0 < (mSol (0 : Matrix ι ι ℂ) z).im ∧ mSol (0 : Matrix ι ι ℂ) z =
      ntr ((0 - (z + mSol (0 : Matrix ι ι ℂ) z) • (1 : Matrix (Fin 1) (Fin 1) ℂ))⁻¹) := by
    refine ⟨h1.1, ?_⟩
    rw [Density_pred_zero]
    exact e1
  have p2 : 0 < (mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z).im ∧ mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z =
      ntr ((0 - (z + mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z) • (1 : Matrix (Fin 1) (Fin 1) ℂ))⁻¹) :=
    ⟨h2.1, h2.2.1⟩
  rw [huniq _ p1, huniq _ p2]

private lemma Density_mExt_zero (z : ℂ) : mExt (0 : Matrix ι ι ℂ) z = msc z := by
  unfold msc
  by_cases h1 : 0 < z.im
  · simp only [mExt, h1, ↓reduceIte]
    exact Density_mSol_zero_eq h1
  by_cases h2 : z.im < 0
  · have h2' : 0 < (star z).im := by simpa using h2
    simp only [mExt, h1, h2, ↓reduceIte]
    rw [Density_mSol_zero_eq h2']
  · simp only [mExt, h1, h2, ↓reduceIte]
    unfold limUnder
    congr 1
    refine Filter.map_congr ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    have h3 : z.im = 0 := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
    apply Density_mSol_zero_eq
    simp [h3]
    exact hη


private lemma Density_zero_herm_norm : opNorm (0 : Matrix ι ι ℂ) ≤ 1 / 10 := by
  have : opNorm (0 : Matrix ι ι ℂ) = 0 := by
    unfold opNorm; simp
  rw [this]; norm_num

/-- The boundary equation `m² + x m + 1 = 0` for `Λ = 0` at a real point. -/
private lemma Density_zero_quadratic (x : ℝ) :
    mExt (0 : Matrix ι ι ℂ) x ^ 2 + (x : ℂ) * mExt (0 : Matrix ι ι ℂ) x + 1 = 0 := by
  obtain ⟨hn, hm, hinv⟩ := (mExt_boundary (0 : Matrix ι ι ℂ) Matrix.isHermitian_zero
    Density_zero_herm_norm).2 x
  set m := mExt (0 : Matrix ι ι ℂ) x with hmdef
  have hne : (x : ℂ) + m ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    have : opNorm (0 : Matrix ι ι ℂ) = 0 := by unfold opNorm; simp
    rw [this] at hn
    linarith
  have h2 : m = -((x : ℂ) + m)⁻¹ := by
    have := hm
    rw [MExt, Density_pred_zero] at this
    exact this
  field_simp at h2
  linear_combination h2

/-- At a real point, `Im m` is `√(4 - x²)/2` for `|x| < 2` and `0` otherwise. -/
private lemma Density_zero_im (x : ℝ) :
    (mExt (0 : Matrix ι ι ℂ) x).im = if |x| < 2 then Real.sqrt (4 - x ^ 2) / 2 else 0 := by
  have hq := Density_zero_quadratic (ι := ι) x
  have hb0 := Density_mExt_im_nonneg (Λ := (0 : Matrix ι ι ℂ)) Matrix.isHermitian_zero
    Density_zero_herm_norm x
  set m := mExt (0 : Matrix ι ι ℂ) x with hm
  have hre : m.re ^ 2 - m.im ^ 2 + x * m.re + 1 = 0 := by
    have := congrArg Complex.re hq
    simpa [sq, Complex.mul_re] using this
  have him : 2 * m.re * m.im + x * m.im = 0 := by
    have := congrArg Complex.im hq
    simp [sq, Complex.mul_im] at this
    linarith
  by_cases hx : |x| < 2
  · simp only [hx, ↓reduceIte]
    have hxx : x ^ 2 < 4 := by
      have := abs_lt.1 hx
      nlinarith
    have hbpos : 0 < m.im := by
      rcases hb0.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hre
        nlinarith [sq_nonneg (2 * m.re + x)]
    have hre2 : m.re = -x / 2 := by
      have : m.im * (2 * m.re + x) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    have hb2 : m.im ^ 2 = (4 - x ^ 2) / 4 := by
      rw [hre2] at hre
      nlinarith
    have : Real.sqrt (4 - x ^ 2) = 2 * m.im := by
      rw [show 4 - x ^ 2 = (2 * m.im) ^ 2 by nlinarith]
      exact Real.sqrt_sq (by positivity)
    rw [this]; ring
  · simp only [hx, ↓reduceIte]
    have hxx : 4 ≤ x ^ 2 := by
      have := not_lt.1 hx
      nlinarith [sq_abs x, abs_nonneg x]
    by_contra hne
    have hbpos : 0 < m.im := lt_of_le_of_ne hb0 (Ne.symm hne)
    have hre2 : m.re = -x / 2 := by
      have : m.im * (2 * m.re + x) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    rw [hre2] at hre
    nlinarith

private lemma Density_rho_zero_eq (x : ℝ) : rho (0 : Matrix ι ι ℂ) x = rhoSc x := by
  rw [Density_rho_eq Matrix.isHermitian_zero Density_zero_herm_norm, Density_zero_im]
  unfold rhoSc
  by_cases hx : |x| < 2
  · have : x ∈ Set.Icc (-2 : ℝ) 2 := ⟨by linarith [(abs_lt.1 hx).1], by linarith [(abs_lt.1 hx).2]⟩
    simp only [hx, this, ↓reduceIte]
    field_simp
  · simp only [hx, ↓reduceIte]
    by_cases h2 : x ∈ Set.Icc (-2 : ℝ) 2
    · simp only [h2, ↓reduceIte]
      have : x ^ 2 = 4 := by
        have := abs_le.2 h2
        have h3 := not_lt.1 hx
        nlinarith [sq_abs x, abs_nonneg x]
      rw [this]; simp
    · simp [h2]


private lemma Density_support_rhoSc : Function.support rhoSc = Set.Ioo (-2 : ℝ) 2 := by
  ext x
  simp only [Function.mem_support, Set.mem_Ioo, rhoSc]
  by_cases h : x ∈ Set.Icc (-2 : ℝ) 2
  · simp only [h, ↓reduceIte]
    constructor
    · intro hne
      have hpos : 0 < Real.sqrt (4 - x ^ 2) := by
        rcases (Real.sqrt_nonneg (4 - x ^ 2)).lt_or_eq with h1 | h1
        · exact h1
        · exfalso; apply hne; rw [← h1]; simp
      have := Real.sqrt_pos.1 hpos
      constructor <;> nlinarith [h.1, h.2]
    · rintro ⟨h1, h2⟩
      have : 0 < 4 - x ^ 2 := by nlinarith
      have := Real.sqrt_pos.2 this
      positivity
  · simp only [h, ↓reduceIte]
    constructor
    · intro hne; exact absurd rfl hne
    · rintro ⟨h1, h2⟩
      exact absurd ⟨h1.le, h2.le⟩ h

private lemma Density_zero_edges :
    Eplus (0 : Matrix ι ι ℂ) = 2 ∧ Eminus (0 : Matrix ι ι ℂ) = -2 := by
  have h : Function.support (rho (0 : Matrix ι ι ℂ)) = Set.Ioo (-2 : ℝ) 2 := by
    have : rho (0 : Matrix ι ι ℂ) = rhoSc := funext Density_rho_zero_eq
    rw [this, Density_support_rhoSc]
  constructor
  · unfold Eplus; rw [h]; exact csSup_Ioo (by norm_num)
  · unfold Eminus; rw [h]; exact csInf_Ioo (by norm_num)

private lemma Density_zero_gamma :
    gammaPlus (0 : Matrix ι ι ℂ) = 1 ∧ gammaMinus (0 : Matrix ι ι ℂ) = 1 := by
  obtain ⟨hp, hm⟩ := Density_zero_edges (ι := ι)
  have hrho : rho (0 : Matrix ι ι ℂ) = rhoSc := funext Density_rho_zero_eq
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  constructor
  · unfold gammaPlus
    rw [hp, hrho]
    have hlim : Tendsto (fun E : ℝ => rhoSc E / Real.sqrt (2 - E)) (𝓝[<] (2 : ℝ)) (𝓝 (1 / Real.pi)) := by
      have h1 : Tendsto (fun E : ℝ => Real.sqrt (2 + E) / (2 * Real.pi)) (𝓝[<] (2 : ℝ))
          (𝓝 (Real.sqrt (2 + 2) / (2 * Real.pi))) := by
        have : Continuous (fun E : ℝ => Real.sqrt (2 + E) / (2 * Real.pi)) := by fun_prop
        exact (this.tendsto 2).mono_left nhdsWithin_le_nhds
      have h2 : Real.sqrt (2 + 2) / (2 * Real.pi) = 1 / Real.pi := by
        rw [show (2 : ℝ) + 2 = 4 by norm_num, hs4]; field_simp
      rw [h2] at h1
      refine h1.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show (-2 : ℝ) < 2 by norm_num)] with E hE
      have hmem : E ∈ Set.Icc (-2 : ℝ) 2 := ⟨hE.1.le, hE.2.le⟩
      have hpos : 0 < 2 - E := by linarith [hE.2]
      unfold rhoSc
      simp only [hmem, ↓reduceIte]
      rw [show 4 - E ^ 2 = (2 - E) * (2 + E) by ring, Real.sqrt_mul hpos.le]
      have : Real.sqrt (2 - E) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
      field_simp
    rw [hlim.limUnder_eq]
    rw [mul_one_div_cancel hπ, Real.one_rpow]
  · unfold gammaMinus
    rw [hm, hrho]
    have hlim : Tendsto (fun E : ℝ => rhoSc E / Real.sqrt (E - -2)) (𝓝[>] (-2 : ℝ)) (𝓝 (1 / Real.pi)) := by
      have h1 : Tendsto (fun E : ℝ => Real.sqrt (2 - E) / (2 * Real.pi)) (𝓝[>] (-2 : ℝ))
          (𝓝 (Real.sqrt (2 - -2) / (2 * Real.pi))) := by
        have : Continuous (fun E : ℝ => Real.sqrt (2 - E) / (2 * Real.pi)) := by fun_prop
        exact (this.tendsto (-2)).mono_left nhdsWithin_le_nhds
      have h2 : Real.sqrt (2 - -2) / (2 * Real.pi) = 1 / Real.pi := by
        rw [show (2 : ℝ) - -2 = 4 by norm_num, hs4]; field_simp
      rw [h2] at h1
      refine h1.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (-2 : ℝ) < 2 by norm_num)] with E hE
      have hmem : E ∈ Set.Icc (-2 : ℝ) 2 := ⟨hE.1.le, hE.2.le⟩
      have hpos : 0 < E - -2 := by linarith [hE.1]
      unfold rhoSc
      simp only [hmem, ↓reduceIte]
      rw [show 4 - E ^ 2 = (E - -2) * (2 - E) by ring, Real.sqrt_mul hpos.le]
      have : Real.sqrt (E - -2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
      field_simp
    rw [hlim.limUnder_eq]
    rw [mul_one_div_cancel hπ, Real.one_rpow]


private lemma Density_msc_quad {z : ℂ} (hz : 0 < z.im) : msc z ^ 2 + z * msc z + 1 = 0 ∧ 0 < (msc z).im := by
  have h0 : msc z = mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z := by
    unfold msc; simp [mExt, hz]
  rw [h0]
  have h2 := mSol_spec (0 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.isHermitian_zero z hz
  refine ⟨?_, h2.1⟩
  set m := mSol (0 : Matrix (Fin 1) (Fin 1) ℂ) z
  have e2 : m = -(z + m)⁻¹ := by
    have := h2.2.1
    rw [MSol, Density_pred_zero] at this
    exact this
  have hne : z + m ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith [h2.1]
  field_simp at e2
  linear_combination e2

end Density_S5

section Density_S6

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Density_continuousAt_inv {X : Type*} [TopologicalSpace X] {A : X → Matrix ι ι ℂ} {x : X}
    (hA : ContinuousAt A x) (hu : IsUnit (A x)) : ContinuousAt (fun y => (A y)⁻¹) x := by
  have hdet : ContinuousAt Ring.inverse (A x).det := by
    have : (A x).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _ |>.1 hu).ne_zero
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ this
  exact (continuousAt_matrix_inv (A x) hdet).comp hA

private lemma Density_continuous_ntr : Continuous (fun B : Matrix ι ι ℂ => ntr B) := by
  unfold ntr
  exact continuous_const.mul (Continuous.matrix_trace continuous_id)

private lemma Density_continuous_phi {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    Continuous (fun E : ℝ => ntr (MExt Λ E * (MExt Λ E)ᴴ)) := by
  have hm : Continuous (fun E : ℝ => (E : ℂ) + mExt Λ (E : ℂ)) :=
    Complex.continuous_ofReal.add (Density_mExt_continuous hΛ hℓ)
  have hA : Continuous (fun E : ℝ => Λ - ((E : ℂ) + mExt Λ (E : ℂ)) • (1 : Matrix ι ι ℂ)) :=
    continuous_const.sub (hm.smul continuous_const)
  have hM : Continuous (fun E : ℝ => MExt Λ E) := by
    refine continuous_iff_continuousAt.2 fun E => ?_
    have hu : IsUnit (Λ - ((E : ℂ) + mExt Λ (E : ℂ)) • (1 : Matrix ι ι ℂ)) := by
      have := ((mExt_boundary Λ hΛ hℓ).2 E).2.2
      exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse this)
    exact Density_continuousAt_inv hA.continuousAt hu
  exact Density_continuous_ntr.comp (hM.matrix_mul hM.matrix_conjTranspose)


private lemma Density_equation_E {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (E : ℝ)
    (hE : E ∈ Set.Icc (Eminus Λ) (Eplus Λ)) : ntr (MExt Λ E * (MExt Λ E)ᴴ) = 1 := by
  obtain ⟨hlt, -⟩ := rho_support Λ hΛ hℓ
  have hcont := Density_continuous_phi hΛ hℓ
  have hbulk : Set.EqOn (fun E : ℝ => ntr (MExt Λ E * (MExt Λ E)ᴴ)) (fun _ => (1 : ℂ))
      (Set.Ioo (Eminus Λ) (Eplus Λ)) := by
    intro E hE
    obtain ⟨t, ht, -, -, hid⟩ := Density_boundary_identity hΛ hℓ E
    have hpos := Density_rho_pos hΛ hℓ hE
    rw [Density_rho_eq hΛ hℓ] at hpos
    have him : 0 < (mExt Λ E).im := by
      have := (div_pos_iff_of_pos_right Real.pi_pos).1 hpos
      exact this
    have ht1 : t = 1 := by
      have : (mExt Λ E).im * (t - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    show ntr (MExt Λ E * (MExt Λ E)ᴴ) = 1
    rw [ht, ht1]; simp
  have := hbulk.of_subset_closure hcont.continuousOn continuousOn_const Set.Ioo_subset_Icc_self
    (by rw [closure_Ioo hlt.ne])
  exact this hE

end Density_S6

section Density_S7
open Set

/-- The Poisson kernel `K_η(s) = π⁻¹ η (s² + η²)⁻¹`. -/
private def Density_K (η s : ℝ) : ℝ := Real.pi⁻¹ * η * (s ^ 2 + η ^ 2)⁻¹

private lemma Density_K_den_pos {η : ℝ} (hη : 0 < η) (s : ℝ) : 0 < s ^ 2 + η ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg s) (pow_pos hη 2)

private lemma Density_K_integrable {η : ℝ} (hη : 0 < η) : Integrable (Density_K η) := by
  have := ProbabilityTheory.integrable_cauchyPDFReal 0 (γ := ⟨η, hη.le⟩)
  refine this.congr (Filter.Eventually.of_forall fun s => ?_)
  show Real.pi⁻¹ * η * ((s - 0) ^ 2 + η ^ 2)⁻¹ = Density_K η s
  simp [Density_K]

/-- `∫_{y > x} K_η(y - u) dy = 1/2 - arctan((x - u)/η)/π`. -/
private lemma Density_Qint {η : ℝ} (hη : 0 < η) (x u : ℝ) :
    ∫ y in Ioi x, Density_K η (y - u) = 1 / 2 - Real.arctan ((x - u) / η) / Real.pi := by
  have hπ := Real.pi_pos
  have hder : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.arctan ((y - u) / η) / Real.pi)
      (Density_K η (y - u)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y - u) / η) (1 / η) y := by
      simpa using ((hasDerivAt_id y).sub_const u).div_const η
    have h2 := (h1.arctan).div_const Real.pi
    convert h2 using 1
    unfold Density_K
    field_simp
    ring
  have hint : IntegrableOn (fun y : ℝ => Density_K η (y - u)) (Ioi x) :=
    ((Density_K_integrable hη).comp_sub_right u).integrableOn
  have hlim : Tendsto (fun y : ℝ => Real.arctan ((y - u) / η) / Real.pi) atTop (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun y : ℝ => (y - u) / η) atTop atTop := by
      refine Tendsto.atTop_div_const hη ?_
      exact tendsto_atTop_add_const_right _ _ tendsto_id
    have h2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
    have h3 := h2.div_const Real.pi
    have h4 : (Real.pi / 2) / Real.pi = 1 / 2 := by field_simp
    rw [h4] at h3
    exact h3
  have := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun y : ℝ => Real.arctan ((y - u) / η) / Real.pi)
    (f' := fun y => Density_K η (y - u)) (a := x) (m := 1 / 2)
    (hder x).continuousAt.continuousWithinAt (fun y _ => hder y) hint hlim
  rw [this]

/-- The error of the cumulative kernel against the step function. -/
private lemma Density_Q_err {η : ℝ} (hη : 0 < η) (s : ℝ) :
    |1 / 2 - Real.arctan (s / η) / Real.pi - (if s < 0 then (1 : ℝ) else 0)| ≤ 1 / 2 ∧
      (0 < |s| → |1 / 2 - Real.arctan (s / η) / Real.pi - (if s < 0 then (1 : ℝ) else 0)| ≤
        η / (Real.pi * |s|)) := by
  have hπ := Real.pi_pos
  have h2 : Real.arctan (|s| / η) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have h3 : 0 ≤ Real.arctan (|s| / η) := Real.arctan_nonneg.2 (by positivity)
  have hnn : 0 ≤ 1 / 2 - Real.arctan (|s| / η) / Real.pi := by
    have : Real.arctan (|s| / η) / Real.pi ≤ 1 / 2 := by
      rw [div_le_iff₀ hπ]; linarith
    linarith
  have hval : |1 / 2 - Real.arctan (s / η) / Real.pi - (if s < 0 then (1 : ℝ) else 0)| =
      1 / 2 - Real.arctan (|s| / η) / Real.pi := by
    by_cases hs : s < 0
    · simp only [hs, ↓reduceIte]
      have e1 : Real.arctan (s / η) = -Real.arctan (|s| / η) := by
        rw [← Real.arctan_neg, abs_of_neg hs]; ring_nf
      have e2 : 1 / 2 - Real.arctan (s / η) / Real.pi - 1 =
          -(1 / 2 - Real.arctan (|s| / η) / Real.pi) := by
        rw [e1]; ring
      rw [e2, abs_neg, abs_of_nonneg hnn]
    · simp only [hs, ↓reduceIte, sub_zero, abs_of_nonneg (not_lt.1 hs)]
      exact abs_of_nonneg (by rwa [abs_of_nonneg (not_lt.1 hs)] at hnn)
  rw [hval]
  refine ⟨?_, fun hs => ?_⟩
  · have : 0 ≤ Real.arctan (|s| / η) / Real.pi := by positivity
    linarith
  · have hd : 0 < |s| / η := by positivity
    have h4 := Real.arctan_inv_of_pos hd
    have h5 : Real.arctan (η / |s|) ≤ η / |s| := by
      have h6 : Real.arctan (η / |s|) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
      have h7 := Real.le_tan (Real.arctan_nonneg.2 (by positivity : 0 ≤ η / |s|)) h6
      rwa [Real.tan_arctan] at h7
    have h8 : (|s| / η)⁻¹ = η / |s| := by rw [inv_div]
    rw [h8] at h4
    have : 1 / 2 - Real.arctan (|s| / η) / Real.pi = Real.arctan (η / |s|) / Real.pi := by
      rw [h4]; field_simp
    rw [this, div_le_iff₀ hπ]
    calc Real.arctan (η / |s|) ≤ η / |s| := h5
      _ = η / (Real.pi * |s|) * Real.pi := by field_simp


private lemma Density_smooth {ρ : ℝ → ℝ} (hρ : Integrable ρ) (h0 : ∀ u, 0 ≤ ρ u) (hB : ∀ u, ρ u ≤ 1 / Real.pi)
    (hm : ∫ u, ρ u = 1) {η : ℝ} (hη : 0 < η) (x : ℝ) :
    IntegrableOn (fun y => ∫ u, ρ u * Density_K η (y - u)) (Ioi x) ∧
      |(∫ y in Ioi x, ∫ u, ρ u * Density_K η (y - u)) - ∫ u in Ioi x, ρ u| ≤
        2 * Real.sqrt η / Real.pi := by
  have hπ := Real.pi_pos
  have hfi : Integrable (fun p : ℝ × ℝ => ρ p.2 * Density_K η (p.1 - p.2)) (volume.prod volume) := by
    have := hρ.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) (Density_K_integrable hη)
    simpa using this
  have hfi' : Integrable (Function.uncurry fun (y u : ℝ) => ρ u * Density_K η (y - u))
      ((volume.restrict (Ioi x)).prod volume) := by
    have h1 : (volume.restrict (Ioi x)).prod (volume : Measure ℝ) =
        (volume.prod volume).restrict (Ioi x ×ˢ (univ : Set ℝ)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [h1]
    exact hfi.restrict
  refine ⟨hfi'.integral_prod_left, ?_⟩
  -- Fubini
  have hswap : (∫ y in Ioi x, ∫ u, ρ u * Density_K η (y - u)) =
      ∫ u, ρ u * (1 / 2 - Real.arctan ((x - u) / η) / Real.pi) := by
    rw [integral_integral_swap hfi']
    congr 1
    funext u
    rw [integral_const_mul, Density_Qint hη x u]
  have hstep : (∫ u in Ioi x, ρ u) = ∫ u, ρ u * (if x - u < 0 then (1 : ℝ) else 0) := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1
    funext u
    by_cases h : x < u
    · simp [Set.indicator, h, sub_neg.2 h]
    · simp [Set.indicator, h, not_lt.1 h, sub_nonneg.2 (not_lt.1 h)]
  set Q : ℝ → ℝ := fun u => 1 / 2 - Real.arctan ((x - u) / η) / Real.pi with hQ
  have hQc : Continuous Q := by
    have : Continuous (fun u : ℝ => Real.arctan ((x - u) / η)) :=
      Real.continuous_arctan.comp ((continuous_const.sub continuous_id).div_const _)
    exact continuous_const.sub (this.div_const _)
  have hQb : ∀ u, |Q u| ≤ 1 := by
    intro u
    have h1 := Real.arctan_lt_pi_div_two ((x - u) / η)
    have h2 := Real.neg_pi_div_two_lt_arctan ((x - u) / η)
    have h3 : Real.arctan ((x - u) / η) / Real.pi < 1 / 2 := by
      rw [div_lt_iff₀ hπ]; linarith
    have h4 : -(1 / 2) < Real.arctan ((x - u) / η) / Real.pi := by
      rw [lt_div_iff₀ hπ]; linarith
    rw [abs_le]
    constructor <;> simp only [hQ] <;> linarith
  have hint1 : Integrable (fun u => ρ u * Q u) := by
    refine Integrable.mono' hρ (hρ.aestronglyMeasurable.mul hQc.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, Real.norm_of_nonneg (h0 u), Real.norm_eq_abs]
    calc ρ u * |Q u| ≤ ρ u * 1 := mul_le_mul_of_nonneg_left (hQb u) (h0 u)
      _ = ρ u := mul_one _
  have hint2 : Integrable (fun u => ρ u * (if x - u < 0 then (1 : ℝ) else 0)) := by
    have : (fun u => ρ u * (if x - u < 0 then (1 : ℝ) else 0)) = (Ioi x).indicator ρ := by
      funext u
      by_cases h : x < u
      · simp [Set.indicator, h, sub_neg.2 h]
      · simp [Set.indicator, h, not_lt.1 h, sub_nonneg.2 (not_lt.1 h)]
    rw [this]
    exact hρ.indicator measurableSet_Ioi
  rw [hswap, hstep, ← integral_sub hint1 hint2]
  -- pointwise bound
  set δ := Real.sqrt η with hδ
  have hδpos : 0 < δ := Real.sqrt_pos.2 hη
  have hδsq : δ * δ = η := Real.mul_self_sqrt hη.le
  set bnd : ℝ → ℝ := fun u => (Ioo (x - δ) (x + δ)).indicator (fun _ => 1 / (2 * Real.pi)) u +
    η / (Real.pi * δ) * ρ u with hbnd
  have hbint : Integrable bnd := by
    refine Integrable.add ?_ (hρ.const_mul _)
    exact (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp))
  have hpt : ∀ u, ‖ρ u * Q u - ρ u * (if x - u < 0 then (1 : ℝ) else 0)‖ ≤ bnd u := by
    intro u
    obtain ⟨e1, e2⟩ := Density_Q_err hη (x - u)
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (h0 u), Real.norm_eq_abs]
    have hnn : 0 ≤ η / (Real.pi * δ) * ρ u := by have := h0 u; positivity
    by_cases hnear : u ∈ Ioo (x - δ) (x + δ)
    · simp only [hbnd, Set.indicator_of_mem hnear]
      have : ρ u * |Q u - if x - u < 0 then (1 : ℝ) else 0| ≤ 1 / Real.pi * (1 / 2) :=
        mul_le_mul (hB u) e1 (abs_nonneg _) (by positivity)
      have h5 : 1 / Real.pi * (1 / 2) = 1 / (2 * Real.pi) := by field_simp
      linarith
    · simp only [hbnd, Set.indicator_of_notMem hnear]
      have hfar : δ ≤ |x - u| := by
        rw [mem_Ioo, not_and_or, not_lt, not_lt] at hnear
        rcases hnear with h | h
        · rw [abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith)]; linarith
      have hs : 0 < |x - u| := lt_of_lt_of_le hδpos hfar
      have h6 := e2 hs
      have h7 : η / (Real.pi * |x - u|) ≤ η / (Real.pi * δ) := by
        gcongr
      have : ρ u * |Q u - if x - u < 0 then (1 : ℝ) else 0| ≤ ρ u * (η / (Real.pi * δ)) :=
        mul_le_mul_of_nonneg_left (h6.trans h7) (h0 u)
      linarith
  have hnorm := norm_integral_le_of_norm_le hbint (Filter.Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  simp only [hbnd]
  rw [integral_add ((integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp)))
    (hρ.const_mul _), integral_const_mul, hm, integral_indicator measurableSet_Ioo]
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith)]
  simp only [smul_eq_mul]
  have : η / (Real.pi * δ) = δ / Real.pi := by
    rw [← hδsq]; field_simp
  rw [this]
  field_simp
  ring

end Density_S7

section Density_S8
open Set
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `Λ - ζ` is invertible when `‖Λ‖ < |ζ|`. -/
private lemma Density_isUnit_sub {Λ : Matrix ι ι ℂ} {ζ : ℂ} (h : opNorm Λ < ‖ζ‖) :
    IsUnit (Λ - ζ • (1 : Matrix ι ι ℂ)) := by
  have h : ‖Λ‖ < ‖ζ‖ := h
  have hnot : ζ ∉ spectrum ℂ Λ := by
    intro hm
    have := spectrum.subset_closedBall_norm Λ hm
    simp at this
    linarith
  rw [spectrum.mem_iff, not_not] at hnot
  have := hnot.neg
  convert this using 1
  rw [Algebra.algebraMap_eq_smul_one]
  abel

/-- For `Im ζ > 0`, `Im ⟨(Λ - ζ)⁻¹⟩ > 0`. -/
private lemma Density_im_ntr_inv {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) {ζ : ℂ} (hζ : 0 < ζ.im)
    (hu : IsUnit (Λ - ζ • (1 : Matrix ι ι ℂ))) :
    0 < (ntr (Λ - ζ • (1 : Matrix ι ι ℂ))⁻¹).im := by
  set M := (Λ - ζ • (1 : Matrix ι ι ℂ))⁻¹ with hMdef
  have hM : (Λ - ζ • (1 : Matrix ι ι ℂ)) * M = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have hid := Density_im_identity hΛ hM
  have h1 := congrArg ntr hid
  have e1 : ntr (M - Mᴴ) = ntr M - star (ntr M) := by
    rw [← Density_ntr_conjTranspose]
    unfold ntr
    rw [Matrix.trace_sub, mul_sub]
  have e2 : ntr ((2 * Complex.I * (ζ.im : ℂ)) • (M * Mᴴ)) =
      (2 * Complex.I * (ζ.im : ℂ)) * ntr (M * Mᴴ) := by
    unfold ntr
    rw [Matrix.trace_smul, smul_eq_mul]
    ring
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hM
    exact zero_ne_one hM
  obtain ⟨t, ht0, hte, htpos, -⟩ := Density_ntr_mul_self_facts M
  rw [e1, e2, hte, Complex.star_def, Complex.sub_conj] at h1
  have h2 : (2 * Complex.I) * (((ntr M).im : ℝ) : ℂ) = (2 * Complex.I) * ((ζ.im * t : ℝ) : ℂ) := by
    push_cast at h1 ⊢
    linear_combination h1
  have h3 := mul_left_cancel₀ (by simp : (2 * Complex.I : ℂ) ≠ 0) h2
  have h4 : (ntr M).im = ζ.im * t := by exact_mod_cast h3
  rw [h4]
  exact mul_pos hζ (htpos hM0)

end Density_S8

section Density_S9
open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A cluster point of `f` along `l` inherits a closed relation. -/
private lemma Density_cluster_mem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {l : Filter X}
    {x₀ : X} {f : X → Y} {y : Y} (hl : Tendsto id l (𝓝 x₀)) (hy : MapClusterPt y l f)
    {C : Set (X × Y)} (hC : IsClosed C) (h : ∀ᶠ x in l, (x, f x) ∈ C) : (x₀, y) ∈ C := by
  by_contra hmem
  have hopen : IsOpen Cᶜ := hC.isOpen_compl
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 (hopen.mem_nhds hmem)
  have h1 : ∃ᶠ x in l, f x ∈ V := mapClusterPt_iff_frequently.1 hy V hV
  have h2 : ∀ᶠ x in l, x ∈ U := hl hU
  obtain ⟨x, hxV, hxU, hxC⟩ : ∃ x, f x ∈ V ∧ x ∈ U ∧ (x, f x) ∈ C := by
    obtain ⟨x, hx⟩ := (h1.and_eventually (h2.and h)).exists
    exact ⟨x, hx.1, hx.2.1, hx.2.2⟩
  exact hUV (Set.mk_mem_prod hxU hxV) hxC

private lemma Density_mSol_continuousOn {Λt : ℝ → Matrix ι ι ℂ} (hc : Continuous Λt)
    (hH : ∀ t, (Λt t).IsHermitian) (hℓ : ∀ t, opNorm (Λt t) ≤ 1 / 10) :
    ContinuousOn (fun p : ℝ × ℂ => mSol (Λt p.1) p.2) {p : ℝ × ℂ | 0 < p.2.im} := by
  have hopen : IsOpen {p : ℝ × ℂ | 0 < p.2.im} :=
    isOpen_lt continuous_const (Complex.continuous_im.comp continuous_snd)
  refine fun p₀ hp₀ => ContinuousAt.continuousWithinAt ?_
  set f : ℝ × ℂ → ℂ := fun p => mSol (Λt p.1) p.2 with hf
  have hev : ∀ᶠ p in 𝓝 p₀, 0 < p.2.im := hopen.mem_nhds hp₀
  -- the closed set of approximate solutions
  set C₁ : Set ((ℝ × ℂ) × ℂ) := {q | 9 / 10 ≤ ‖q.1.2 + q.2‖} ∩ {q | 0 ≤ q.2.im} with hC₁
  have hC₁c : IsClosed C₁ := by
    refine IsClosed.inter (isClosed_le continuous_const ?_) (isClosed_le continuous_const ?_)
    · exact ((continuous_snd.comp continuous_fst).add continuous_snd).norm
    · exact Complex.continuous_im.comp continuous_snd
  set G : (ℝ × ℂ) × ℂ → ℂ := fun q => q.2 - ntr ((Λt q.1.1 - (q.1.2 + q.2) • (1 : Matrix ι ι ℂ))⁻¹)
    with hG
  have hGc : ContinuousOn G C₁ := by
    intro q hq
    refine ContinuousAt.continuousWithinAt ?_
    have hA : Continuous (fun q : (ℝ × ℂ) × ℂ => Λt q.1.1 - (q.1.2 + q.2) • (1 : Matrix ι ι ℂ)) := by
      refine (hc.comp (continuous_fst.comp continuous_fst)).sub ?_
      exact ((continuous_snd.comp continuous_fst).add continuous_snd).smul continuous_const
    have h9 : 9 / 10 ≤ ‖q.1.2 + q.2‖ := hq.1
    have hu : IsUnit (Λt q.1.1 - (q.1.2 + q.2) • (1 : Matrix ι ι ℂ)) :=
      Density_isUnit_sub (lt_of_le_of_lt (hℓ _) (by linarith))
    have hinv := Density_continuousAt_inv hA.continuousAt hu
    exact continuous_snd.continuousAt.sub (Density_continuous_ntr.continuousAt.comp hinv)
  set C : Set ((ℝ × ℂ) × ℂ) := C₁ ∩ G ⁻¹' {0} with hCdef
  have hCc : IsClosed C := hGc.preimage_isClosed_of_isClosed hC₁c isClosed_singleton
  have hmemC : ∀ p : ℝ × ℂ, 0 < p.2.im → (p, f p) ∈ C := by
    intro p hp
    have hs := mSol_spec (Λt p.1) (hH p.1) p.2 hp
    have ha := mSol_apriori (Λt p.1) (hH p.1) (hℓ p.1) p.2 hp
    refine ⟨⟨?_, hs.1.le⟩, ?_⟩
    · have := ha.1
      have := hℓ p.1
      show 9 / 10 ≤ ‖p.2 + mSol (Λt p.1) p.2‖
      linarith
    · show G (p, f p) = 0
      simp only [hG, hf]
      have := hs.2.1
      rw [MSol] at this
      rw [← this, sub_self]
  have hbd : ∀ᶠ p in 𝓝 p₀, f p ∈ Metric.closedBall (0 : ℂ) 1 := by
    filter_upwards [hev] with p hp
    rw [mem_closedBall_zero_iff]
    exact (mSol_apriori (Λt p.1) (hH p.1) (hℓ p.1) p.2 hp).2.1.le
  refine (isCompact_closedBall (0 : ℂ) 1).tendsto_nhds_of_unique_mapClusterPt hbd ?_
  intro m hm hclus
  have hmem : (p₀, m) ∈ C := by
    refine Density_cluster_mem (l := 𝓝 p₀) (f := f) tendsto_id hclus hCc ?_
    filter_upwards [hev] with p hp using hmemC p hp
  obtain ⟨⟨hn', him'⟩, hG0⟩ := hmem
  have hn : 9 / 10 ≤ ‖p₀.2 + m‖ := hn'
  have him : 0 ≤ m.im := him'
  have hG0' : m = ntr ((Λt p₀.1 - (p₀.2 + m) • (1 : Matrix ι ι ℂ))⁻¹) := by
    have : G (p₀, m) = 0 := hG0
    simp only [hG] at this
    exact sub_eq_zero.1 this
  have hu : IsUnit (Λt p₀.1 - (p₀.2 + m) • (1 : Matrix ι ι ℂ)) :=
    Density_isUnit_sub (lt_of_le_of_lt (hℓ _) (by linarith [hn]))
  have hpos : 0 < ((p₀.2 + m)).im := by
    have : 0 < p₀.2.im := hp₀
    simp only [Complex.add_im]
    linarith [him]
  have hmim : 0 < m.im := by
    have := Density_im_ntr_inv (hH p₀.1) hpos hu
    rw [← hG0'] at this
    exact this
  obtain ⟨w, hw, huniq⟩ := mSol_existsUnique (Λt p₀.1) (hH p₀.1) p₀.2 hp₀
  have h1 : 0 < m.im ∧ m = ntr (Λt p₀.1 - (p₀.2 + m) • (1 : Matrix ι ι ℂ))⁻¹ := ⟨hmim, hG0'⟩
  have hs := mSol_spec (Λt p₀.1) (hH p₀.1) p₀.2 hp₀
  have h2 : 0 < (mSol (Λt p₀.1) p₀.2).im ∧ mSol (Λt p₀.1) p₀.2 =
      ntr (Λt p₀.1 - (p₀.2 + mSol (Λt p₀.1) p₀.2) • (1 : Matrix ι ι ℂ))⁻¹ := by
    refine ⟨hs.1, ?_⟩
    have := hs.2.1
    rw [MSol] at this
    exact this
  rw [huniq m h1]
  exact (huniq _ h2).symm

end Density_S9

section Density_S10
open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `T(x) = ∫_{(x, ∞)} ρ_N`. -/
private def Density_T (Λ : Matrix ι ι ℂ) (x : ℝ) : ℝ := ∫ E in Ioi x, rho Λ E

private lemma Density_T_of_ge {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {x : ℝ}
    (hx : Eplus Λ ≤ x) : Density_T Λ x = 0 := by
  unfold Density_T
  refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
  refine Density_rho_eq_zero hΛ hℓ fun h => ?_
  have := h.2
  have : x < u := hu
  linarith [h.2]

private lemma Density_T_of_le {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {x : ℝ}
    (hx : x ≤ Eminus Λ) : Density_T Λ x = 1 := by
  unfold Density_T
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, Density_mass hΛ hℓ]
  intro u hu
  refine Density_rho_eq_zero hΛ hℓ fun h => ?_
  have : ¬ x < u := hu
  push Not at this
  linarith [h.1]

private lemma Density_T_sub {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {x y : ℝ}
    (hxy : x ≤ y) : Density_T Λ x - Density_T Λ y = ∫ u in x..y, rho Λ u := by
  unfold Density_T
  exact intervalIntegral.integral_Ioi_sub_Ioi (Density_rho_integrable hΛ hℓ).integrableOn hxy

private lemma Density_T_antitone {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    Antitone (Density_T Λ) := by
  intro x y hxy
  have := Density_T_sub hΛ hℓ hxy
  have h0 : 0 ≤ ∫ u in x..y, rho Λ u :=
    intervalIntegral.integral_nonneg hxy fun u _ => Density_rho_nonneg hΛ hℓ u
  linarith

private lemma Density_T_continuous {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    Continuous (Density_T Λ) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (rho Λ) volume a b := fun a b =>
    (Density_rho_continuous hΛ hℓ).intervalIntegrable a b
  have hprim := intervalIntegral.continuous_primitive hint 0
  have : Density_T Λ = fun x => Density_T Λ 0 - ∫ u in (0 : ℝ)..x, rho Λ u := by
    funext x
    rcases le_total 0 x with h | h
    · rw [← Density_T_sub hΛ hℓ h]; ring
    · have := Density_T_sub hΛ hℓ h
      rw [intervalIntegral.integral_symm]
      linarith
  rw [this]
  exact continuous_const.sub hprim

private lemma Density_T_strictAnti {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {x y : ℝ}
    (hx : Eminus Λ ≤ x) (hxy : x < y) (hy : y ≤ Eplus Λ) : Density_T Λ y < Density_T Λ x := by
  have h1 := Density_T_sub hΛ hℓ hxy.le
  have hpos : 0 < ∫ u in x..y, rho Λ u := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Density_rho_continuous hΛ hℓ).intervalIntegrable x y) (fun u hu => ?_) hxy
    exact Density_rho_pos hΛ hℓ ⟨lt_of_le_of_lt hx hu.1, lt_of_lt_of_le hu.2 hy⟩
  linarith

/-- The quantile of `ρ_N` at level `p ∈ (0,1)` is the unique `γ ∈ (E⁻, E⁺)` with `T γ = p`, and
`{x : p ≤ T x} = (-∞, γ]`. -/
private lemma Density_quant_spec {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ γ : ℝ, Eminus Λ < γ ∧ γ < Eplus Λ ∧ Density_T Λ γ = p ∧ ∀ x, p ≤ Density_T Λ x ↔ x ≤ γ := by
  obtain ⟨hlt, -⟩ := rho_support Λ hΛ hℓ
  have hc := Density_T_continuous hΛ hℓ
  have h0 := Density_T_of_ge hΛ hℓ (le_refl (Eplus Λ))
  have h1 := Density_T_of_le hΛ hℓ (le_refl (Eminus Λ))
  obtain ⟨γ, hγ, hTγ⟩ := intermediate_value_Icc' hlt.le hc.continuousOn
    (show p ∈ Icc (Density_T Λ (Eplus Λ)) (Density_T Λ (Eminus Λ)) by rw [h0, h1]; exact ⟨hp0.le, hp1.le⟩)
  have hne1 : γ ≠ Eminus Λ := fun h => by rw [h, h1] at hTγ; linarith
  have hne2 : γ ≠ Eplus Λ := fun h => by rw [h, h0] at hTγ; linarith
  have hγ1 : Eminus Λ < γ := lt_of_le_of_ne hγ.1 (Ne.symm hne1)
  have hγ2 : γ < Eplus Λ := lt_of_le_of_ne hγ.2 hne2
  refine ⟨γ, hγ1, hγ2, hTγ, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · by_contra hcon
    push Not at hcon
    rcases le_or_gt (Eplus Λ) x with h | h
    · rw [Density_T_of_ge hΛ hℓ h] at hx; linarith
    · have := Density_T_strictAnti hΛ hℓ hγ1.le hcon h.le
      linarith
  · have := Density_T_antitone hΛ hℓ hx
    linarith

private lemma Density_quant_eq {Λ : Matrix ι ι ℂ} {p : ℝ} {γ : ℝ}
    (h : ∀ x, p ≤ Density_T Λ x ↔ x ≤ γ) (Mc k : ℕ) (hp : ((k : ℝ) - 1 / 2) / Mc = p) :
    quant (rho Λ) Mc k = γ := by
  unfold quant
  have : {x : ℝ | ((k : ℝ) - 1 / 2) / Mc ≤ ∫ E in Ioi x, rho Λ E} = Iic γ := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_Iic]
    rw [hp]
    exact h x
  rw [this]
  exact csSup_Iic

end Density_S10

section Density_S11
open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `π⁻¹ Im m(y + iη)` is the Poisson smoothing of `ρ_N`. -/
private lemma Density_poisson {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {η : ℝ}
    (hη : 0 < η) (y : ℝ) :
    (mSol Λ ((y : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi =
      ∫ u : ℝ, rho Λ u * Density_K η (y - u) := by
  have hz : 0 < (((y : ℂ) + (η : ℂ) * Complex.I)).im := by simpa using hη
  rw [Density_rep hΛ hℓ hz]
  have hne : ∀ u : ℝ, (u : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I) ≠ 0 := fun u h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hint : Integrable (fun u : ℝ => (rho Λ u : ℂ) / ((u : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I))) := by
    have hcont : Continuous (fun u : ℝ => (rho Λ u : ℂ) / ((u : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I))) := by
      have h1 : Continuous (fun u : ℝ => (u : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I)) :=
        Complex.continuous_ofReal.sub continuous_const
      have h2 : Continuous (fun u : ℝ => ((u : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I))⁻¹) :=
        h1.inv₀ hne
      have h3 : Continuous (fun u : ℝ => (rho Λ u : ℂ)) :=
        Complex.continuous_ofReal.comp (Density_rho_continuous hΛ hℓ)
      have h4 : Continuous (fun u : ℝ => (rho Λ u : ℂ) *
          ((u : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I))⁻¹) := h3.mul h2
      simpa only [div_eq_mul_inv] using h4
    refine Integrable.mono' ((Density_rho_integrable hΛ hℓ).div_const η) hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Density_rho_nonneg hΛ hℓ u)]
    have hn : η ≤ ‖(u : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I)‖ := by
      have := Complex.abs_im_le_norm ((u : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I))
      simpa [abs_of_pos hη] using this
    exact div_le_div_of_nonneg_left (Density_rho_nonneg hΛ hℓ u) hη hn
  have h1 : (∫ u : ℝ, (rho Λ u : ℂ) / ((u : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I))).im =
      ∫ u : ℝ, ((rho Λ u : ℂ) / ((u : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I))).im := by
    have := (Complex.imCLM).integral_comp_comm hint
    simpa using this.symm
  rw [h1, ← integral_div]
  congr 1
  funext u
  have hpos : 0 < (u - y) ^ 2 + η ^ 2 := Density_K_den_pos hη _
  have e : ((rho Λ u : ℂ) / ((u : ℂ) - ((y : ℂ) + (η : ℂ) * Complex.I))).im =
      rho Λ u * (η / ((u - y) ^ 2 + η ^ 2)) := by
    rw [Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp
  rw [e]
  unfold Density_K
  have : (u - y) ^ 2 = (y - u) ^ 2 := by ring
  rw [this]
  field_simp

end Density_S11

section Density_S12
open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Density_T_family {Λt : ℝ → Matrix ι ι ℂ} (hc : Continuous Λt) (hH : ∀ t, (Λt t).IsHermitian)
    (hℓ : ∀ t, opNorm (Λt t) ≤ 1 / 10) (x : ℝ) : Continuous fun t => Density_T (Λt t) x := by
  have hπ := Real.pi_pos
  by_cases hx : 3 ≤ x
  · have : (fun t => Density_T (Λt t) x) = fun _ => 0 := funext fun t =>
      Density_T_of_ge (hH t) (hℓ t) (by linarith [(Density_edge_bounds (hH t) (hℓ t)).1])
    rw [this]; exact continuous_const
  push Not at hx
  set G : ℝ → ℝ → ℝ := fun η t => ∫ y in x..4, (mSol (Λt t) ((y : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi
    with hG
  have hGc : ∀ η : ℝ, 0 < η → Continuous (G η) := by
    intro η hη
    have hmap : Continuous (fun p : ℝ × ℝ => (p.1, (p.2 : ℂ) + (η : ℂ) * Complex.I)) :=
      continuous_fst.prodMk ((Complex.continuous_ofReal.comp continuous_snd).add continuous_const)
    have hS : ∀ p : ℝ × ℝ, (p.1, (p.2 : ℂ) + (η : ℂ) * Complex.I) ∈ {q : ℝ × ℂ | 0 < q.2.im} := by
      intro p; simpa using hη
    have h1 := (Density_mSol_continuousOn hc hH hℓ).comp_continuous hmap hS
    have h1' : Continuous (fun p : ℝ × ℝ => mSol (Λt p.1) ((p.2 : ℂ) + (η : ℂ) * Complex.I)) := by
      convert h1 using 1
      funext p
      rfl
    have h2 : Continuous (Function.uncurry fun (t y : ℝ) =>
        (mSol (Λt t) ((y : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi) :=
      (Complex.continuous_im.comp h1').div_const _
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h2 x 4
  have hGerr : ∀ η : ℝ, 0 < η → ∀ t : ℝ, |G η t - Density_T (Λt t) x| ≤ 4 * Real.sqrt η / Real.pi := by
    intro η hη t
    have hΛ := hH t
    have hl := hℓ t
    set ρ := rho (Λt t) with hρ
    have hsm := fun z => Density_smooth (ρ := ρ) (Density_rho_integrable hΛ hl) (Density_rho_nonneg hΛ hl)
      (Density_rho_le hΛ hl) (Density_mass hΛ hl) hη z
    obtain ⟨hi1, hb1⟩ := hsm x
    obtain ⟨hi2, hb2⟩ := hsm 4
    have hA : ∀ y : ℝ, (mSol (Λt t) ((y : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi =
        ∫ u, ρ u * Density_K η (y - u) := fun y => Density_poisson hΛ hl hη y
    have hGt : G η t = ∫ y in x..4, ∫ u, ρ u * Density_K η (y - u) := by
      simp only [hG]
      exact intervalIntegral.integral_congr fun y _ => hA y
    have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hi1 (show x ≤ 4 by linarith)
    have hT4 : Density_T (Λt t) 4 = 0 :=
      Density_T_of_ge hΛ hl (by linarith [(Density_edge_bounds hΛ hl).1])
    have hT4' : ∫ u in Ioi (4 : ℝ), ρ u = 0 := hT4
    rw [hT4'] at hb2
    have hTx : Density_T (Λt t) x = ∫ u in Ioi x, ρ u := rfl
    rw [hGt, ← hsplit, hTx]
    have e1 := abs_le.1 hb1
    have e2 := abs_le.1 hb2
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, show 4 * Real.sqrt η / Real.pi =
      2 * Real.sqrt η / Real.pi + 2 * Real.sqrt η / Real.pi by ring]
  have hTU : TendstoUniformly G (fun t => Density_T (Λt t) x) (𝓝[>] (0 : ℝ)) := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hlim : Tendsto (fun η : ℝ => 4 * Real.sqrt η / Real.pi) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun η : ℝ => 4 * Real.sqrt η / Real.pi) (𝓝 0) (𝓝 (4 * Real.sqrt 0 / Real.pi)) :=
        (by fun_prop : Continuous fun η : ℝ => 4 * Real.sqrt η / Real.pi).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    filter_upwards [hlim.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with η h1 h2 t
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hGerr η h2 t) h1
  exact hTU.continuous (Filter.Eventually.frequently
    (by filter_upwards [self_mem_nhdsWithin] with η hη using hGc η hη))

end Density_S12

section Density_S13
open Set

section Transport

variable {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private lemma Density_ntr_submatrix (e : ι ≃ κ) (B : Matrix ι ι ℂ) :
    ntr (B.submatrix e.symm e.symm) = ntr B := by
  unfold ntr
  rw [Fintype.card_congr e]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun j => B j j)

open scoped Matrix.Norms.L2Operator in
private lemma Density_opNorm_submatrix [Nonempty ι] (e : ι ≃ κ) (Λ : Matrix ι ι ℂ) :
    opNorm (Λ.submatrix e.symm e.symm) ≤ opNorm Λ := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix κ ι ℂ, P = Matrix.of fun a j => if e.symm a = j then 1 else 0 :=
    ⟨_, rfl⟩
  have hPe : ∀ a j, P a j = if e.symm a = j then 1 else 0 := fun a j => by rw [hP]; rfl
  have hPP : Pᴴ * P = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hPe, Matrix.one_apply]
    have : ∀ a : κ, (star (if e.symm a = i then (1 : ℂ) else 0)) * (if e.symm a = j then 1 else 0) =
        if a = e i then (if i = j then 1 else 0) else 0 := by
      intro a
      by_cases h1 : e.symm a = i
      · subst h1
        simp
      · have : a ≠ e i := by intro h; apply h1; rw [h]; simp
        simp [h1, this]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hPΛ : P * Λ * Pᴴ = Λ.submatrix e.symm e.symm := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hPe, Matrix.submatrix_apply]
    simp
  have hn : ‖P‖ * ‖P‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hPP]
    exact norm_one
  have h1 : ‖P‖ = 1 := by
    have h0 : 0 ≤ ‖P‖ := norm_nonneg _
    nlinarith
  show ‖Λ.submatrix e.symm e.symm‖ ≤ ‖Λ‖
  rw [← hPΛ]
  calc ‖P * Λ * Pᴴ‖ ≤ ‖P * Λ‖ * ‖Pᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖P‖ * ‖Λ‖) * ‖Pᴴ‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ = ‖Λ‖ := by rw [Matrix.l2_opNorm_conjTranspose, h1]; ring


private lemma Density_ntr_inv_submatrix (e : ι ≃ κ) (Λ : Matrix ι ι ℂ) (c : ℂ) :
    ntr ((Λ.submatrix e.symm e.symm - c • (1 : Matrix κ κ ℂ))⁻¹) = ntr ((Λ - c • (1 : Matrix ι ι ℂ))⁻¹) := by
  have : Λ.submatrix e.symm e.symm - c • (1 : Matrix κ κ ℂ) =
      (Λ - c • (1 : Matrix ι ι ℂ)).submatrix e.symm e.symm := by
    ext a b
    simp [Matrix.one_apply]
  rw [this, Matrix.inv_submatrix_equiv, Density_ntr_submatrix]

private lemma Density_mSol_submatrix [Nonempty ι] (e : ι ≃ κ) {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) : mSol (Λ.submatrix e.symm e.symm) z = mSol Λ z := by
  haveI : Nonempty κ := ⟨e (Classical.arbitrary ι)⟩
  have hΛ' : (Λ.submatrix e.symm e.symm).IsHermitian := hΛ.submatrix _
  obtain ⟨w, hw, huniq⟩ := mSol_existsUnique (Λ.submatrix e.symm e.symm) hΛ' z hz
  have hs := mSol_spec Λ hΛ z hz
  have hs' := mSol_spec (Λ.submatrix e.symm e.symm) hΛ' z hz
  have h1 : 0 < (mSol Λ z).im ∧ mSol Λ z =
      ntr ((Λ.submatrix e.symm e.symm - (z + mSol Λ z) • (1 : Matrix κ κ ℂ))⁻¹) := by
    refine ⟨hs.1, ?_⟩
    rw [Density_ntr_inv_submatrix]
    have := hs.2.1
    rw [MSol] at this
    exact this
  have h2 : 0 < (mSol (Λ.submatrix e.symm e.symm) z).im ∧ mSol (Λ.submatrix e.symm e.symm) z =
      ntr ((Λ.submatrix e.symm e.symm - (z + mSol (Λ.submatrix e.symm e.symm) z) •
        (1 : Matrix κ κ ℂ))⁻¹) := by
    refine ⟨hs'.1, ?_⟩
    have := hs'.2.1
    rw [MSol] at this
    exact this
  rw [huniq _ h1, huniq _ h2]

private lemma Density_rho_submatrix [Nonempty ι] (e : ι ≃ κ) {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    rho (Λ.submatrix e.symm e.symm) = rho Λ := by
  funext x
  unfold rho
  congr 1
  unfold limUnder
  congr 1
  refine Filter.map_congr ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
  simp only [Density_mSol_submatrix e hΛ this]

end Transport

private lemma Density_sqrt_bounds : ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ), Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
    ∀ x ∈ Set.Icc (Eminus Λ) (Eplus Λ),
      C⁻¹ * Real.sqrt ((Eplus Λ - x) * (x - Eminus Λ)) ≤ rho Λ x ∧
        rho Λ x ≤ C * Real.sqrt ((Eplus Λ - x) * (x - Eminus Λ)) := by
  obtain ⟨C, hC, h⟩ := square_root_density 1 one_pos
  refine ⟨C, hC, fun {ι} _ _ _ Λ hΛ hℓ x hx => ?_⟩
  set e := Fintype.equivFin ι with he
  haveI : Nonempty (Fin (Fintype.card ι)) := ⟨e (Classical.arbitrary ι)⟩
  have hΛ' : (Λ.submatrix e.symm e.symm).IsHermitian := hΛ.submatrix _
  have hℓ' : opNorm (Λ.submatrix e.symm e.symm) ≤ 1 / 10 :=
    (Density_opNorm_submatrix e Λ).trans hℓ
  have hrho := Density_rho_submatrix e hΛ
  have hEp : Eplus (Λ.submatrix e.symm e.symm) = Eplus Λ := by unfold Eplus; rw [hrho]
  have hEm : Eminus (Λ.submatrix e.symm e.symm) = Eminus Λ := by unfold Eminus; rw [hrho]
  have := (h (Fin (Fintype.card ι)) (Λ.submatrix e.symm e.symm) hΛ' hℓ').1 x
    (by rw [hEp, hEm]; exact hx)
  rw [hEp, hEm, hrho] at this
  exact this

end Density_S13

section Density_S14
open Set

section Edges

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Density_T_nonneg {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (x : ℝ) :
    0 ≤ Density_T Λ x :=
  setIntegral_nonneg measurableSet_Ioi fun u _ => Density_rho_nonneg hΛ hℓ u

private lemma Density_T_le_one {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (x : ℝ) :
    Density_T Λ x ≤ 1 := by
  have := setIntegral_le_integral (μ := volume) (s := Ioi x) (Density_rho_integrable hΛ hℓ)
    (Filter.Eventually.of_forall fun u => Density_rho_nonneg hΛ hℓ u)
  rwa [Density_mass hΛ hℓ] at this

private lemma Density_T_pos_of_lt {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {a : ℝ}
    (ha : a < Eplus Λ) : 0 < Density_T Λ a := by
  rcases lt_or_ge a (Eminus Λ) with h | h
  · rw [Density_T_of_le hΛ hℓ h.le]; exact one_pos
  · have := Density_T_strictAnti hΛ hℓ h ha (le_refl _)
    rwa [Density_T_of_ge hΛ hℓ (le_refl _)] at this

private lemma Density_T_lt_one_of_gt {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {a : ℝ}
    (ha : Eminus Λ < a) : Density_T Λ a < 1 := by
  rcases lt_or_ge a (Eplus Λ) with h | h
  · have := Density_T_strictAnti hΛ hℓ (le_refl (Eminus Λ)) ha h.le
    rwa [Density_T_of_le hΛ hℓ (le_refl _)] at this
  · rw [Density_T_of_ge hΛ hℓ h]; exact one_pos

variable {Λt : ℝ → Matrix ι ι ℂ}

private lemma Density_Eplus_lower (hc : Continuous Λt) (hH : ∀ t, (Λt t).IsHermitian)
    (hℓ : ∀ t, opNorm (Λt t) ≤ 1 / 10) (t₀ : ℝ) {a : ℝ} (ha : a < Eplus (Λt t₀)) :
    ∀ᶠ t in 𝓝 t₀, a < Eplus (Λt t) := by
  have h0 := Density_T_pos_of_lt (hH t₀) (hℓ t₀) ha
  have hev : ∀ᶠ t in 𝓝 t₀, 0 < Density_T (Λt t) a :=
    (Density_T_family hc hH hℓ a).continuousAt.eventually (lt_mem_nhds h0)
  filter_upwards [hev] with t ht
  by_contra hcon
  push Not at hcon
  rw [Density_T_of_ge (hH t) (hℓ t) hcon] at ht
  exact lt_irrefl _ ht

private lemma Density_Eminus_upper (hc : Continuous Λt) (hH : ∀ t, (Λt t).IsHermitian)
    (hℓ : ∀ t, opNorm (Λt t) ≤ 1 / 10) (t₀ : ℝ) {a : ℝ} (ha : Eminus (Λt t₀) < a) :
    ∀ᶠ t in 𝓝 t₀, Eminus (Λt t) < a := by
  have h0 := Density_T_lt_one_of_gt (hH t₀) (hℓ t₀) ha
  have hev : ∀ᶠ t in 𝓝 t₀, Density_T (Λt t) a < 1 :=
    (Density_T_family hc hH hℓ a).continuousAt.eventually (gt_mem_nhds h0)
  filter_upwards [hev] with t ht
  by_contra hcon
  push Not at hcon
  rw [Density_T_of_le (hH t) (hℓ t) hcon] at ht
  exact lt_irrefl _ ht


private lemma Density_Eplus_upper (hc : Continuous Λt) (hH : ∀ t, (Λt t).IsHermitian)
    (hℓ : ∀ t, opNorm (Λt t) ≤ 1 / 10) (t₀ : ℝ) {a : ℝ} (ha : Eplus (Λt t₀) < a) :
    ∀ᶠ t in 𝓝 t₀, Eplus (Λt t) < a := by
  obtain ⟨C, hC, hsq⟩ := Density_sqrt_bounds.{u}
  by_contra hcon
  rw [not_eventually] at hcon
  have hlt := (rho_support _ (hH t₀) (hℓ t₀)).1
  set E₀ := Eplus (Λt t₀) with hE₀
  set Lw := Eminus (Λt t₀) with hLw
  set ε := a - E₀ with hε
  have hε0 : 0 < ε := by linarith
  set x₂ := E₀ + ε / 2 with hx₂
  set d := (E₀ - Lw) / 2 with hd
  have hd0 : 0 < d := by linarith
  set r := C⁻¹ * Real.sqrt ((ε / 4) * d) with hr
  have hr0 : 0 < r := by positivity
  set c := (ε / 4) * r with hc0
  have hc1 : 0 < c := by positivity
  have hT0 : Density_T (Λt t₀) x₂ = 0 := Density_T_of_ge (hH t₀) (hℓ t₀) (by linarith)
  have hev1 : ∀ᶠ t in 𝓝 t₀, Density_T (Λt t) x₂ < c :=
    (Density_T_family hc hH hℓ x₂).continuousAt.eventually
      (gt_mem_nhds (by show Density_T (Λt t₀) x₂ < c; rw [hT0]; exact hc1))
  have hev2 : ∀ᶠ t in 𝓝 t₀, Eminus (Λt t) < Lw + d := Density_Eminus_upper hc hH hℓ t₀ (by linarith)
  obtain ⟨t, ht3, ht1, ht2⟩ := (hcon.and_eventually (hev1.and hev2)).exists
  have hat : a ≤ Eplus (Λt t) := not_lt.1 ht3
  have hΛ := hH t
  have hl := hℓ t
  have hlow : ∀ y ∈ Set.Icc x₂ (x₂ + ε / 4), r ≤ rho (Λt t) y := by
    intro y hy
    have hmem : y ∈ Set.Icc (Eminus (Λt t)) (Eplus (Λt t)) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have h1 := (hsq (Λt t) hΛ hl y hmem).1
    refine le_trans ?_ h1
    rw [hr]
    have e1 : ε / 4 ≤ Eplus (Λt t) - y := by linarith [hy.2]
    have e2 : d ≤ y - Eminus (Λt t) := by linarith [hy.1]
    have hprod : ε / 4 * d ≤ (Eplus (Λt t) - y) * (y - Eminus (Λt t)) :=
      mul_le_mul e1 e2 hd0.le (by linarith)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprod) (inv_nonneg.2 hC.le)
  have hint : (ε / 4) * r ≤ ∫ u in x₂..(x₂ + ε / 4), rho (Λt t) u := by
    have := intervalIntegral.integral_mono_on (a := x₂) (b := x₂ + ε / 4) (by linarith)
      (intervalIntegrable_const (μ := volume) (c := r)) ((Density_rho_continuous hΛ hl).intervalIntegrable _ _) hlow
    rwa [intervalIntegral.integral_const, smul_eq_mul, show x₂ + ε / 4 - x₂ = ε / 4 by ring] at this
  have hsub := Density_T_sub hΛ hl (show x₂ ≤ x₂ + ε / 4 by linarith)
  have hnn := Density_T_nonneg hΛ hl (x₂ + ε / 4)
  linarith

private lemma Density_Eminus_lower (hc : Continuous Λt) (hH : ∀ t, (Λt t).IsHermitian)
    (hℓ : ∀ t, opNorm (Λt t) ≤ 1 / 10) (t₀ : ℝ) {a : ℝ} (ha : a < Eminus (Λt t₀)) :
    ∀ᶠ t in 𝓝 t₀, a < Eminus (Λt t) := by
  obtain ⟨C, hC, hsq⟩ := Density_sqrt_bounds.{u}
  by_contra hcon
  rw [not_eventually] at hcon
  have hlt := (rho_support _ (hH t₀) (hℓ t₀)).1
  set E₀ := Eplus (Λt t₀) with hE₀
  set Lw := Eminus (Λt t₀) with hLw
  set ε := Lw - a with hε
  have hε0 : 0 < ε := by linarith
  set x₂ := Lw - ε / 2 with hx₂
  set d := (E₀ - Lw) / 2 with hd
  have hd0 : 0 < d := by linarith
  set r := C⁻¹ * Real.sqrt ((ε / 4) * d) with hr
  have hr0 : 0 < r := by positivity
  set c := (ε / 4) * r with hc0
  have hc1 : 0 < c := by positivity
  have hT0 : Density_T (Λt t₀) x₂ = 1 := Density_T_of_le (hH t₀) (hℓ t₀) (by linarith)
  have hev1 : ∀ᶠ t in 𝓝 t₀, 1 - c < Density_T (Λt t) x₂ :=
    (Density_T_family hc hH hℓ x₂).continuousAt.eventually
      (lt_mem_nhds (by show 1 - c < Density_T (Λt t₀) x₂; rw [hT0]; linarith))
  have hev2 : ∀ᶠ t in 𝓝 t₀, E₀ - d < Eplus (Λt t) := Density_Eplus_lower hc hH hℓ t₀ (by linarith)
  obtain ⟨t, ht3, ht1, ht2⟩ := (hcon.and_eventually (hev1.and hev2)).exists
  have hat : Eminus (Λt t) ≤ a := not_lt.1 ht3
  have hΛ := hH t
  have hl := hℓ t
  have hlow : ∀ y ∈ Set.Icc (x₂ - ε / 4) x₂, r ≤ rho (Λt t) y := by
    intro y hy
    have hmem : y ∈ Set.Icc (Eminus (Λt t)) (Eplus (Λt t)) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have h1 := (hsq (Λt t) hΛ hl y hmem).1
    refine le_trans ?_ h1
    rw [hr]
    have e1 : d ≤ Eplus (Λt t) - y := by linarith [hy.2]
    have e2 : ε / 4 ≤ y - Eminus (Λt t) := by linarith [hy.1]
    have hprod : ε / 4 * d ≤ (Eplus (Λt t) - y) * (y - Eminus (Λt t)) := by
      rw [mul_comm (ε / 4) d]
      exact mul_le_mul e1 e2 (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprod) (inv_nonneg.2 hC.le)
  have hint : (ε / 4) * r ≤ ∫ u in (x₂ - ε / 4)..x₂, rho (Λt t) u := by
    have := intervalIntegral.integral_mono_on (a := x₂ - ε / 4) (b := x₂) (by linarith)
      (intervalIntegrable_const (μ := volume) (c := r)) ((Density_rho_continuous hΛ hl).intervalIntegrable _ _) hlow
    rwa [intervalIntegral.integral_const, smul_eq_mul, show x₂ - (x₂ - ε / 4) = ε / 4 by ring] at this
  have hsub := Density_T_sub hΛ hl (show x₂ - ε / 4 ≤ x₂ by linarith)
  have hle := Density_T_le_one hΛ hl (x₂ - ε / 4)
  linarith

end Edges

end Density_S14

section Density_S15
open Set

section Moving

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Λt : ℝ → Matrix ι ι ℂ}

private lemma Density_quant_gt {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) {p γ : ℝ}
    (hp1 : p < 1) (hγ2 : γ < Eplus Λ) (hTγ : Density_T Λ γ = p) {x : ℝ} (hx : x < γ) :
    p < Density_T Λ x := by
  rcases lt_or_ge x (Eminus Λ) with h | h
  · rw [Density_T_of_le hΛ hℓ h.le]; exact hp1
  · have := Density_T_strictAnti hΛ hℓ h hx hγ2.le
    rwa [hTγ] at this

private lemma Density_quant_continuous (hc : Continuous Λt) (hH : ∀ t, (Λt t).IsHermitian)
    (hℓ : ∀ t, opNorm (Λt t) ≤ 1 / 10) (Mc k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ Mc) :
    Continuous fun t => quant (rho (Λt t)) Mc k := by
  have hMc : (0 : ℝ) < Mc := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have : (k : ℝ) ≤ Mc := by exact_mod_cast hk2
    linarith
  set p : ℝ := ((k : ℝ) - 1 / 2) / Mc with hp
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk2' : (k : ℝ) ≤ Mc := by exact_mod_cast hk2
  have hp0 : 0 < p := by rw [hp]; apply div_pos <;> linarith
  have hp1 : p < 1 := by rw [hp, div_lt_one hMc]; linarith
  have hspec : ∀ t, ∃ γ : ℝ, Eminus (Λt t) < γ ∧ γ < Eplus (Λt t) ∧ Density_T (Λt t) γ = p ∧
      ∀ x, p ≤ Density_T (Λt t) x ↔ x ≤ γ := fun t => Density_quant_spec (hH t) (hℓ t) hp0 hp1
  choose γ hγ using hspec
  have hq : (fun t => quant (rho (Λt t)) Mc k) = γ := by
    funext t
    exact Density_quant_eq (hγ t).2.2.2 Mc k rfl
  rw [hq]
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have h0 : p < Density_T (Λt t₀) a :=
      Density_quant_gt (hH t₀) (hℓ t₀) hp1 (hγ t₀).2.1 (hγ t₀).2.2.1 ha
    have hev : ∀ᶠ t in 𝓝 t₀, p < Density_T (Λt t) a :=
      (Density_T_family hc hH hℓ a).continuousAt.eventually (lt_mem_nhds h0)
    filter_upwards [hev] with t ht
    have h1 : a ≤ γ t := ((hγ t).2.2.2 a).1 ht.le
    refine lt_of_le_of_ne h1 fun h => ?_
    rw [h, (hγ t).2.2.1] at ht
    exact lt_irrefl _ ht
  · have h0 : Density_T (Λt t₀) a < p := by
      by_contra hcon
      push Not at hcon
      have := ((hγ t₀).2.2.2 a).1 hcon
      linarith
    have hev : ∀ᶠ t in 𝓝 t₀, Density_T (Λt t) a < p :=
      (Density_T_family hc hH hℓ a).continuousAt.eventually (gt_mem_nhds h0)
    filter_upwards [hev] with t ht
    by_contra hcon
    push Not at hcon
    have := ((hγ t).2.2.2 a).2 hcon
    linarith

private lemma Density_moving {Λt : ℝ → Matrix ι ι ℂ} (hc : Continuous Λt) (hH : ∀ t, (Λt t).IsHermitian)
    (hℓ : ∀ t, opNorm (Λt t) ≤ 1 / 10) :
    Continuous (fun t => Eplus (Λt t)) ∧ Continuous (fun t => Eminus (Λt t)) ∧
      (∀ Mc k : ℕ, 1 ≤ k → k ≤ Mc → Continuous fun t => quant (rho (Λt t)) Mc k) ∧
      ContinuousOn (fun p : ℝ × ℂ => mSol (Λt p.1) p.2) {p : ℝ × ℂ | 0 < p.2.im} := by
  refine ⟨?_, ?_, fun Mc k hk1 hk2 => Density_quant_continuous hc hH hℓ Mc k hk1 hk2,
    Density_mSol_continuousOn hc hH hℓ⟩
  · refine continuous_iff_continuousAt.2 fun t₀ => tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact Density_Eplus_lower hc hH hℓ t₀ ha
    · exact Density_Eplus_upper hc hH hℓ t₀ ha
  · refine continuous_iff_continuousAt.2 fun t₀ => tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact Density_Eminus_lower hc hH hℓ t₀ ha
    · exact Density_Eminus_upper hc hH hℓ t₀ ha

end Moving

end Density_S15

section Density_S16
open Set
open scoped Matrix.Norms.L2Operator

private lemma Density_lam_isHermitian (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (lam D N A).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  simp only [lam, star_add]
  split_ifs <;> simp [add_comm]

/-- The embedding of the `N`-dimensional space as the `a`-th block. -/
private def Density_J (D N : ℕ) (a : Fin D) : Matrix (Idx D N) (Fin N) ℂ :=
  Matrix.of fun p i => if p = (a, i) then 1 else 0

private lemma Density_J_conj_mul (D N : ℕ) (a : Fin D) : (Density_J D N a)ᴴ * Density_J D N a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Density_J, Matrix.of_apply, Matrix.one_apply]
  have : ∀ p : Idx D N, star (if p = (a, i) then (1 : ℂ) else 0) * (if p = (a, j) then 1 else 0) =
      if p = (a, i) then (if i = j then 1 else 0) else 0 := by
    intro p
    by_cases h : p = (a, i)
    · subst h
      by_cases hij : i = j <;> simp [hij]
    · simp [h]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma Density_J_norm (D N : ℕ) (hN : 1 ≤ N) (a : Fin D) : ‖Density_J D N a‖ ≤ 1 := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (Density_J D N a)
  rw [Density_J_conj_mul, norm_one] at h1
  have h0 : 0 ≤ ‖Density_J D N a‖ := norm_nonneg _
  nlinarith

private lemma Density_block_norm (D N : ℕ) (hN : 1 ≤ N) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖Density_J D N a * M * (Density_J D N b)ᴴ‖ ≤ ‖M‖ := by
  have ha := Density_J_norm D N hN a
  have hb := Density_J_norm D N hN b
  calc ‖Density_J D N a * M * (Density_J D N b)ᴴ‖ ≤ ‖Density_J D N a * M‖ * ‖(Density_J D N b)ᴴ‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Density_J D N a‖ * ‖M‖) * ‖(Density_J D N b)ᴴ‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
    _ = ‖M‖ := by ring

private lemma Density_block_apply (D N : ℕ) (a b : Fin D) (M : Matrix (Fin N) (Fin N) ℂ) (p q : Idx D N) :
    (Density_J D N a * M * (Density_J D N b)ᴴ) p q = if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h1 : p1 = a <;> by_cases h2 : q1 = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Density_J, Prod.ext_iff, h1, h2]

private lemma Density_lam_eq (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    lam D N A = ∑ a : Fin D, ∑ b : Fin D,
      ((if fwd D a b then Density_J D N a * A * (Density_J D N b)ᴴ else 0) +
        (if fwd D b a then Density_J D N a * Aᴴ * (Density_J D N b)ᴴ else 0)) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.add_apply]
  have e1 : ∀ a b : Fin D, (if fwd D a b then Density_J D N a * A * (Density_J D N b)ᴴ else 0) p q =
      if fwd D a b ∧ p.1 = a ∧ q.1 = b then A p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D a b <;> simp [h, Density_block_apply]
  have e2 : ∀ a b : Fin D, (if fwd D b a then Density_J D N a * Aᴴ * (Density_J D N b)ᴴ else 0) p q =
      if fwd D b a ∧ p.1 = a ∧ q.1 = b then Aᴴ p.2 q.2 else 0 := by
    intro a b
    by_cases h : fwd D b a <;> simp [h, Density_block_apply]
  simp only [e1, e2, Finset.sum_add_distrib]
  unfold lam
  congr 1
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha, ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb, hb]) (by simp)]
    by_cases h : fwd D p.1 q.1 <;> simp [h]
  · rw [Finset.sum_eq_single p.1 (fun a _ ha => by simp [Ne.symm ha, ha]) (by simp),
      Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb, hb]) (by simp)]
    by_cases h : fwd D q.1 p.1 <;> simp [h, Matrix.conjTranspose_apply]


private lemma Density_opNorm_lam (D N : ℕ) (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ) :
    opNorm (lam D N A) ≤ 2 * (D : ℝ) ^ 2 * opNorm A := by
  show ‖lam D N A‖ ≤ 2 * (D : ℝ) ^ 2 * ‖A‖
  rw [Density_lam_eq]
  have hb : ∀ a b : Fin D, ‖(if fwd D a b then Density_J D N a * A * (Density_J D N b)ᴴ else 0) +
      (if fwd D b a then Density_J D N a * Aᴴ * (Density_J D N b)ᴴ else 0)‖ ≤ 2 * ‖A‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if fwd D a b then Density_J D N a * A * (Density_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact Density_block_norm D N hN a b A
      · simp
    have h2 : ‖(if fwd D b a then Density_J D N a * Aᴴ * (Density_J D N b)ᴴ else 0)‖ ≤ ‖A‖ := by
      split_ifs
      · exact (Density_block_norm D N hN a b Aᴴ).trans (by rw [Matrix.l2_opNorm_conjTranspose])
      · simp
    linarith
  calc ‖∑ a : Fin D, ∑ b : Fin D, _‖ ≤ ∑ a : Fin D, ‖∑ b : Fin D, _‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin D, ∑ b : Fin D, 2 * ‖A‖ := by
        refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb a b)
    _ = 2 * (D : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Density_S16

section Density_S17
open Set

private lemma Density_integral_sqrt_aux {d : ℝ} (hd : 0 ≤ d) :
    ∫ s in (0 : ℝ)..d, Real.sqrt s = (2 / 3) * d ^ (3 / 2 : ℝ) := by
  have h := integral_rpow (a := 0) (b := d) (r := 1 / 2) (Or.inl (by norm_num))
  simp only [Real.zero_rpow (show (1 / 2 + 1 : ℝ) ≠ 0 by norm_num), sub_zero] at h
  have e : ∀ s : ℝ, Real.sqrt s = s ^ (1 / 2 : ℝ) := fun s => Real.sqrt_eq_rpow s
  simp only [e]
  rw [h]
  norm_num
  ring

private lemma Density_integral_sqrt {h : ℝ → ℝ} (hc : Continuous h) {α β : ℝ}
    (hlow : ∀ s ∈ Icc (0 : ℝ) 1, α * Real.sqrt s ≤ h s)
    (hup : ∀ s ∈ Icc (0 : ℝ) 1, h s ≤ β * Real.sqrt s) {d : ℝ} (hd : d ∈ Icc (0 : ℝ) 1) :
    (2 / 3) * α * d ^ (3 / 2 : ℝ) ≤ ∫ s in (0 : ℝ)..d, h s ∧
      ∫ s in (0 : ℝ)..d, h s ≤ (2 / 3) * β * d ^ (3 / 2 : ℝ) := by
  have hsq : Continuous Real.sqrt := Real.continuous_sqrt
  have hint : ∀ c : ℝ, IntervalIntegrable (fun s => c * Real.sqrt s) volume 0 d := fun c =>
    (continuous_const.mul hsq).intervalIntegrable _ _
  constructor
  · have := intervalIntegral.integral_mono_on hd.1 (hint α) (hc.intervalIntegrable _ _)
      (fun s hs => hlow s ⟨hs.1, hs.2.trans hd.2⟩)
    rw [intervalIntegral.integral_const_mul, Density_integral_sqrt_aux hd.1] at this
    linarith
  · have := intervalIntegral.integral_mono_on hd.1 (hc.intervalIntegrable _ _) (hint β)
      (fun s hs => hup s ⟨hs.1, hs.2.trans hd.2⟩)
    rw [intervalIntegral.integral_const_mul, Density_integral_sqrt_aux hd.1] at this
    linarith


private lemma Density_rpow_cancel {y : ℝ} (hy : 0 ≤ y) : (y ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = y := by
  rw [← Real.rpow_mul hy]
  norm_num

private lemma Density_two_case {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {D : ℕ} (hD : 1 ≤ D) {K p d : ℝ}
    (hK0 : 0 < K) (hKD : K ≤ D) (hp1 : K / (2 * D) ≤ p) (hp2 : p ≤ K / D) (hd0 : 0 < d)
    (hdL : d ≤ 21 / 5) (h1 : d ≤ 1 → a * d ^ (3 / 2 : ℝ) ≤ p ∧ p ≤ b * d ^ (3 / 2 : ℝ))
    (h2 : 1 < d → a ≤ p) :
    min ((2 * D * b) ^ (-(2 / 3 : ℝ))) ((D : ℝ) ^ (-(2 / 3 : ℝ))) * K ^ (2 / 3 : ℝ) ≤ d ∧
      d ≤ 21 / 5 * (a * D) ^ (-(2 / 3 : ℝ)) * K ^ (2 / 3 : ℝ) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hKu : 0 < K ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hK0 _
  have hm1 : (0 : ℝ) < 2 * D * b := by positivity
  have hm2 : (0 : ℝ) < a * D := by positivity
  -- rewriting `x⁻ᵘ * K^u` as `(K / x)^u`
  have hdiv : ∀ m : ℝ, 0 < m → (K / m) ^ (2 / 3 : ℝ) = m ^ (-(2 / 3 : ℝ)) * K ^ (2 / 3 : ℝ) := by
    intro m hm
    rw [Real.div_rpow hK0.le hm.le, Real.rpow_neg hm.le]
    ring
  have hmin1 : min ((2 * D * b) ^ (-(2 / 3 : ℝ))) ((D : ℝ) ^ (-(2 / 3 : ℝ))) ≤
      (2 * D * b) ^ (-(2 / 3 : ℝ)) := min_le_left _ _
  have hmin2 : min ((2 * D * b) ^ (-(2 / 3 : ℝ))) ((D : ℝ) ^ (-(2 / 3 : ℝ))) ≤
      (D : ℝ) ^ (-(2 / 3 : ℝ)) := min_le_right _ _
  have hc1 : 0 < (a * D) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hm2 _
  by_cases hd1 : d ≤ 1
  · obtain ⟨hlo, hup⟩ := h1 hd1
    have hd32 : 0 ≤ d ^ (3 / 2 : ℝ) := Real.rpow_nonneg hd0.le _
    constructor
    · -- lower bound
      have e1 : K / (2 * D * b) ≤ d ^ (3 / 2 : ℝ) := by
        rw [div_le_iff₀ hm1]
        have : K / (2 * D) ≤ b * d ^ (3 / 2 : ℝ) := hp1.trans hup
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * D)] at this
        nlinarith
      have e2 : (K / (2 * D * b)) ^ (2 / 3 : ℝ) ≤ d := by
        calc (K / (2 * D * b)) ^ (2 / 3 : ℝ) ≤ (d ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) :=
              Real.rpow_le_rpow (by positivity) e1 (by norm_num)
          _ = d := Density_rpow_cancel hd0.le
      rw [hdiv _ hm1] at e2
      calc min ((2 * D * b) ^ (-(2 / 3 : ℝ))) ((D : ℝ) ^ (-(2 / 3 : ℝ))) * K ^ (2 / 3 : ℝ)
          ≤ (2 * D * b) ^ (-(2 / 3 : ℝ)) * K ^ (2 / 3 : ℝ) := by gcongr
        _ ≤ d := e2
    · -- upper bound
      have e1 : d ^ (3 / 2 : ℝ) ≤ K / (a * D) := by
        rw [le_div_iff₀ hm2]
        have : a * d ^ (3 / 2 : ℝ) ≤ K / D := hlo.trans hp2
        rw [le_div_iff₀ hD0] at this
        nlinarith
      have e2 : d ≤ (K / (a * D)) ^ (2 / 3 : ℝ) := by
        calc d = (d ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := (Density_rpow_cancel hd0.le).symm
          _ ≤ (K / (a * D)) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow hd32 e1 (by norm_num)
      rw [hdiv _ hm2] at e2
      calc d ≤ (a * D) ^ (-(2 / 3 : ℝ)) * K ^ (2 / 3 : ℝ) := e2
        _ ≤ 21 / 5 * (a * D) ^ (-(2 / 3 : ℝ)) * K ^ (2 / 3 : ℝ) := by
          have : 0 ≤ (a * D) ^ (-(2 / 3 : ℝ)) * K ^ (2 / 3 : ℝ) := by positivity
          nlinarith
  · push Not at hd1
    have hpa := h2 hd1
    constructor
    · -- lower bound
      have hKD' : K / D ≤ 1 := by rw [div_le_one hD0]; exact hKD
      have e1 : (K / D) ^ (2 / 3 : ℝ) ≤ 1 := Real.rpow_le_one (by positivity) hKD' (by norm_num)
      rw [hdiv _ hD0] at e1
      calc min ((2 * D * b) ^ (-(2 / 3 : ℝ))) ((D : ℝ) ^ (-(2 / 3 : ℝ))) * K ^ (2 / 3 : ℝ)
          ≤ (D : ℝ) ^ (-(2 / 3 : ℝ)) * K ^ (2 / 3 : ℝ) := by gcongr
        _ ≤ 1 := e1
        _ ≤ d := hd1.le
    · -- upper bound
      have e1 : a * D ≤ K := by
        have : a ≤ K / D := hpa.trans hp2
        rw [le_div_iff₀ hD0] at this
        exact this
      have e2 : 1 ≤ (K / (a * D)) ^ (2 / 3 : ℝ) :=
        Real.one_le_rpow (by rw [le_div_iff₀ hm2]; linarith) (by norm_num)
      rw [hdiv _ hm2] at e2
      calc d ≤ 21 / 5 := hdL
        _ = 21 / 5 * 1 := by ring
        _ ≤ 21 / 5 * ((a * D) ^ (-(2 / 3 : ℝ)) * K ^ (2 / 3 : ℝ)) := by gcongr
        _ = 21 / 5 * (a * D) ^ (-(2 / 3 : ℝ)) * K ^ (2 / 3 : ℝ) := by ring

end Density_S17

section Density_S18
open Set

section EdgeAsym

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private lemma Density_width {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    Real.pi ≤ Eplus Λ - Eminus Λ ∧ Eplus Λ - Eminus Λ ≤ 21 / 5 := by
  obtain ⟨hlt, -⟩ := rho_support Λ hΛ hℓ
  obtain ⟨h1, h2⟩ := Density_edge_bounds hΛ hℓ
  refine ⟨?_, by linarith⟩
  have hsub := Density_T_sub hΛ hℓ hlt.le
  rw [Density_T_of_le hΛ hℓ (le_refl _), Density_T_of_ge hΛ hℓ (le_refl _)] at hsub
  have hint : ∫ u in Eminus Λ..Eplus Λ, rho Λ u ≤ ∫ u in Eminus Λ..Eplus Λ, 1 / Real.pi :=
    intervalIntegral.integral_mono_on hlt.le ((Density_rho_continuous hΛ hℓ).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume)) fun u _ => Density_rho_le hΛ hℓ u
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have : 1 ≤ (Eplus Λ - Eminus Λ) * (1 / Real.pi) := by linarith
  have hπ := Real.pi_pos
  rw [mul_one_div, le_div_iff₀ hπ] at this
  linarith


end EdgeAsym

private lemma Density_edge_asym : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (Λ : Matrix ι ι ℂ), Λ.IsHermitian → opNorm Λ ≤ 1 / 10 →
    ∀ d ∈ Set.Icc (0 : ℝ) 1,
      ((2 / 3) * α * d ^ (3 / 2 : ℝ) ≤ Density_T Λ (Eplus Λ - d) ∧
        Density_T Λ (Eplus Λ - d) ≤ (2 / 3) * β * d ^ (3 / 2 : ℝ)) ∧
      ((2 / 3) * α * d ^ (3 / 2 : ℝ) ≤ 1 - Density_T Λ (Eminus Λ + d) ∧
        1 - Density_T Λ (Eminus Λ + d) ≤ (2 / 3) * β * d ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hsq⟩ := Density_sqrt_bounds.{u}
  have hπ : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  refine ⟨C⁻¹ * Real.sqrt (Real.pi - 1), C * Real.sqrt (21 / 5), by positivity, by positivity, ?_⟩
  intro ι _ _ _ Λ hΛ hℓ d hd
  obtain ⟨hlt, -⟩ := rho_support Λ hΛ hℓ
  obtain ⟨hw1, hw2⟩ := Density_width hΛ hℓ
  have hcont : Continuous (rho Λ) := Density_rho_continuous hΛ hℓ
  have hsqrt1 : ∀ s : ℝ, 0 ≤ s → Real.sqrt (s * (Real.pi - 1)) = Real.sqrt s * Real.sqrt (Real.pi - 1) :=
    fun s hs => Real.sqrt_mul hs _
  have hsqrt2 : ∀ s : ℝ, 0 ≤ s → Real.sqrt (s * (21 / 5)) = Real.sqrt s * Real.sqrt (21 / 5) :=
    fun s hs => Real.sqrt_mul hs _
  constructor
  · -- right edge
    have hsub := Density_T_sub hΛ hℓ (show Eplus Λ - d ≤ Eplus Λ by linarith [hd.1])
    rw [Density_T_of_ge hΛ hℓ (le_refl _), sub_zero] at hsub
    have hcomp : ∫ s in (0 : ℝ)..d, rho Λ (Eplus Λ - s) = ∫ u in Eplus Λ - d..Eplus Λ, rho Λ u := by
      rw [intervalIntegral.integral_comp_sub_left (fun u => rho Λ u) (Eplus Λ)]
      simp
    have hI := Density_integral_sqrt (h := fun s => rho Λ (Eplus Λ - s))
      (hcont.comp (continuous_const.sub continuous_id))
      (α := C⁻¹ * Real.sqrt (Real.pi - 1)) (β := C * Real.sqrt (21 / 5))
      (fun s hs => by
        have hx : Eplus Λ - s ∈ Set.Icc (Eminus Λ) (Eplus Λ) :=
          ⟨by linarith [hs.2], by linarith [hs.1]⟩
        have := (hsq Λ hΛ hℓ _ hx).1
        refine le_trans ?_ this
        have e : (Eplus Λ - (Eplus Λ - s)) * (Eplus Λ - s - Eminus Λ) ≥ s * (Real.pi - 1) := by
          have : Real.pi - 1 ≤ Eplus Λ - s - Eminus Λ := by linarith [hs.2]
          simp only [sub_sub_cancel]
          exact mul_le_mul_of_nonneg_left this hs.1
        calc C⁻¹ * Real.sqrt (Real.pi - 1) * Real.sqrt s
            = C⁻¹ * Real.sqrt (s * (Real.pi - 1)) := by rw [hsqrt1 s hs.1]; ring
          _ ≤ C⁻¹ * Real.sqrt ((Eplus Λ - (Eplus Λ - s)) * (Eplus Λ - s - Eminus Λ)) := by
              gcongr)
      (fun s hs => by
        have hx : Eplus Λ - s ∈ Set.Icc (Eminus Λ) (Eplus Λ) :=
          ⟨by linarith [hs.2], by linarith [hs.1]⟩
        have := (hsq Λ hΛ hℓ _ hx).2
        refine le_trans this ?_
        have e : (Eplus Λ - (Eplus Λ - s)) * (Eplus Λ - s - Eminus Λ) ≤ s * (21 / 5) := by
          have h1 : Eplus Λ - s - Eminus Λ ≤ 21 / 5 := by linarith [hs.1]
          simp only [sub_sub_cancel]
          exact mul_le_mul_of_nonneg_left h1 hs.1
        calc C * Real.sqrt ((Eplus Λ - (Eplus Λ - s)) * (Eplus Λ - s - Eminus Λ))
            ≤ C * Real.sqrt (s * (21 / 5)) := by gcongr
          _ = C * Real.sqrt (21 / 5) * Real.sqrt s := by rw [hsqrt2 s hs.1]; ring)
      hd
    rw [hcomp, ← hsub] at hI
    exact hI
  · -- left edge
    have hsub := Density_T_sub hΛ hℓ (show Eminus Λ ≤ Eminus Λ + d by linarith [hd.1])
    rw [Density_T_of_le hΛ hℓ (le_refl _)] at hsub
    have hcomp : ∫ s in (0 : ℝ)..d, rho Λ (Eminus Λ + s) = ∫ u in Eminus Λ..Eminus Λ + d, rho Λ u := by
      rw [intervalIntegral.integral_comp_add_left (fun u => rho Λ u) (Eminus Λ)]
      simp
    have hI := Density_integral_sqrt (h := fun s => rho Λ (Eminus Λ + s))
      (hcont.comp (continuous_const.add continuous_id))
      (α := C⁻¹ * Real.sqrt (Real.pi - 1)) (β := C * Real.sqrt (21 / 5))
      (fun s hs => by
        have hx : Eminus Λ + s ∈ Set.Icc (Eminus Λ) (Eplus Λ) :=
          ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have := (hsq Λ hΛ hℓ _ hx).1
        refine le_trans ?_ this
        have e : (Eplus Λ - (Eminus Λ + s)) * (Eminus Λ + s - Eminus Λ) ≥ s * (Real.pi - 1) := by
          have : Real.pi - 1 ≤ Eplus Λ - (Eminus Λ + s) := by linarith [hs.2]
          rw [add_sub_cancel_left, mul_comm]
          exact mul_le_mul_of_nonneg_left this hs.1
        calc C⁻¹ * Real.sqrt (Real.pi - 1) * Real.sqrt s
            = C⁻¹ * Real.sqrt (s * (Real.pi - 1)) := by rw [hsqrt1 s hs.1]; ring
          _ ≤ C⁻¹ * Real.sqrt ((Eplus Λ - (Eminus Λ + s)) * (Eminus Λ + s - Eminus Λ)) := by
              gcongr)
      (fun s hs => by
        have hx : Eminus Λ + s ∈ Set.Icc (Eminus Λ) (Eplus Λ) :=
          ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have := (hsq Λ hΛ hℓ _ hx).2
        refine le_trans this ?_
        have e : (Eplus Λ - (Eminus Λ + s)) * (Eminus Λ + s - Eminus Λ) ≤ s * (21 / 5) := by
          have h1 : Eplus Λ - (Eminus Λ + s) ≤ 21 / 5 := by linarith [hs.1]
          rw [add_sub_cancel_left, mul_comm]
          exact mul_le_mul_of_nonneg_left h1 hs.1
        calc C * Real.sqrt ((Eplus Λ - (Eminus Λ + s)) * (Eminus Λ + s - Eminus Λ))
            ≤ C * Real.sqrt (s * (21 / 5)) := by gcongr
          _ = C * Real.sqrt (21 / 5) * Real.sqrt s := by rw [hsqrt2 s hs.1]; ring)
      hd
    rw [hcomp] at hI
    have : ∫ u in Eminus Λ..Eminus Λ + d, rho Λ u = 1 - Density_T Λ (Eminus Λ + d) := by linarith
    rw [this] at hI
    exact hI

end Density_S18

section Density_S19
open Set

set_option maxHeartbeats 1000000 in
private theorem Density_kappa_aux (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
        c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤
            Eplus (lam D N A) - quant (rho (lam D N A)) (D * N) k ∧
          Eplus (lam D N A) - quant (rho (lam D N A)) (D * N) k ≤
            C * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ∧
          c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤
            quant (rho (lam D N A)) (D * N) (D * N + 1 - k) - Eminus (lam D N A) ∧
          quant (rho (lam D N A)) (D * N) (D * N + 1 - k) - Eminus (lam D N A) ≤
            C * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
  obtain ⟨α, β, hα, hβ, hasym⟩ := Density_edge_asym.{0}
  have hD1 : 1 ≤ D := by omega
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  set a₁ : ℝ := (2 / 3) * α with ha₁def
  set b₁ : ℝ := (2 / 3) * β with hb₁def
  have ha₁ : 0 < a₁ := by positivity
  have hb₁ : 0 < b₁ := by positivity
  refine ⟨min ((2 * D * b₁) ^ (-(2 / 3 : ℝ))) ((D : ℝ) ^ (-(2 / 3 : ℝ))),
    21 / 5 * (a₁ * D) ^ (-(2 / 3 : ℝ)),
    lt_min (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hD0 _),
    by have := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < a₁ * D) (-(2 / 3 : ℝ)); positivity,
    max 1 ⌈(20 * (D : ℝ) ^ 2) ^ (1 / δA)⌉₊, ?_⟩
  intro N hN A hA k hk1 hkD
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNceil : (20 * (D : ℝ) ^ 2) ^ (1 / δA) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have h20 : 20 * (D : ℝ) ^ 2 ≤ (N : ℝ) ^ δA := by
    calc 20 * (D : ℝ) ^ 2 = ((20 * (D : ℝ) ^ 2) ^ (1 / δA)) ^ δA := by
          rw [← Real.rpow_mul (by positivity)]; field_simp; simp
      _ ≤ (N : ℝ) ^ δA := Real.rpow_le_rpow (by positivity) hNceil hδA.le
  have hNpow : (N : ℝ) ^ (-δA) = ((N : ℝ) ^ δA)⁻¹ := Real.rpow_neg hN0.le _
  have hℓA : 2 * (D : ℝ) ^ 2 * opNorm A ≤ 1 / 10 := by
    have h1 : opNorm A ≤ (20 * (D : ℝ) ^ 2)⁻¹ := by
      refine hA.trans ?_
      rw [hNpow]
      exact inv_anti₀ (by positivity) h20
    calc 2 * (D : ℝ) ^ 2 * opNorm A ≤ 2 * (D : ℝ) ^ 2 * (20 * (D : ℝ) ^ 2)⁻¹ := by gcongr
      _ = 1 / 10 := by field_simp; norm_num
  have hℓ : opNorm (lam D N A) ≤ 1 / 10 := (Density_opNorm_lam D N hN1 A).trans hℓA
  haveI : Nonempty (Idx D N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hΛ := Density_lam_isHermitian D N A
  set Λ := lam D N A with hΛdef
  obtain ⟨hlt, -⟩ := rho_support Λ hΛ hℓ
  obtain ⟨hw1, hw2⟩ := Density_width hΛ hℓ
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkDN : (k : ℝ) ≤ D * N := by exact_mod_cast hkD
  have hMcast : ((D * N : ℕ) : ℝ) = (D : ℝ) * N := by push_cast; ring
  have hDN0 : (0 : ℝ) < (D : ℝ) * N := by positivity
  set p : ℝ := ((k : ℝ) - 1 / 2) / ((D * N : ℕ) : ℝ) with hp
  have hp0 : 0 < p := by rw [hp, hMcast]; apply div_pos <;> linarith
  have hp1 : p < 1 := by rw [hp, hMcast, div_lt_one hDN0]; linarith
  -- the mirror index
  have hk' : D * N + 1 - k ≤ D * N := by omega
  have hk'1 : 1 ≤ D * N + 1 - k := by omega
  have hkc : (((D * N + 1 - k : ℕ)) : ℝ) = (D : ℝ) * N + 1 - k := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  set p' : ℝ := (((D * N + 1 - k : ℕ) : ℝ) - 1 / 2) / ((D * N : ℕ) : ℝ) with hp'
  have hp'p : p' = 1 - p := by
    rw [hp', hp, hkc, hMcast]; field_simp; ring
  have hp'0 : 0 < p' := by rw [hp'p]; linarith
  have hp'1 : p' < 1 := by rw [hp'p]; linarith
  obtain ⟨γ, hγ1, hγ2, hTγ, hγiff⟩ := Density_quant_spec hΛ hℓ hp0 hp1
  obtain ⟨γ', hγ1', hγ2', hTγ', hγiff'⟩ := Density_quant_spec hΛ hℓ hp'0 hp'1
  have hq : quant (rho Λ) (D * N) k = γ := Density_quant_eq hγiff (D * N) k rfl
  have hq' : quant (rho Λ) (D * N) (D * N + 1 - k) = γ' := Density_quant_eq hγiff' (D * N) _ rfl
  rw [hq, hq']
  -- common data
  set K : ℝ := (k : ℝ) / N with hK
  have hK0 : 0 < K := by positivity
  have hKD : K ≤ D := by rw [hK, div_le_iff₀ hN0]; linarith
  have hpp1 : K / (2 * D) ≤ p := by
    rw [hp, hMcast, hK, div_div, div_le_div_iff₀ (by positivity) hDN0]
    nlinarith
  have hpp2 : p ≤ K / D := by
    rw [hp, hMcast, hK, div_div, div_le_div_iff₀ hDN0 (by positivity)]
    nlinarith
  have hconv : K ^ (2 / 3 : ℝ) = (k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [hK, Real.div_rpow (by positivity) hN0.le, Real.rpow_neg hN0.le, div_eq_mul_inv]
  have hdone : ∀ d : ℝ, 0 < d → d ≤ 21 / 5 → p ∈ Set.Icc (K / (2 * D)) (K / D) →
      (d ≤ 1 → a₁ * d ^ (3 / 2 : ℝ) ≤ p ∧ p ≤ b₁ * d ^ (3 / 2 : ℝ)) → (1 < d → a₁ ≤ p) →
      min ((2 * D * b₁) ^ (-(2 / 3 : ℝ))) ((D : ℝ) ^ (-(2 / 3 : ℝ))) *
          ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤ d ∧
        d ≤ 21 / 5 * (a₁ * D) ^ (-(2 / 3 : ℝ)) * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
    intro d hd0 hdL hpI h1 h2
    rw [← hconv]
    exact Density_two_case ha₁ hb₁ hD1 hK0 hKD hpI.1 hpI.2 hd0 hdL h1 h2
  have hpI : p ∈ Set.Icc (K / (2 * D)) (K / D) := ⟨hpp1, hpp2⟩
  have hR := hdone (Eplus Λ - γ) (by linarith) (by linarith) hpI
    (fun hd1 => by
      have := (hasym Λ hΛ hℓ (Eplus Λ - γ) ⟨by linarith, hd1⟩).1
      rw [show Eplus Λ - (Eplus Λ - γ) = γ by ring, hTγ] at this
      exact this)
    (fun hd1 => by
      have h1 := (hasym Λ hΛ hℓ 1 ⟨by norm_num, le_refl _⟩).1.1
      rw [Real.one_rpow, mul_one] at h1
      have h2 := Density_T_antitone hΛ hℓ (show Eplus Λ - (Eplus Λ - γ) ≤ Eplus Λ - 1 by linarith)
      rw [show Eplus Λ - (Eplus Λ - γ) = γ by ring] at h2
      have h3 : γ ≤ Eplus Λ - 1 := by linarith
      have := Density_T_antitone hΛ hℓ h3
      rw [hTγ] at this
      rw [ha₁def]
      linarith)
  have hpL : 1 - Density_T Λ γ' = p := by rw [hTγ', hp'p]; ring
  have hL := hdone (γ' - Eminus Λ) (by linarith) (by linarith) hpI
    (fun hd1 => by
      have := (hasym Λ hΛ hℓ (γ' - Eminus Λ) ⟨by linarith, hd1⟩).2
      rw [show Eminus Λ + (γ' - Eminus Λ) = γ' by ring, hpL] at this
      exact this)
    (fun hd1 => by
      have h1 := (hasym Λ hΛ hℓ 1 ⟨by norm_num, le_refl _⟩).2.1
      rw [Real.one_rpow, mul_one] at h1
      have h3 : Eminus Λ + 1 ≤ γ' := by linarith
      have h2 := Density_T_antitone hΛ hℓ h3
      rw [ha₁def]
      linarith)
  exact ⟨hR.1, hR.2, hL.1, hL.2⟩

end Density_S19

/-- `m` is the Stieltjes transform of the probability density `ρ_N` of (2.19)
[eq:density_rhoN] (Definition 2.7 [defn_Mm] and the text after it). -/
theorem rho_stieltjes {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) :
    (∀ x, 0 ≤ rho Λ x) ∧ Continuous (rho Λ) ∧ Integrable (rho Λ) ∧ ∫ x, rho Λ x = 1 ∧
      ∀ z : ℂ, 0 < z.im → mSol Λ z = ∫ x : ℝ, (rho Λ x : ℂ) / ((x : ℂ) - z) := by
  refine ⟨Density_rho_nonneg hΛ hℓ, Density_rho_continuous hΛ hℓ, Density_rho_integrable hΛ hℓ,
    Density_mass hΛ hℓ, fun z hz => Density_rep hΛ hℓ hz⟩

/-- The case `Λ = 0` of Definition 2.7 [defn_Mm]: `m = m_sc`, `ρ_N = ρ_sc` of (2.18)
[eq:semidensity], `E^± = ±2`, `γ_± = 1`, and `m_sc` solves `m² + zm + 1 = 0` with `Im m_sc > 0`
on the upper half plane. -/
theorem rho_zero {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (∀ z : ℂ, mExt (0 : Matrix ι ι ℂ) z = msc z) ∧ rho (0 : Matrix ι ι ℂ) = rhoSc ∧
      Eplus (0 : Matrix ι ι ℂ) = 2 ∧ Eminus (0 : Matrix ι ι ℂ) = -2 ∧
      gammaPlus (0 : Matrix ι ι ℂ) = 1 ∧ gammaMinus (0 : Matrix ι ι ℂ) = 1 ∧
      ∀ z : ℂ, 0 < z.im → msc z ^ 2 + z * msc z + 1 = 0 ∧ 0 < (msc z).im := by
  obtain ⟨hp, hm⟩ := Density_zero_edges (ι := ι)
  obtain ⟨hgp, hgm⟩ := Density_zero_gamma (ι := ι)
  exact ⟨Density_mExt_zero, funext Density_rho_zero_eq, hp, hm, hgp, hgm,
    fun z hz => Density_msc_quad hz⟩

/-- Definition 2.10 [def_moving_Lambda]: for a continuous family `Λ_t` of Hermitian matrices
with `‖Λ_t‖ ≤ 1/10`, the edges `E_t^±`, the quantiles `γ_k(t)` and `m_t(z)` depend continuously
on `t` (and on `z` in the upper half plane). -/
theorem moving_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λt : ℝ → Matrix ι ι ℂ) (hc : Continuous Λt) (hH : ∀ t, (Λt t).IsHermitian)
    (hℓ : ∀ t, opNorm (Λt t) ≤ 1 / 10) :
    Continuous (fun t => Eplus (Λt t)) ∧ Continuous (fun t => Eminus (Λt t)) ∧
      (∀ Mc k : ℕ, 1 ≤ k → k ≤ Mc → Continuous fun t => quant (rho (Λt t)) Mc k) ∧
      ContinuousOn (fun p : ℝ × ℂ => mSol (Λt p.1) p.2) {p : ℝ × ℂ | 0 < p.2.im} := by
  exact Density_moving hc hH hℓ

/-- (A.4) [equation_E_in_spectrum]: `⟨M(E) M(E)^*⟩ = 1` for `E ∈ [E⁻, E⁺]`. -/
theorem equation_E_in_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10) (E : ℝ)
    (hE : E ∈ Set.Icc (Eminus Λ) (Eplus Λ)) :
    ntr (MExt Λ E * (MExt Λ E)ᴴ) = 1 := by
  exact Density_equation_E hΛ hℓ E hE

/-- (2.21) [eq:kappa_gamma_k]: `E⁺ - γ_k ∼ k^{2/3} N^{-2/3}` and `γ_{DN+1-k} - E⁻ ∼ k^{2/3}
N^{-2/3}` for `k ∈ ⟦1, DN⟧`, `Λ = lam D N A`, `‖A‖ ≤ N^{-δ_A}`; the constants depend on `D`
and `δ_A` only. -/
theorem kappa_gamma_k (D : ℕ) (hD : 2 ≤ D) (δA : ℝ) (hδA : 0 < δA) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Matrix (Fin N) (Fin N) ℂ, opNorm A ≤ (N : ℝ) ^ (-δA) →
      ∀ k : ℕ, 1 ≤ k → k ≤ D * N →
        c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤
            Eplus (lam D N A) - quant (rho (lam D N A)) (D * N) k ∧
          Eplus (lam D N A) - quant (rho (lam D N A)) (D * N) k ≤
            C * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ∧
          c * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ≤
            quant (rho (lam D N A)) (D * N) (D * N + 1 - k) - Eminus (lam D N A) ∧
          quant (rho (lam D N A)) (D * N) (D * N + 1 - k) - Eminus (lam D N A) ≤
            C * ((k : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
  exact Density_kappa_aux D hD δA hδA

end RBMTransitionEdge

end
