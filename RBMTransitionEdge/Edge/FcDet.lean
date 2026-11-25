module

public import RBMTransitionEdge.Edge.Defs
public import RBMTransitionEdge.Localized.Pathwise

@[expose] public section

/-!
# The free-convolution data of the deterministic density in Lemma 4.1

The subordination identity `m(z) = m_V(z + t' m(z))` for `V = c⁻¹H + Λ`, the moments of `ρ_N` just
right of `E⁺`, and the identification of the free-convolution edge and curvature of `ρ_V` with
`E⁺` and `γ₊` (proof of Lemma 4.1 [CVtG], after [CorrelatedBandAOP, Section 6.1]).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section
open Classical

namespace RBMTransitionEdge

section FcDetAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `U diag(d) U^*` for a unitary `U`. -/
private def FcDet_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (diagonal d)

private lemma FcDet_cd_mul (U : Matrix.unitaryGroup ι ℂ) (d e : ι → ℂ) :
    FcDet_cd U d * FcDet_cd U e = FcDet_cd U (fun j => d j * e j) := by
  rw [FcDet_cd, FcDet_cd, FcDet_cd, ← map_mul, diagonal_mul_diagonal]

private lemma FcDet_cd_one (U : Matrix.unitaryGroup ι ℂ) : FcDet_cd U (fun _ => 1) = 1 := by
  rw [FcDet_cd, diagonal_one, map_one]

private lemma FcDet_cd_smul (U : Matrix.unitaryGroup ι ℂ) (c : ℂ) (d : ι → ℂ) :
    c • FcDet_cd U d = FcDet_cd U (fun j => c * d j) := by
  rw [FcDet_cd, FcDet_cd, ← map_smul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

private lemma FcDet_cd_sub_smul_one (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (c : ℂ) :
    FcDet_cd U d - c • (1 : Matrix ι ι ℂ) = FcDet_cd U (fun j => d j - c) := by
  rw [← FcDet_cd_one U, FcDet_cd_smul, FcDet_cd, FcDet_cd, FcDet_cd, ← map_sub, diagonal_sub]
  simp

private lemma FcDet_ntr_cd (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    ntr (FcDet_cd U d) = ((Fintype.card ι : ℂ))⁻¹ * ∑ j, d j := by
  rw [ntr, FcDet_cd, Unitary.conjStarAlgAut_apply, trace_mul_comm, ← mul_assoc,
    Unitary.star_mul_self_of_mem U.property, one_mul, trace_diagonal]

private lemma FcDet_cd_inv (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (h : ∀ j, d j ≠ 0) :
    (FcDet_cd U d)⁻¹ = FcDet_cd U (fun j => (d j)⁻¹) := by
  apply inv_eq_right_inv
  rw [FcDet_cd_mul]
  simp only [mul_inv_cancel₀ (h _)]
  exact FcDet_cd_one U

private lemma FcDet_cd_ct (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) :
    (FcDet_cd U d)ᴴ = FcDet_cd U (fun j => star (d j)) := by
  rw [← star_eq_conjTranspose, FcDet_cd, ← map_star, star_eq_conjTranspose,
    diagonal_conjTranspose]
  rfl

private lemma FcDet_cd_real_smul (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (s : ℝ) :
    (s : ℂ) • FcDet_cd U (fun j => (μ j : ℂ)) = FcDet_cd U (fun j => ((s * μ j : ℝ) : ℂ)) := by
  rw [FcDet_cd_smul]
  congr 1
  funext j
  push_cast
  ring

/-- Every eigenvalue of a Hermitian matrix is bounded by the operator norm. -/
private lemma FcDet_eig_le {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) (j : ι) :
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
private lemma FcDet_decomp {Λ : Matrix ι ι ℂ} (hΛ : Λ.IsHermitian) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ),
      Λ = FcDet_cd U (fun j => (μ j : ℂ)) ∧ ∀ j, |μ j| ≤ opNorm Λ :=
  ⟨_, _, hΛ.spectral_theorem, FcDet_eig_le hΛ⟩

/-- The resolvent of `U diag(ν) U^*` at a point off the spectrum. -/
private lemma FcDet_res (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) {ζ : ℂ}
    (h : ∀ j, (ν j : ℂ) ≠ ζ) :
    (FcDet_cd U (fun j => (ν j : ℂ)) - ζ • (1 : Matrix ι ι ℂ))⁻¹ =
      FcDet_cd U (fun j => ((ν j : ℂ) - ζ)⁻¹) := by
  rw [FcDet_cd_sub_smul_one, FcDet_cd_inv _ _ fun j => sub_ne_zero.2 (h j)]

/-- The normalized average `n⁻¹ Σ_j f_j`. -/
private def FcDet_av (f : ι → ℝ) : ℝ := ((Fintype.card ι : ℝ))⁻¹ * ∑ j, f j

/-- `⟨(ν - w)⁻¹⟩ = -⟨(w - ν)⁻¹⟩` at a real point `w` off the spectrum. -/
private lemma FcDet_ntr_res (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) {w : ℝ}
    (h : ∀ j, ν j ≠ w) :
    ntr (FcDet_cd U (fun j => (ν j : ℂ)) - (w : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ =
      ((-FcDet_av (fun j => (w - ν j)⁻¹) : ℝ) : ℂ) := by
  rw [FcDet_res U ν (fun j e => h j (by exact_mod_cast e)), FcDet_ntr_cd, FcDet_av]
  push_cast
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← inv_neg, neg_sub]

/-- `⟨M M^*⟩ = ⟨(w - ν)^{-2}⟩` for `M = (U diag(ν) U^* - w)⁻¹` at a real point `w`. -/
private lemma FcDet_ntr_res_sq (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) {w : ℝ}
    (h : ∀ j, ν j ≠ w) :
    ntr ((FcDet_cd U (fun j => (ν j : ℂ)) - (w : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ *
      ((FcDet_cd U (fun j => (ν j : ℂ)) - (w : ℂ) • (1 : Matrix ι ι ℂ))⁻¹)ᴴ) =
      ((FcDet_av (fun j => ((w - ν j) ^ 2)⁻¹) : ℝ) : ℂ) := by
  rw [FcDet_res U ν (fun j e => h j (by exact_mod_cast e)), FcDet_cd_ct, FcDet_cd_mul,
    FcDet_ntr_cd, FcDet_av]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ((ν j : ℂ) - (w : ℂ)) = (((ν j - w : ℝ)) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← mul_inv, ← sq]
  push_cast
  ring

end FcDetAux

/-- The subordination identity of the proof of Lemma 4.1 [CVtG]: for Hermitian `Λ`, `c ≥ 1` and
`Im z > 0`, `m(z) = m_V(z + t' m(z))` with `t' = 1 - c^{-2}` and `m_V(ζ) = c m_{cΛ}(cζ)`, where
`m_{cΛ}` solves (2.16) [self_m] for `cΛ` (`V = c⁻¹ H + Λ`, `c = e^{𝔱/2}`). -/
theorem mSol_subord {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (c : ℝ) (hc : 1 ≤ c) (z : ℂ) (hz : 0 < z.im) :
    mSol Λ z =
      (c : ℂ) * mSol ((c : ℂ) • Λ) ((c : ℂ) * (z + ((1 - c⁻¹ ^ 2 : ℝ) : ℂ) * mSol Λ z)) := by
  obtain ⟨hμim, hμeq, hμinv⟩ := mSol_spec Λ hΛ z hz
  set μ := mSol Λ z with hμdef
  have hc0 : (0 : ℝ) < c := by linarith
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc0.ne'
  have ht : 0 ≤ 1 - c⁻¹ ^ 2 := by
    have h1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
    have h2 : 0 ≤ c⁻¹ := by positivity
    nlinarith
  set ζ : ℂ := (c : ℂ) * (z + ((1 - c⁻¹ ^ 2 : ℝ) : ℂ) * μ) with hζdef
  have hζ : 0 < ζ.im := by
    have e : ζ.im = c * (z.im + (1 - c⁻¹ ^ 2) * μ.im) := by
      simp only [hζdef, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        zero_mul, add_zero, Complex.add_re]
    rw [e]
    have := mul_nonneg ht hμim.le
    positivity
  have hherm : ((c : ℂ) • Λ).IsHermitian := hΛ.smul (by simp [IsSelfAdjoint])
  set A : Matrix ι ι ℂ := Λ - (z + μ) • (1 : Matrix ι ι ℂ) with hA
  have hsum : ζ + μ / (c : ℂ) = (c : ℂ) * (z + μ) := by
    rw [hζdef]
    push_cast
    field_simp
    ring
  have hmat : (c : ℂ) • Λ - (ζ + μ / (c : ℂ)) • (1 : Matrix ι ι ℂ) = (c : ℂ) • A := by
    rw [hsum, hA, smul_sub, smul_smul]
  have hinv : ((c : ℂ) • A)⁻¹ = (c : ℂ)⁻¹ • MSol Λ z := by
    apply inv_eq_right_inv
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hcC, one_smul]
    exact hμinv
  have hw : 0 < (μ / (c : ℂ)).im ∧
      μ / (c : ℂ) = ntr ((c : ℂ) • Λ - (ζ + μ / (c : ℂ)) • (1 : Matrix ι ι ℂ))⁻¹ := by
    refine ⟨?_, ?_⟩
    · rw [Complex.div_ofReal_im]; positivity
    · rw [hmat, hinv, ntr, trace_smul, smul_eq_mul]
      rw [ntr] at hμeq
      rw [div_eq_inv_mul, hμeq]
      ring
  obtain ⟨h2im, h2eq, -⟩ := mSol_spec _ hherm ζ hζ
  have huniq := (mSol_existsUnique _ hherm ζ hζ).unique ⟨h2im, h2eq⟩ hw
  rw [huniq]
  field_simp

section FcDetBd

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The boundary value `m(x)` at a real point is the limit of `m(x + iη)` as `η ↓ 0`. -/
private lemma FcDet_tendsto_bd (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (x : ℝ) :
    Tendsto (fun η : ℝ => mSol Λ ((x : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 (mExt Λ x)) := by
  have hcont := (mExt_boundary Λ hΛ hℓ).1
  have hx : (x : ℂ) ∈ {z : ℂ | 0 ≤ z.im} := by simp
  have hg : Tendsto (fun η : ℝ => (x : ℂ) + (η : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Continuous fun η : ℝ => (x : ℂ) + (η : ℂ) * Complex.I := by fun_prop
      have h0 := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using h0
    · filter_upwards [self_mem_nhdsWithin] with η hη
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
      exact le_of_lt hη
  refine ((hcont _ hx).tendsto.comp hg).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have him : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
  simp only [Function.comp_apply, mExt, him, ↓reduceIte]

/-- `Im m(x) = π ρ_N(x)` at a real point `x`, (2.19) [eq:density_rhoN]. -/
private lemma FcDet_im_mExt (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (x : ℝ) : (mExt Λ x).im = Real.pi * rho Λ x := by
  have h2 : Tendsto (fun η : ℝ => (mSol Λ ((x : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] 0)
      (𝓝 (mExt Λ x).im) := (Complex.continuous_im.tendsto _).comp (FcDet_tendsto_bd Λ hΛ hℓ x)
  rw [rho, h2.limUnder_eq]
  field_simp

/-- Off `[E⁻, E⁺]`, the boundary value `m(x)` is the real Stieltjes integral
`∫ ρ_N(y)/(y - x) dy`. -/
private lemma FcDet_stieltjes_real (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian)
    (hℓ : opNorm Λ ≤ 1 / 10) (x : ℝ) (hx : x ∉ Set.Icc (Eminus Λ) (Eplus Λ)) :
    mExt Λ x = ((∫ y, rho Λ y / (y - x) : ℝ) : ℂ) := by
  obtain ⟨hρ0, hρc, hρi, -, hrep⟩ := rho_stieltjes Λ hΛ hℓ
  have hsupp := (rho_support Λ hΛ hℓ).2
  have hmem : ∀ y, rho Λ y ≠ 0 → y ∈ Set.Ioo (Eminus Λ) (Eplus Λ) := fun y hy => by
    rw [← hsupp]; exact hy
  obtain ⟨δ, hδ, hδy⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ y, rho Λ y ≠ 0 → δ ≤ |y - x| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · refine ⟨Eminus Λ - x, by linarith, fun y hy => ?_⟩
      have := (hmem y hy).1
      rw [abs_of_pos (by linarith)]; linarith
    · refine ⟨x - Eplus Λ, by linarith, fun y hy => ?_⟩
      have := (hmem y hy).2
      rw [abs_of_neg (by linarith)]; linarith
  have hlim : Tendsto (fun η : ℝ => ∫ y, (rho Λ y : ℂ) / ((y : ℂ) - ((x : ℂ) + (η : ℂ) *
      Complex.I))) (𝓝[>] 0) (𝓝 (∫ y, (rho Λ y : ℂ) / ((y : ℂ) - (x : ℂ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => rho Λ y / δ) ?_ ?_
      (hρi.div_const δ) ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      refine Continuous.aestronglyMeasurable ?_
      refine (Complex.continuous_ofReal.comp hρc).div (by fun_prop) fun y e => ?_
      exact (ne_of_gt hη) (by simpa using congrArg Complex.im e)
    · filter_upwards [self_mem_nhdsWithin] with η hη
      refine Eventually.of_forall fun y => ?_
      by_cases hy : rho Λ y = 0
      · simp [hy]
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ0 y)]
        apply div_le_div_of_nonneg_left (hρ0 y) hδ
        refine (hδy y hy).trans ?_
        have := Complex.abs_re_le_norm ((y : ℂ) - ((x : ℂ) + (η : ℂ) * Complex.I))
        simpa using this
    · refine Eventually.of_forall fun y => ?_
      by_cases hy : rho Λ y = 0
      · simp [hy]
      · have hyx : (y : ℂ) - (x : ℂ) ≠ 0 := by
          have h2 := hδy y hy
          intro e
          have h1 : y - x = 0 := by exact_mod_cast e
          rw [h1, abs_zero] at h2
          linarith
        have hd : Continuous (fun η : ℝ => (y : ℂ) - ((x : ℂ) + (η : ℂ) * Complex.I)) := by
          fun_prop
        have h0 : (y : ℂ) - ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = (y : ℂ) - (x : ℂ) := by
          simp only [Complex.ofReal_zero, zero_mul, add_zero]
        have hc := Filter.Tendsto.div (tendsto_const_nhds (x := (rho Λ y : ℂ)))
          (hd.tendsto 0) (by rw [h0]; exact hyx)
        have := hc.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        rw [h0] at this
        exact this
  have hlim' : Tendsto (fun η : ℝ => ∫ y, (rho Λ y : ℂ) / ((y : ℂ) - ((x : ℂ) + (η : ℂ) *
      Complex.I))) (𝓝[>] 0) (𝓝 (mExt Λ x)) := by
    refine (FcDet_tendsto_bd Λ hΛ hℓ x).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hrep _ (by simpa using hη)
  rw [tendsto_nhds_unique hlim' hlim]
  have e : (fun y : ℝ => (rho Λ y : ℂ) / ((y : ℂ) - (x : ℂ))) =
      fun y => ((rho Λ y / (y - x) : ℝ) : ℂ) := by
    funext y; push_cast; rfl
  rw [e, integral_complex_ofReal]

end FcDetBd

section FcDetMom

/-- `S_j(x) = ∫ ρ(y)(x - y)^{-j} dy`, the moments of a density at a real point `x`. -/
private def FcDet_S (ρ : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ := ∫ y, ρ y / (x - y) ^ j

/-- `d/dx a (x - y)^{-(k+1)} = -(k+1) a (x - y)^{-(k+2)}`. -/
private lemma FcDet_hasDerivAt_pow (a y x : ℝ) (k : ℕ) (hx : x - y ≠ 0) :
    HasDerivAt (fun x => a / (x - y) ^ (k + 1)) (a * (-((k : ℝ) + 1)) / (x - y) ^ (k + 2)) x := by
  have hp : HasDerivAt (fun x => (x - y) ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * (x - y) ^ k * 1) x :=
    ((hasDerivAt_id x).sub_const y).pow (k + 1)
  have := (hasDerivAt_const x a).div hp (pow_ne_zero _ hx)
  convert this using 1
  push_cast
  field_simp
  ring

/-- For `x ≥ E + ε` and `ρ` supported in `(-∞, E)`, `|ρ(y)(x - y)^{-n}| ≤ ρ(y) ε^{-n}`. -/
private lemma FcDet_bd {ρ : ℝ → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y) {E : ℝ}
    (hsupp : ∀ y, ρ y ≠ 0 → y < E) {ε x : ℝ} (hε : 0 < ε) (hx : E + ε ≤ x) (n : ℕ) (y : ℝ) :
    ‖ρ y / (x - y) ^ n‖ ≤ ρ y / ε ^ n := by
  by_cases hy : ρ y = 0
  · simp [hy]
  · have h1 := hsupp y hy
    have h2 : ε ≤ x - y := by linarith
    rw [norm_div, Real.norm_eq_abs, abs_of_nonneg (hρ0 y), norm_pow, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    exact div_le_div_of_nonneg_left (hρ0 y) (pow_pos hε n) (pow_le_pow_left₀ hε.le h2 n)

private lemma FcDet_meas {ρ : ℝ → ℝ} (hρc : Continuous ρ) (n : ℕ) (x : ℝ) :
    AEStronglyMeasurable (fun y => ρ y / (x - y) ^ n) volume :=
  (hρc.measurable.div ((measurable_const.sub measurable_id).pow_const n)).aestronglyMeasurable

/-- The integrand of `S_n(x)` is integrable for `x > E`. -/
private lemma FcDet_int {ρ : ℝ → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y) (hρc : Continuous ρ)
    (hρi : Integrable ρ) {E : ℝ} (hsupp : ∀ y, ρ y ≠ 0 → y < E) {x : ℝ} (hx : E < x) (n : ℕ) :
    Integrable (fun y => ρ y / (x - y) ^ n) :=
  Integrable.mono' (hρi.div_const ((x - E) ^ n)) (FcDet_meas hρc n x)
    (Eventually.of_forall fun y => FcDet_bd hρ0 hsupp (sub_pos.2 hx) (by linarith) n y)

/-- `S_{k+1}' = -(k+1) S_{k+2}` on `(E, ∞)` for a density supported in `(-∞, E)`. -/
private lemma FcDet_S_deriv {ρ : ℝ → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y) (hρc : Continuous ρ)
    (hρi : Integrable ρ) {E : ℝ} (hsupp : ∀ y, ρ y ≠ 0 → y < E) {x₀ : ℝ} (hx₀ : E < x₀)
    (k : ℕ) :
    HasDerivAt (FcDet_S ρ (k + 1)) (-((k : ℝ) + 1) * FcDet_S ρ (k + 2) x₀) x₀ := by
  set ε := (x₀ - E) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hs : Set.Ioi (E + ε) ∈ 𝓝 x₀ := Ioi_mem_nhds (by rw [hε]; linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun x y => ρ y / (x - y) ^ (k + 1))
    (F' := fun x y => ρ y * (-((k : ℝ) + 1)) / (x - y) ^ (k + 2))
    (bound := fun y => ((k : ℝ) + 1) * (ρ y / ε ^ (k + 2))) hs
    (Eventually.of_forall fun x => FcDet_meas hρc (k + 1) x)
    (FcDet_int hρ0 hρc hρi hsupp hx₀ (k + 1))
    (((hρc.measurable.mul_const _).div
      ((measurable_const.sub measurable_id).pow_const _)).aestronglyMeasurable)
    (Eventually.of_forall fun y x hx => by
      have h := FcDet_bd hρ0 hsupp hε0 (le_of_lt hx) (k + 2) y
      rw [mul_comm, mul_div_assoc, norm_mul, Real.norm_eq_abs, abs_neg,
        abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left h (by positivity))
    ((hρi.div_const _).const_mul _)
    (Eventually.of_forall fun y x hx => by
      by_cases hy : ρ y = 0
      · simp only [hy, zero_div, zero_mul]
        exact hasDerivAt_const x 0
      · have h1 := hsupp y hy
        have hx' : E + ε < x := hx
        exact FcDet_hasDerivAt_pow (ρ y) y x k (by linarith))
  have e : ∫ y, ρ y * (-((k : ℝ) + 1)) / (x₀ - y) ^ (k + 2) =
      -((k : ℝ) + 1) * FcDet_S ρ (k + 2) x₀ := by
    rw [FcDet_S, ← integral_const_mul]
    congr 1; funext y; ring
  rw [← e]
  exact key.2

/-- `rhoMom Λ c j ξ = c^j S_j(cξ)` for `S_j` the moments of `ρ_N` of `Λ` (substitution `y = cx`). -/
private lemma FcDet_rhoMom_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℂ) {c : ℝ}
    (hc : 0 < c) (j : ℕ) (ξ : ℝ) :
    rhoMom Λ c j ξ = c ^ j * FcDet_S (rho Λ) j (c * ξ) := by
  have h1 : rhoMom Λ c j ξ = ∫ x, (fun y => c * rho Λ y / (ξ - y / c) ^ j) (c * x) := by
    rw [rhoMom]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_div_cancel_left₀ x hc.ne']
  have h2 : ∀ y : ℝ, c * rho Λ y / (ξ - y / c) ^ j =
      c * c ^ j * (rho Λ y / (c * ξ - y) ^ j) := fun y => by
    have : ξ - y / c = (c * ξ - y) / c := by field_simp
    rw [this, div_pow, div_div_eq_mul_div]
    ring
  rw [h1, Measure.integral_comp_mul_left (fun y => c * rho Λ y / (ξ - y / c) ^ j) c,
    abs_of_pos (inv_pos.2 hc), smul_eq_mul]
  simp only [h2]
  rw [integral_const_mul, FcDet_S]
  field_simp

end FcDetMom

section FcDetG

variable {ι : Type*} [Fintype ι]

/-- `G_k(u) = ⟨(u - ν)^{-k}⟩` for real eigenvalues `ν`. -/
private def FcDet_G (ν : ι → ℝ) (k : ℕ) (u : ℝ) : ℝ := FcDet_av (fun j => ((u - ν j) ^ k)⁻¹)

/-- `G_{k+1}' = -(k+1) G_{k+2}` off the spectrum. -/
private lemma FcDet_G_deriv (ν : ι → ℝ) (k : ℕ) {u : ℝ} (hu : ∀ j, u - ν j ≠ 0) :
    HasDerivAt (FcDet_G ν (k + 1)) (-((k : ℝ) + 1) * FcDet_G ν (k + 2) u) u := by
  have hs : HasDerivAt (fun u => ∑ j, 1 / (u - ν j) ^ (k + 1))
      (∑ j, 1 * (-((k : ℝ) + 1)) / (u - ν j) ^ (k + 2)) u :=
    HasDerivAt.fun_sum fun j _ => FcDet_hasDerivAt_pow 1 (ν j) u k (hu j)
  have := hs.const_mul ((Fintype.card ι : ℝ))⁻¹
  unfold FcDet_G FcDet_av
  convert this using 1
  · funext u; simp only [one_div]
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end FcDetG

section FcDetEdgeMom

/-- An integrand vanishing off `(a, b)` integrates over `ℝ` as over `[a, b]`. -/
private lemma FcDet_int_eq_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, x ∉ Set.Ioo a b → f x = 0) : ∫ x, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x (hx : x ∉ Set.Ioc a b) =>
    h x (fun h' : x ∈ Set.Ioo a b => hx ⟨h'.1, h'.2.le⟩))).symm

/-- `κ^{3/2 - j} = √κ · κ / κ^j` for `κ > 0`. -/
private lemma FcDet_rpow_eq {κ : ℝ} (hκ : 0 < κ) (j : ℕ) :
    κ ^ ((3 / 2 : ℝ) - j) = Real.sqrt κ * κ / κ ^ j := by
  rw [Real.rpow_sub hκ, Real.rpow_natCast, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.rpow_add hκ, Real.rpow_one, Real.sqrt_eq_rpow]

/-- `√v / v^j = v^{1/2 - j}` for `v > 0`. -/
private lemma FcDet_rpow_eq' {v : ℝ} (hv : 0 < v) (j : ℕ) :
    Real.sqrt v / v ^ j = v ^ ((1 / 2 : ℝ) - j) := by
  rw [Real.rpow_sub hv, Real.rpow_natCast, Real.sqrt_eq_rpow]

end FcDetEdgeMom

/-- The moments of `ρ_N` just right of `E⁺` (proof of Lemma 4.1 [CVtG]), from (A.1)
[square_root_density]: for Hermitian `Λ` with `‖Λ‖ ≤ 1/10`, `j = 2, 3, 4` and `0 < κ ≤ 1`,
`∫ ρ_N(x)(E⁺ + κ - x)^{-j} dx ∼ κ^{3/2-j}`, with a constant independent of `Λ`. -/
theorem rhoMom_edge :
    ∃ K : ℝ, 0 < K ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ),
      Λ.IsHermitian → opNorm Λ ≤ 1 / 10 → ∀ j : ℕ, 2 ≤ j → j ≤ 4 → ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
        K⁻¹ * κ ^ ((3 / 2 : ℝ) - j) ≤ rhoMom Λ 1 j (Eplus Λ + κ) ∧
          rhoMom Λ 1 j (Eplus Λ + κ) ≤ K * κ ^ ((3 / 2 : ℝ) - j) := by
  obtain ⟨C, hC, hsq⟩ := square_root_density 1 one_pos
  obtain ⟨C₂, hC₂, hedge⟩ := edge_close_to_edge_sc
  set L₀ : ℝ := 4 + C₂ / 10 with hL₀
  set ℓ₀ : ℝ := min 1 C⁻¹ with hℓ₀
  set β : ℝ := min 1 (ℓ₀ / 2) with hβ
  have hℓ₀p : 0 < ℓ₀ := lt_min one_pos (inv_pos.2 hC)
  have hβp : 0 < β := lt_min one_pos (by positivity)
  set Kup : ℝ := 2 * (C * Real.sqrt L₀) with hKup
  set klo : ℝ := C⁻¹ * Real.sqrt (β * ℓ₀ / 4) * (β / 2) / 2 ^ 4 with hklo
  have hKup0 : 0 < Kup := by positivity
  have hklo0 : 0 < klo := by positivity
  refine ⟨max Kup klo⁻¹, lt_max_of_lt_left hKup0, fun ι _ _ _ Λ hΛ hℓ j hj2 hj4 κ hκ hκ1 => ?_⟩
  obtain ⟨hρ0, hρc, hρi, hmass, -⟩ := rho_stieltjes Λ hΛ hℓ
  obtain ⟨hlt, hsupp⟩ := rho_support Λ hΛ hℓ
  have hsqΛ := (hsq ι Λ hΛ hℓ).1
  set Ep := Eplus Λ with hEp
  set Em := Eminus Λ with hEm
  set L := Ep - Em with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  have hzero : ∀ x, x ∉ Set.Ioo Em Ep → rho Λ x = 0 := fun x hx => by
    by_contra h
    exact hx (hsupp ▸ h)
  -- the width `E⁺ - E⁻` is between `ℓ₀` and `L₀`
  have hLup : L ≤ L₀ := by
    have h1 := hedge ι Λ hΛ hℓ
    have h2 : C₂ * opNorm Λ ≤ C₂ / 10 := by nlinarith
    have h3 := le_abs_self (Ep - 2)
    have h4 := neg_le_abs (2 + Em)
    rw [abs_sub_comm] at h3
    rw [hL, hL₀]; linarith
  have hLlo : ℓ₀ ≤ L := by
    have hb : ∀ x ∈ Set.Icc Em Ep, rho Λ x ≤ C * L := fun x hx => by
      refine (hsqΛ x hx).2.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
      rw [Real.sqrt_le_left hL0.le]
      have h1 : Ep - x ≤ L := by rw [hL]; linarith [hx.1]
      have h2 : x - Em ≤ L := by rw [hL]; linarith [hx.2]
      have := mul_le_mul h1 h2 (by linarith [hx.1]) hL0.le
      nlinarith [hx.1, hx.2]
    have hm : (1 : ℝ) ≤ C * L * L := by
      rw [← hmass, FcDet_int_eq_interval hlt.le hzero]
      have := intervalIntegral.integral_mono_on (μ := volume) hlt.le (hρc.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) hb
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      rw [hL] at this ⊢; linarith
    rcases le_or_gt 1 L with h | h
    · exact (min_le_left _ _).trans h
    · refine (min_le_right _ _).trans ?_
      rw [inv_le_iff_one_le_mul₀ hC]
      nlinarith
  -- the integrand
  set f : ℝ → ℝ := fun x => rho Λ x / (Ep + κ - x) ^ j with hf
  have hmom : rhoMom Λ 1 j (Ep + κ) = ∫ x, f x := by
    rw [rhoMom]; simp only [one_mul, hf]
  have hsuppE : ∀ y, rho Λ y ≠ 0 → y < Ep := fun y hy => by
    by_contra h; exact hy (hzero y fun h' => h h'.2)
  have hfi : Integrable f := FcDet_int hρ0 hρc hρi hsuppE (x := Ep + κ) (by linarith) j
  have hf0 : ∀ x, 0 ≤ f x := fun x => by
    by_cases hx : rho Λ x = 0
    · simp [hf, hx]
    · have := hsuppE x hx
      exact div_nonneg (hρ0 x) (pow_nonneg (by linarith) _)
  have hj : (2 : ℝ) ≤ j := by exact_mod_cast hj2
  have hκpow : 0 < κ ^ ((3 / 2 : ℝ) - j) := Real.rpow_pos_of_pos hκ _
  constructor
  · -- lower bound
    set a := κ * β with ha
    have ha0 : 0 < a := by positivity
    have haκ : a ≤ κ := by rw [ha]; nlinarith [min_le_left 1 (ℓ₀ / 2)]
    have haL : a ≤ L / 2 := by
      have : β ≤ ℓ₀ / 2 := min_le_right _ _
      rw [ha]; nlinarith
    set v := C⁻¹ * Real.sqrt (a / 2 * (ℓ₀ / 2)) / (2 * κ) ^ j with hv
    have hpt : ∀ x ∈ Set.Icc (Ep - a) (Ep - a / 2), v ≤ f x := fun x hx => by
      have hxI : x ∈ Set.Icc Em Ep := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have h1 := (hsqΛ x hxI).1
      have hd1 : 0 < Ep + κ - x := by linarith [hx.2]
      have hd2 : Ep + κ - x ≤ 2 * κ := by linarith [hx.1]
      have hs : Real.sqrt (a / 2 * (ℓ₀ / 2)) ≤ Real.sqrt ((Ep - x) * (x - Em)) := by
        apply Real.sqrt_le_sqrt
        apply mul_le_mul (by linarith [hx.2]) (by linarith [hx.1]) (by positivity)
          (by linarith [hx.2])
      have hρx : C⁻¹ * Real.sqrt (a / 2 * (ℓ₀ / 2)) ≤ rho Λ x :=
        (mul_le_mul_of_nonneg_left hs (inv_pos.2 hC).le).trans h1
      simp only [hv, hf]
      exact div_le_div₀ (hρ0 x) hρx (pow_pos hd1 _) (pow_le_pow_left₀ hd1.le hd2 _)
    have hI : (a / 2) * v ≤ ∫ x, f x := by
      have e1 : ∫ x in (Ep - a)..(Ep - a / 2), v = (a / 2) * v := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring_nf
      have h2 := intervalIntegral.integral_mono_on (μ := volume) (by linarith)
        (continuous_const.intervalIntegrable _ _)
        (hfi.intervalIntegrable) hpt
      have h3 : ∫ x in (Ep - a)..(Ep - a / 2), f x ≤ ∫ x, f x := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_le_integral hfi (Eventually.of_forall hf0)
      linarith
    have hval : (a / 2) * v = C⁻¹ * Real.sqrt (β * ℓ₀ / 4) * (β / 2) / 2 ^ j *
        (Real.sqrt κ * κ / κ ^ j) := by
      have hs : Real.sqrt (a / 2 * (ℓ₀ / 2)) = Real.sqrt (β * ℓ₀ / 4) * Real.sqrt κ := by
        rw [← Real.sqrt_mul (by positivity)]; congr 1; rw [ha]; ring
      rw [hv, hs, mul_pow, ha]
      field_simp
    have hcmp : klo ≤ C⁻¹ * Real.sqrt (β * ℓ₀ / 4) * (β / 2) / 2 ^ j := by
      rw [hklo]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_right₀ (by norm_num) hj4
    rw [hmom, FcDet_rpow_eq hκ j]
    rw [FcDet_rpow_eq hκ j] at hκpow
    calc (max Kup klo⁻¹)⁻¹ * (Real.sqrt κ * κ / κ ^ j)
        ≤ klo * (Real.sqrt κ * κ / κ ^ j) := by
          apply mul_le_mul_of_nonneg_right _ hκpow.le
          rw [inv_le_comm₀ (lt_max_of_lt_left hKup0) hklo0]
          exact le_max_right _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hcmp hκpow.le
      _ = (a / 2) * v := hval.symm
      _ ≤ _ := hI
  · -- upper bound
    set r : ℝ := (1 / 2 : ℝ) - j with hr
    have hr1 : r + 1 = (3 / 2 : ℝ) - j := by rw [hr]; ring
    have hrne : r ≠ -1 := by rw [hr]; intro h; linarith
    have hpt : ∀ x ∈ Set.Icc Em Ep, f x ≤ C * Real.sqrt L₀ * (Ep + κ - x) ^ r := fun x hx => by
      have hd1 : 0 < Ep + κ - x := by linarith [hx.2]
      have h1 := (hsqΛ x hx).2
      have hs : Real.sqrt ((Ep - x) * (x - Em)) ≤ Real.sqrt L₀ * Real.sqrt (Ep + κ - x) := by
        rw [← Real.sqrt_mul (by linarith)]
        apply Real.sqrt_le_sqrt
        rw [mul_comm L₀]
        apply mul_le_mul (by linarith) (by linarith [hx.2, hLup, hL]) (by linarith [hx.1])
          hd1.le
      simp only [hf]
      calc rho Λ x / (Ep + κ - x) ^ j
          ≤ C * (Real.sqrt L₀ * Real.sqrt (Ep + κ - x)) / (Ep + κ - x) ^ j :=
            div_le_div_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left hs hC.le))
              (pow_nonneg hd1.le _)
        _ = C * Real.sqrt L₀ * (Real.sqrt (Ep + κ - x) / (Ep + κ - x) ^ j) := by ring
        _ = _ := by rw [FcDet_rpow_eq' hd1 j]
    have hcont : ContinuousOn (fun x => C * Real.sqrt L₀ * (Ep + κ - x) ^ r) (Set.uIcc Em Ep) := by
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl ?_
      rw [Set.uIcc_of_le hlt.le] at hx
      linarith [hx.2]
    have h1 : ∫ x, f x ≤ ∫ x in Em..Ep, C * Real.sqrt L₀ * (Ep + κ - x) ^ r := by
      rw [FcDet_int_eq_interval hlt.le (fun x hx => by simp [hf, hzero x hx])]
      exact intervalIntegral.integral_mono_on hlt.le hfi.intervalIntegrable
        (hcont.intervalIntegrable) hpt
    have h2 : ∫ x in Em..Ep, C * Real.sqrt L₀ * (Ep + κ - x) ^ r =
        C * Real.sqrt L₀ * (((Ep + κ - Em) ^ (r + 1) - κ ^ (r + 1)) / (r + 1)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun x => x ^ r) (Ep + κ),
        integral_rpow (Or.inr ⟨hrne, ?_⟩)]
      · congr 3; ring_nf
      · rw [Set.mem_uIcc]; push Not
        constructor <;> intro h <;> linarith
    have h3 : ((Ep + κ - Em) ^ (r + 1) - κ ^ (r + 1)) / (r + 1) ≤ 2 * κ ^ (r + 1) := by
      have hB : 0 < (Ep + κ - Em) ^ (r + 1) := Real.rpow_pos_of_pos (by linarith) _
      have hk : 0 < κ ^ (r + 1) := Real.rpow_pos_of_pos hκ _
      have hneg : r + 1 ≤ -(1 / 2) := by rw [hr1]; linarith
      rw [div_le_iff_of_neg (by linarith)]
      nlinarith
    rw [hmom, ← hr1]
    calc ∫ x, f x ≤ _ := h1
      _ = _ := h2
      _ ≤ C * Real.sqrt L₀ * (2 * κ ^ (r + 1)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Kup * κ ^ (r + 1) := by rw [hKup]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by rw [hr1]; exact hκpow.le)

section FcDetGamma

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `x ↦ m(x)` is continuous along the real axis. -/
private lemma FcDet_tendsto_real (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (x₀ : ℝ) : Tendsto (fun x : ℝ => mExt Λ x) (𝓝 x₀) (𝓝 (mExt Λ x₀)) := by
  have hcont := (mExt_boundary Λ hΛ hℓ).1
  have hg : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 x₀) (𝓝[{z : ℂ | 0 ≤ z.im}] (x₀ : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Complex.continuous_ofReal.tendsto x₀) (Eventually.of_forall fun x => by simp)
  exact (hcont _ (by simp)).tendsto.comp hg

omit [DecidableEq ι] in
private lemma FcDet_av_pos {f : ι → ℝ} (h : ∀ j, 0 < f j) : 0 < FcDet_av f := by
  unfold FcDet_av
  have : 0 < ∑ j, f j := Finset.sum_pos (fun j _ => h j) Finset.univ_nonempty
  positivity

/-- The edge data of `Λ = U diag(μ) U^*`: `m(E⁺) = a` is real and negative, `w₊ = E⁺ + a` lies
right of the spectrum, `a = -⟨(w₊ - μ)^{-1}⟩` and `⟨(w₊ - μ)^{-2}⟩ = 1` ((2.16) [self_m] and
(A.4) [equation_E_in_spectrum] at `E⁺`). -/
private lemma FcDet_edge (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (hdec : Λ = FcDet_cd U (fun j => (μ j : ℂ)))
    (hμ : ∀ j, |μ j| ≤ opNorm Λ) :
    ∃ a : ℝ, mExt Λ (Eplus Λ) = a ∧ a < 0 ∧ 9 / 10 ≤ Eplus Λ + a ∧
      a = -FcDet_G μ 1 (Eplus Λ + a) ∧ FcDet_G μ 2 (Eplus Λ + a) = 1 := by
  obtain ⟨hlt, hsupp⟩ := rho_support Λ hΛ hℓ
  set Ep := Eplus Λ with hEp
  set a := (mExt Λ Ep).re with ha
  have hρ : rho Λ Ep = 0 := by
    by_contra h
    have : Ep ∈ Set.Ioo (Eminus Λ) Ep := hsupp ▸ h
    exact lt_irrefl _ this.2
  have hm : mExt Λ Ep = a := by
    apply Complex.ext
    · simp [ha]
    · rw [FcDet_im_mExt Λ hΛ hℓ, hρ]; simp
  -- `a ≤ 0`, from the real Stieltjes integral right of `E⁺`
  have ha0 : a ≤ 0 := by
    have ht := (Complex.continuous_re.tendsto _).comp
      ((FcDet_tendsto_real Λ hΛ hℓ Ep).mono_left (nhdsWithin_le_nhds (s := Set.Ioi Ep)))
    refine le_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : x ∉ Set.Icc (Eminus Λ) Ep := fun h => by
      have : x ≤ Ep := h.2
      exact absurd hx (not_lt.2 this)
    simp only [Function.comp_apply]
    rw [FcDet_stieltjes_real Λ hΛ hℓ x hx', Complex.ofReal_re]
    refine integral_nonpos fun y => ?_
    by_cases hy : rho Λ y = 0
    · simp [hy]
    · have : y ∈ Set.Ioo (Eminus Λ) Ep := hsupp ▸ hy
      have hx2 : Ep < x := hx
      exact div_nonpos_of_nonneg_of_nonpos ((rho_stieltjes Λ hΛ hℓ).1 y) (by linarith [this.2])
  obtain ⟨hb1, hb2, hb3⟩ := (mExt_boundary Λ hΛ hℓ).2 Ep
  set w := Ep + a with hw
  have hwC : (Ep : ℂ) + mExt Λ Ep = (w : ℂ) := by rw [hm, hw]; push_cast; ring
  have hw9 : 9 / 10 ≤ |w| := by
    rw [hwC, Complex.norm_real, Real.norm_eq_abs] at hb1; linarith
  have hμ1 : ∀ j, |μ j| ≤ 1 / 10 := fun j => (hμ j).trans hℓ
  have hne : ∀ j, μ j ≠ w := fun j e => by
    have := hμ1 j; rw [e] at this; linarith
  have hG1 : a = -FcDet_G μ 1 w := by
    have h := hb2
    rw [MExt, hwC, hm, hdec, FcDet_ntr_res U μ hne] at h
    have h' : a = -FcDet_av (fun j => (w - μ j)⁻¹) := by exact_mod_cast h
    rw [h', FcDet_G]
    simp only [pow_one]
  have hwpos : 9 / 10 ≤ w := by
    rcases le_or_gt 0 w with h | h
    · rwa [abs_of_nonneg h] at hw9
    · exfalso
      rw [abs_of_neg h] at hw9
      have hneg : 0 < FcDet_G μ 1 w * -1 := by
        have : 0 < FcDet_av (fun j => -((w - μ j) ^ 1)⁻¹) := FcDet_av_pos fun j => by
          have := hμ1 j
          have h1 : w - μ j < 0 := by linarith [neg_abs_le (μ j)]
          rw [pow_one, neg_pos, inv_lt_zero]; exact h1
        unfold FcDet_av at this; unfold FcDet_G FcDet_av
        rw [Finset.sum_neg_distrib] at this; linarith
      linarith
  have hG2 : FcDet_G μ 2 w = 1 := by
    have h := equation_E_in_spectrum Λ hΛ hℓ Ep ⟨hlt.le, le_rfl⟩
    rw [MExt, hwC, hdec, FcDet_ntr_res_sq U μ hne] at h
    exact_mod_cast h
  have hapos : a < 0 := by
    have : 0 < FcDet_G μ 1 w := FcDet_av_pos fun j => by
      have := hμ1 j
      have : 0 < w - μ j := by linarith [le_abs_self (μ j)]
      positivity
    linarith
  exact ⟨a, hm, hapos, hwpos, hG1, hG2⟩

end FcDetGamma

section FcDetGamma2

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `γ₊ = ⟨(w₊ - μ)^{-3}⟩^{-1/3}` for `Λ = U diag(μ) U^*` ((2.6) [eq:def_gamma]): near `E⁺`,
`E - E⁺ = (ζ - w₊)^2 h(ζ)` with `ζ = E + m(E)` and `h(w₊) = ⟨(w₊ - μ)^{-3}⟩`, so
`Im m(E) / √(E⁺ - E) → ⟨(w₊ - μ)^{-3}⟩^{-1/2}`. -/
private lemma FcDet_gamma (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (U : Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (hdec : Λ = FcDet_cd U (fun j => (μ j : ℂ)))
    (hμ : ∀ j, |μ j| ≤ opNorm Λ) (a : ℝ) (hm : mExt Λ (Eplus Λ) = a)
    (hw9 : 9 / 10 ≤ Eplus Λ + a) (hG1 : a = -FcDet_G μ 1 (Eplus Λ + a))
    (hG2 : FcDet_G μ 2 (Eplus Λ + a) = 1) :
    gammaPlus Λ = FcDet_G μ 3 (Eplus Λ + a) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨hlt, hsupp⟩ := rho_support Λ hΛ hℓ
  set Ep := Eplus Λ with hEp
  set w := Ep + a with hw
  set n : ℂ := ((Fintype.card ι : ℂ))⁻¹ with hn
  have hμ1 : ∀ j, |μ j| ≤ 1 / 10 := fun j => (hμ j).trans hℓ
  have hμw : ∀ j, 0 < w - μ j := fun j => by linarith [le_abs_self (μ j), hμ1 j]
  set γ3 := FcDet_G μ 3 w with hγ3
  have hγ3p : 0 < γ3 := FcDet_av_pos fun j => by have := hμw j; positivity
  -- the function `h`
  set h : ℂ → ℂ := fun ζ => n * ∑ j, ((ζ - μ j) * ((w : ℂ) - μ j) ^ 2)⁻¹ with hh
  have hwμ : ∀ j, (w : ℂ) - μ j ≠ 0 := fun j => by
    have := hμw j; intro e; have : w - μ j = 0 := by exact_mod_cast e
    linarith
  have hhw : h w = (γ3 : ℂ) := by
    simp only [hh, hγ3, FcDet_G, FcDet_av, hn]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- `ζ(E) = E + m(E)` and its limit `w`
  set ζ : ℝ → ℂ := fun E => (E : ℂ) + mExt Λ E with hζ
  have hζlim : Tendsto ζ (𝓝[<] Ep) (𝓝 (w : ℂ)) := by
    have := ((Complex.continuous_ofReal.tendsto Ep).add (FcDet_tendsto_real Λ hΛ hℓ Ep)).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio Ep))
    rw [hm] at this
    convert this using 2
    rw [hw]; push_cast; ring
  have hhlim : Tendsto (fun E => h (ζ E)) (𝓝[<] Ep) (𝓝 (γ3 : ℂ)) := by
    rw [← hhw]
    simp only [hh]
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => ?_)
    exact Tendsto.inv₀ ((hζlim.sub_const _).mul_const _)
      (mul_ne_zero (hwμ j) (pow_ne_zero _ (hwμ j)))
  -- the identity `E - E⁺ = (ζ - w)^2 h(ζ)` in the bulk
  have hbulk : ∀ E ∈ Set.Ioo (Eminus Λ) Ep, ((E - Ep : ℝ) : ℂ) = (ζ E - w) ^ 2 * h (ζ E) := by
    intro E hE
    obtain ⟨hb1, hb2, -⟩ := (mExt_boundary Λ hΛ hℓ).2 E
    have hz9 : 9 / 10 ≤ ‖ζ E‖ := by simp only [hζ]; linarith
    have hne : ∀ j, (μ j : ℂ) ≠ ζ E := fun j e => by
      rw [← e, Complex.norm_real, Real.norm_eq_abs] at hz9; linarith [hμ1 j]
    have hne' : ∀ j, ζ E - μ j ≠ 0 := fun j e => hne j (by linear_combination -e)
    have hmE : mExt Λ E = -(n * ∑ j, (ζ E - μ j)⁻¹) := by
      rw [hb2, MExt]
      change ntr ((Λ - ζ E • (1 : Matrix ι ι ℂ))⁻¹) = _
      rw [hdec, FcDet_res U μ hne, FcDet_ntr_cd, ← mul_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← inv_neg, neg_sub]
    have haC : (a : ℂ) = -(n * ∑ j, ((w : ℂ) - μ j)⁻¹) := by
      rw [hG1, FcDet_G, FcDet_av, hn]; push_cast; simp only [pow_one]
    have h2C : n * ∑ j, (((w : ℂ) - μ j) ^ 2)⁻¹ = 1 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hG2
      simp only [FcDet_G, FcDet_av] at this
      push_cast at this
      rw [hn]; exact this
    have hterm : ∀ j, (ζ E - w) * (((w : ℂ) - μ j) ^ 2)⁻¹ + ((ζ E - μ j)⁻¹ - ((w : ℂ) - μ j)⁻¹) =
        (ζ E - w) ^ 2 * ((ζ E - μ j) * ((w : ℂ) - μ j) ^ 2)⁻¹ := fun j => by
      field_simp [hne' j, hwμ j]
      ring
    have hsum := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hterm j)
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      at hsum
    have hζE : ζ E = (E : ℂ) + mExt Λ E := rfl
    have hwC : (w : ℂ) = (Ep : ℂ) + (a : ℂ) := by rw [hw]; push_cast; ring
    simp only [hh]
    push_cast
    linear_combination n * hsum - (ζ E - w) * h2C - hmE + haC - hζE + hwC
  -- `q(E) = (ζ(E) - w)/√(E⁺ - E)` satisfies `q^2 h(ζ) = -1`
  set q : ℝ → ℂ := fun E => (ζ E - w) / (Real.sqrt (Ep - E) : ℂ) with hq
  have hev : ∀ᶠ E in 𝓝[<] Ep, E ∈ Set.Ioo (Eminus Λ) Ep := Ioo_mem_nhdsLT hlt
  have hq2 : ∀ E ∈ Set.Ioo (Eminus Λ) Ep, q E ^ 2 * h (ζ E) = -1 := by
    intro E hE
    have hs : 0 < Ep - E := by linarith [hE.2]
    have hsq : ((Real.sqrt (Ep - E) : ℂ)) ^ 2 = ((Ep - E : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]
    have hs0 : ((Real.sqrt (Ep - E) : ℂ)) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hs).ne'
    have hs0' : ((Ep - E : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact hs.ne'
    simp only [hq]
    rw [div_pow, hsq, div_mul_eq_mul_div, ← hbulk E hE, div_eq_iff hs0']
    push_cast; ring
  set σ : ℝ := (Real.sqrt γ3)⁻¹ with hσ
  have hσp : 0 < σ := inv_pos.2 (Real.sqrt_pos.2 hγ3p)
  have hiσ : (Complex.I * σ) ^ 2 = -1 / (γ3 : ℂ) := by
    have : (σ : ℂ) ^ 2 = 1 / (γ3 : ℂ) := by
      rw [hσ, ← Complex.ofReal_pow, inv_pow, Real.sq_sqrt hγ3p.le]; push_cast; ring
    rw [mul_pow, Complex.I_sq, this]; ring
  have hq2lim : Tendsto (fun E => q E ^ 2) (𝓝[<] Ep) (𝓝 ((Complex.I * σ) ^ 2)) := by
    rw [hiσ]
    have hγ0 : (γ3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hγ3p.ne'
    refine (tendsto_const_nhds.div hhlim hγ0).congr' ?_
    filter_upwards [hev] with E hE
    have h1 := hq2 E hE
    have h0 : h (ζ E) ≠ 0 := fun e => by rw [e, mul_zero] at h1; norm_num at h1
    change (-1 : ℂ) / h (ζ E) = q E ^ 2
    rw [div_eq_iff h0]; exact h1.symm
  -- `Im q ≥ 0`, hence `q → iσ`
  have hqim : ∀ E ∈ Set.Ioo (Eminus Λ) Ep, (q E).im = Real.pi * rho Λ E / Real.sqrt (Ep - E) := by
    intro E hE
    simp only [hq, hζ]
    rw [Complex.div_ofReal_im]
    simp [FcDet_im_mExt Λ hΛ hℓ]
  have hqbd : ∀ E ∈ Set.Ioo (Eminus Λ) Ep,
      ‖q E - Complex.I * σ‖ ≤ ‖q E ^ 2 - (Complex.I * σ) ^ 2‖ / σ := by
    intro E hE
    have him : 0 ≤ (q E).im := by
      rw [hqim E hE]
      exact div_nonneg (mul_nonneg Real.pi_pos.le ((rho_stieltjes Λ hΛ hℓ).1 E))
        (Real.sqrt_nonneg _)
    have hplus : σ ≤ ‖q E + Complex.I * σ‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, one_mul, zero_add]
      rw [abs_of_nonneg (by linarith)]; linarith
    rw [le_div_iff₀ hσp, show q E ^ 2 - (Complex.I * σ) ^ 2 =
      (q E - Complex.I * σ) * (q E + Complex.I * σ) by ring, norm_mul]
    exact mul_le_mul_of_nonneg_left hplus (norm_nonneg _)
  have hqlim : Tendsto q (𝓝[<] Ep) (𝓝 (Complex.I * σ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun E => ‖q E ^ 2 - (Complex.I * σ) ^ 2‖ / σ) (𝓝[<] Ep) (𝓝 0) := by
      have := ((hq2lim.sub_const ((Complex.I * σ) ^ 2)).norm).div_const σ
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun E => norm_nonneg _) ?_ h0
    filter_upwards [hev] with E hE using hqbd E hE
  have hρlim : Tendsto (fun E => rho Λ E / Real.sqrt (Ep - E)) (𝓝[<] Ep) (𝓝 (σ / Real.pi)) := by
    have := ((Complex.continuous_im.tendsto _).comp hqlim).div_const Real.pi
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, zero_add] at this
    refine this.congr' ?_
    filter_upwards [hev] with E hE
    simp only [Function.comp_apply]
    rw [hqim E hE]
    field_simp
  have hgl := (def_gamma_limits Λ hΛ hℓ).1
  have hγp : 0 < gammaPlus Λ := lt_of_lt_of_le (by norm_num) (def_gamma_limits Λ hΛ hℓ).2.2.1
  have heq : gammaPlus Λ ^ (3 / 2 : ℝ) = σ := by
    have := tendsto_nhds_unique hgl hρlim
    field_simp at this
    linarith
  have e1 : gammaPlus Λ = (gammaPlus Λ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_mul hγp.le]; norm_num
  rw [e1, heq, hσ, Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hγ3p.le,
    ← Real.rpow_mul hγ3p.le]
  norm_num

end FcDetGamma2

section FcDetScale

variable {ι : Type*} [Fintype ι]

/-- `G_k` of the eigenvalues `cν` at `cu` is `c^{-k} G_k(u)`. -/
private lemma FcDet_G_smul (ν : ι → ℝ) (k : ℕ) (c : ℝ) (u : ℝ) :
    FcDet_G (fun j => c * ν j) k (c * u) = (c ^ k)⁻¹ * FcDet_G ν k u := by
  unfold FcDet_G FcDet_av
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_sub, mul_pow, mul_inv]
  ring

end FcDetScale

section FcDetSrel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- `ntr (Λ - w)⁻¹ = -⟨(w - ν)⁻¹⟩` for `Λ = U diag(ν) U^*` at a real point `w` off the
spectrum. -/
private lemma FcDet_ntr_res' {Λ : Matrix ι ι ℂ} (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ)
    (hdec : Λ = FcDet_cd U (fun j => (ν j : ℂ))) {w : ℝ} (h : ∀ j, ν j ≠ w) :
    ntr (Λ - (w : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ = ((-FcDet_av (fun j => (w - ν j)⁻¹) : ℝ) : ℂ) := by
  subst hdec
  exact FcDet_ntr_res U ν h

/-- Right of `E⁺`, `m(x) = -S_1(x)` for the moments `S_j` of `ρ_N`. -/
private lemma FcDet_mS (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (x : ℝ) (hx : Eplus Λ < x) : mExt Λ x = ((-FcDet_S (rho Λ) 1 x : ℝ) : ℂ) := by
  have hx' : x ∉ Set.Icc (Eminus Λ) (Eplus Λ) := fun h => by linarith [h.2]
  rw [FcDet_stieltjes_real Λ hΛ hℓ x hx', FcDet_S, ← integral_neg]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [pow_one, ← div_neg_eq_neg_div, neg_sub]

/-- Right of `E⁺`, `S_1(x) = ⟨(u - ν)^{-1}⟩` at `u = x - S_1(x)` ((2.16) [self_m] for
`Λ = U diag(ν) U^*` on the real axis). -/
private lemma FcDet_rel (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (hdec : Λ = FcDet_cd U (fun j => (ν j : ℂ)))
    (hν1 : ∀ j, |ν j| ≤ 1 / 10) (x : ℝ) (hx : Eplus Λ < x) :
    (∀ j, x - FcDet_S (rho Λ) 1 x - ν j ≠ 0) ∧
      FcDet_S (rho Λ) 1 x = FcDet_G ν 1 (x - FcDet_S (rho Λ) 1 x) := by
  obtain ⟨hb1, hb2, -⟩ := (mExt_boundary Λ hΛ hℓ).2 x
  set u := x - FcDet_S (rho Λ) 1 x with hu_def
  have hu : (x : ℂ) + mExt Λ x = (u : ℂ) := by
    rw [FcDet_mS Λ hΛ hℓ x hx, hu_def]; push_cast; ring
  rw [hu, Complex.norm_real, Real.norm_eq_abs] at hb1
  have hne : ∀ j, ν j ≠ u := fun j e => by
    have h1 := hν1 j
    rw [e] at h1
    have h2 : 9 / 10 ≤ |u| := by linarith
    linarith
  refine ⟨fun j => sub_ne_zero.2 (hne j).symm, ?_⟩
  rw [MExt, hu, FcDet_ntr_res' U ν hdec hne, FcDet_mS Λ hΛ hℓ x hx] at hb2
  have h' : -FcDet_S (rho Λ) 1 x = -FcDet_av (fun j => (u - ν j)⁻¹) := by
    exact_mod_cast hb2
  rw [FcDet_G]
  simp only [pow_one]
  linarith

/-- Right of `E⁺`, with `u = x - S_1(x)`: `S_2 = G_2(u)(1 + S_2)` and
`S_3 = G_3(u)(1 + S_2)^2 + G_2(u) S_3` (the first two derivatives of `S_1 = G_1(u)`). -/
private lemma FcDet_Srel (Λ : Matrix ι ι ℂ) (hΛ : Λ.IsHermitian) (hℓ : opNorm Λ ≤ 1 / 10)
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (hdec : Λ = FcDet_cd U (fun j => (ν j : ℂ)))
    (hν1 : ∀ j, |ν j| ≤ 1 / 10) (x₀ : ℝ) (hx₀ : Eplus Λ < x₀) :
    FcDet_S (rho Λ) 1 x₀ = FcDet_G ν 1 (x₀ - FcDet_S (rho Λ) 1 x₀) ∧
      FcDet_S (rho Λ) 2 x₀ =
        FcDet_G ν 2 (x₀ - FcDet_S (rho Λ) 1 x₀) * (1 + FcDet_S (rho Λ) 2 x₀) ∧
      -2 * FcDet_S (rho Λ) 3 x₀ =
        -2 * FcDet_G ν 3 (x₀ - FcDet_S (rho Λ) 1 x₀) * (1 + FcDet_S (rho Λ) 2 x₀) ^ 2 +
          FcDet_G ν 2 (x₀ - FcDet_S (rho Λ) 1 x₀) * (-2 * FcDet_S (rho Λ) 3 x₀) := by
  obtain ⟨hlt, hsupp⟩ := rho_support Λ hΛ hℓ
  obtain ⟨hρ0, hρc, hρi, -, -⟩ := rho_stieltjes Λ hΛ hℓ
  have hsuppE : ∀ y, rho Λ y ≠ 0 → y < Eplus Λ := fun y hy =>
    (show y ∈ Set.Ioo (Eminus Λ) (Eplus Λ) from hsupp ▸ hy).2
  set S : ℕ → ℝ → ℝ := fun j => FcDet_S (rho Λ) j with hS
  have hrel := FcDet_rel Λ hΛ hℓ U ν hdec hν1
  have hS1d : ∀ x, Eplus Λ < x → HasDerivAt (S 1) (-S 2 x) x := fun x hx => by
    have h := FcDet_S_deriv hρ0 hρc hρi hsuppE hx 0
    simp only [Nat.cast_zero, zero_add, neg_mul, one_mul] at h
    exact h
  have hud : ∀ x, Eplus Λ < x → HasDerivAt (fun x => x - S 1 x) (1 + S 2 x) x := fun x hx => by
    have h := (hasDerivAt_id' x).sub (hS1d x hx)
    rw [sub_neg_eq_add] at h
    exact h
  have hid1 : ∀ x, Eplus Λ < x → S 2 x = FcDet_G ν 2 (x - S 1 x) * (1 + S 2 x) := by
    intro x hx
    have hcomp := (FcDet_G_deriv ν 0 (hrel x hx).1).comp x (hud x hx)
    have heq : S 1 =ᶠ[𝓝 x] (FcDet_G ν (0 + 1) ∘ fun x => x - S 1 x) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact (hrel y hy).2
    have := (hS1d x hx).unique (hcomp.congr_of_eventuallyEq heq)
    simp only [Nat.cast_zero, zero_add, neg_mul, one_mul, neg_inj] at this
    exact this
  have hS2d : HasDerivAt (S 2) (-2 * S 3 x₀) x₀ := by
    have h := FcDet_S_deriv hρ0 hρc hρi hsuppE hx₀ 1
    norm_num at h
    rw [neg_mul]
    exact h
  refine ⟨(hrel x₀ hx₀).2, hid1 x₀ hx₀, ?_⟩
  have hcomp := (FcDet_G_deriv ν 1 (hrel x₀ hx₀).1).comp x₀ (hud x₀ hx₀)
  have hprod := hcomp.mul ((hasDerivAt_const x₀ (1 : ℝ)).add hS2d)
  have heq : S 2 =ᶠ[𝓝 x₀]
      fun x => (FcDet_G ν (1 + 1) ∘ fun x => x - S 1 x) x * (1 + S 2 x) := by
    filter_upwards [Ioi_mem_nhds hx₀] with y hy
    exact hid1 y hy
  have := hS2d.unique (hprod.congr_of_eventuallyEq heq)
  norm_num at this
  linear_combination this

end FcDetSrel

/-- The free-convolution data of the deterministic density `ρ_V(x) = c ρ_{cΛ}(cx)` are `E⁺` and
`γ₊` of `Λ` (proof of Lemma 4.1 [CVtG], after [CorrelatedBandAOP, Section 6.1]): with
`t' = 1 - c^{-2}` there is `ξ > c⁻¹ E⁺(cΛ)` with `t' ∫ ρ_V(x)(ξ - x)^{-2} dx = 1`,
`E⁺(Λ) = ξ + t' ∫ ρ_V(x)(ξ - x)^{-1} dx` and `γ₊(Λ) = t'^{-1} (∫ ρ_V(x)(ξ - x)^{-3} dx)^{-1/3}`. -/
theorem fcDet_eq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (Λ : Matrix ι ι ℂ)
    (hΛ : Λ.IsHermitian) (c : ℝ) (hc : 1 < c) (hc2 : c ≤ 2)
    (hcΛ : opNorm ((c : ℂ) • Λ) ≤ 1 / 10) :
    ∃ ξ : ℝ, c⁻¹ * Eplus ((c : ℂ) • Λ) < ξ ∧
      (1 - c⁻¹ ^ 2) * rhoMom ((c : ℂ) • Λ) c 2 ξ = 1 ∧
      Eplus Λ = ξ + (1 - c⁻¹ ^ 2) * rhoMom ((c : ℂ) • Λ) c 1 ξ ∧
      gammaPlus Λ = (1 - c⁻¹ ^ 2)⁻¹ * rhoMom ((c : ℂ) • Λ) c 3 ξ ^ (-(1 / 3 : ℝ)) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc0.ne'
  set t : ℝ := 1 - c⁻¹ ^ 2 with ht
  have hs : c⁻¹ ^ 2 < 1 := by
    have h1 : c⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
    have h2 : 0 < c⁻¹ := inv_pos.2 hc0
    nlinarith
  have ht0 : 0 < t := by rw [ht]; linarith
  set Λ' : Matrix ι ι ℂ := (c : ℂ) • Λ with hΛ'
  have hΛ'h : Λ'.IsHermitian := hΛ.smul (by simp [IsSelfAdjoint])
  have hnorm : opNorm Λ' = c * opNorm Λ := by
    simp only [hΛ', opNorm]
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  have hℓ : opNorm Λ ≤ 1 / 10 := by
    have h0 : 0 ≤ opNorm Λ := norm_nonneg _
    nlinarith
  obtain ⟨U, μ, hdec, hμ⟩ := FcDet_decomp hΛ
  set ν : ι → ℝ := fun j => c * μ j with hν
  have hdec' : Λ' = FcDet_cd U (fun j => (ν j : ℂ)) := by
    rw [hΛ', hdec, FcDet_cd_real_smul]
  have hν1 : ∀ j, |ν j| ≤ 1 / 10 := fun j => by
    simp only [hν]
    rw [abs_mul, abs_of_pos hc0]
    have := mul_le_mul_of_nonneg_left (hμ j) hc0.le
    linarith
  obtain ⟨a, hm, ha, hw9, hG1, hG2⟩ := FcDet_edge Λ hΛ hℓ U μ hdec hμ
  have hγ := FcDet_gamma Λ hΛ hℓ U μ hdec hμ a hm hw9 hG1 hG2
  set Ep := Eplus Λ with hEp
  set w := Ep + a with hw
  set ξ := Ep + t * a with hξ
  -- the boundary subordination at `E⁺`: `a = c m_{cΛ}(cξ)`
  have hF1 : (a : ℂ) = (c : ℂ) * mExt Λ' ((c * ξ : ℝ) : ℂ) := by
    have hlimL := FcDet_tendsto_bd Λ hΛ hℓ Ep
    rw [hm] at hlimL
    set p : ℝ → ℂ := fun η => (c : ℂ) * ((Ep : ℂ) + (η : ℂ) * Complex.I + ((t : ℝ) : ℂ) *
      mSol Λ ((Ep : ℂ) + (η : ℂ) * Complex.I)) with hp
    have hp1 : Tendsto p (𝓝[>] 0) (𝓝 ((c * ξ : ℝ) : ℂ)) := by
      have hη : Tendsto (fun η : ℝ => (Ep : ℂ) + (η : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (Ep : ℂ)) := by
        have : Continuous fun η : ℝ => (Ep : ℂ) + (η : ℂ) * Complex.I := by fun_prop
        have h0 := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        simpa using h0
      have := (hη.add (hlimL.const_mul ((t : ℝ) : ℂ))).const_mul (c : ℂ)
      convert this using 2
      rw [hξ]; push_cast; ring
    have hpim : ∀ η : ℝ, 0 < η → 0 < (p η).im := fun η hη => by
      have h1 := (mSol_spec Λ hΛ ((Ep : ℂ) + (η : ℂ) * Complex.I) (by simpa using hη)).1
      have e : (p η).im = c * (η + t * (mSol Λ ((Ep : ℂ) + (η : ℂ) * Complex.I)).im) := by
        simp only [hp, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
          Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
        ring
      rw [e]
      have := mul_pos ht0 h1
      positivity
    have hpS : Tendsto p (𝓝[>] 0) (𝓝[{z : ℂ | 0 ≤ z.im}] ((c * ξ : ℝ) : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hp1
        (by filter_upwards [self_mem_nhdsWithin] with η hη using (hpim η hη).le)
    have hR := (((mExt_boundary Λ' hΛ'h hcΛ).1 _ (by simp)).tendsto.comp hpS).const_mul (c : ℂ)
    have hL' : Tendsto (fun η : ℝ => mSol Λ ((Ep : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] 0)
        (𝓝 ((c : ℂ) * mExt Λ' ((c * ξ : ℝ) : ℂ))) := by
      refine hR.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with η hη
      have him := hpim η hη
      simp only [Function.comp_apply, mExt, him, ↓reduceIte]
      rw [mSol_subord Λ hΛ c hc.le _ (by simpa using hη)]
    exact tendsto_nhds_unique hlimL hL'
  have hm2 : mExt Λ' ((c * ξ : ℝ) : ℂ) = ((a / c : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, eq_div_iff hcC, mul_comm]
    exact hF1.symm
  have hcwC : ((c * ξ : ℝ) : ℂ) + mExt Λ' ((c * ξ : ℝ) : ℂ) = ((c * w : ℝ) : ℂ) := by
    rw [hm2, hw, hξ, ht]; push_cast; field_simp; ring
  have hcw9 : 9 / 10 ≤ c * w := by nlinarith
  have hνcw : ∀ j, ν j ≠ c * w := fun j e => by have := hν1 j; rw [e] at this
                                              ; rw [abs_of_pos (by linarith)] at this; linarith
  have hGs2 : FcDet_G ν 2 (c * w) = c⁻¹ ^ 2 := by
    rw [hν, FcDet_G_smul μ 2 c, hG2, inv_pow, mul_one]
  -- `cξ` lies right of the support of `ρ_{cΛ}`
  obtain ⟨hlt2, hsupp2⟩ := rho_support Λ' hΛ'h hcΛ
  set E2 := Eplus Λ' with hE2
  have hcξ : E2 < c * ξ := by
    by_contra hle
    push Not at hle
    by_cases hlo : Eminus Λ' ≤ c * ξ
    · have h := equation_E_in_spectrum Λ' hΛ'h hcΛ (c * ξ) ⟨hlo, hle⟩
      rw [MExt, hcwC, hdec', FcDet_ntr_res_sq U ν hνcw] at h
      have h' : FcDet_G ν 2 (c * w) = 1 := by exact_mod_cast h
      rw [hGs2] at h'
      linarith
    · push Not at hlo
      have hx : c * ξ ∉ Set.Icc (Eminus Λ') E2 := fun h => by linarith [h.1]
      have h := FcDet_stieltjes_real Λ' hΛ'h hcΛ (c * ξ) hx
      rw [hm2] at h
      have h' : a / c = ∫ y, rho Λ' y / (y - c * ξ) := by exact_mod_cast h
      have hnn : 0 ≤ ∫ y, rho Λ' y / (y - c * ξ) := by
        refine integral_nonneg fun y => ?_
        by_cases hy : rho Λ' y = 0
        · simp [hy]
        · have : y ∈ Set.Ioo (Eminus Λ') E2 := hsupp2 ▸ hy
          exact div_nonneg ((rho_stieltjes Λ' hΛ'h hcΛ).1 y) (by linarith [this.1])
      have : a / c < 0 := div_neg_of_neg_of_pos ha hc0
      linarith
  -- the moments `S_j` of `ρ_{cΛ}` at `x₀ = cξ`
  set x₀ := c * ξ with hx₀
  obtain ⟨-, h1, hid2⟩ := FcDet_Srel Λ' hΛ'h hcΛ U ν hdec' hν1 x₀ hcξ
  have hmS₀ := FcDet_mS Λ' hΛ'h hcΛ x₀ hcξ
  -- the values at `x₀ = cξ`
  have hS1₀ : FcDet_S (rho Λ') 1 x₀ = -(a / c) := by
    have h := hmS₀.symm.trans hm2
    have : -FcDet_S (rho Λ') 1 x₀ = a / c := by exact_mod_cast h
    linarith
  have hu₀ : x₀ - FcDet_S (rho Λ') 1 x₀ = c * w := by
    rw [hS1₀, hx₀, hξ, hw, ht]; field_simp; ring
  set γ3 := FcDet_G μ 3 w with hγ3
  have hγ3p : 0 < γ3 := FcDet_av_pos fun j => by
    have h1 := hμ j
    have : 0 < w - μ j := by linarith [le_abs_self (μ j)]
    positivity
  have hGs3 : FcDet_G ν 3 (c * w) = (c ^ 3)⁻¹ * γ3 := by
    rw [hν, FcDet_G_smul μ 3 c]
  rw [hu₀, hGs2] at h1
  rw [hu₀, hGs2, hGs3] at hid2
  have hS2v : FcDet_S (rho Λ') 2 x₀ = c⁻¹ ^ 2 / t := by
    rw [eq_div_iff ht0.ne', ht]; linear_combination h1
  have h1S2 : 1 + FcDet_S (rho Λ') 2 x₀ = 1 / t := by
    rw [hS2v, eq_div_iff ht0.ne', add_mul, div_mul_cancel₀ _ ht0.ne', ht]; ring
  rw [h1S2] at hid2
  have hS3v : FcDet_S (rho Λ') 3 x₀ = (c ^ 3)⁻¹ * γ3 / t ^ 3 := by
    have h3 : FcDet_S (rho Λ') 3 x₀ * t = (c ^ 3)⁻¹ * γ3 * (1 / t) ^ 2 := by
      rw [ht] at hid2 ⊢; linear_combination (-1 / 2 : ℝ) * hid2
    rw [eq_div_iff (pow_ne_zero 3 ht0.ne'),
      show FcDet_S (rho Λ') 3 x₀ * t ^ 3 = (FcDet_S (rho Λ') 3 x₀ * t) * t ^ 2 by ring, h3]
    field_simp
  refine ⟨ξ, ?_, ?_, ?_, ?_⟩
  · rw [inv_mul_lt_iff₀ hc0]; exact hcξ
  · rw [FcDet_rhoMom_eq Λ' hc0 2 ξ, ← hx₀, hS2v]
    field_simp
  · rw [FcDet_rhoMom_eq Λ' hc0 1 ξ, ← hx₀, hS1₀, hξ]
    field_simp
    ring
  · rw [FcDet_rhoMom_eq Λ' hc0 3 ξ, ← hx₀, hS3v, hγ]
    have e1 : c ^ 3 * ((c ^ 3)⁻¹ * γ3 / t ^ 3) = γ3 / t ^ 3 := by field_simp
    rw [e1, Real.div_rpow hγ3p.le (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul ht0.le]
    norm_num
    rw [Real.rpow_neg_one]
    field_simp

end RBMTransitionEdge

end
