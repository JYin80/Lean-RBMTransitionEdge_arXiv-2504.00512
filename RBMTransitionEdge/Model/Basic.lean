module

public import RBMTransitionEdge.MainDefs
public import Mathlib

@[expose] public section

/-!
# The block random matrix model

The model `H_Λ = H + Λ` of (1.2) [eq:def_model] and (1.3) [matrix_H] under Assumption 1
[main_assm], its ordered eigenvalues and unit eigenvectors, the operator and Hilbert–Schmidt
norms, the index function `𝔯(k)` of (1.4) [eq:rk], the GUE of Theorem 2.2 [MixEV], and the
`n`-point correlation pairing of Theorem 2.5 [theorem_localized_eigenvalue].
-/

open MeasureTheory ProbabilityTheory Matrix

noncomputable section
open Classical

namespace RBMTransitionEdge

/-- The standard complex Gaussian law, `E|z|² = 1` and `E z² = 0`. -/
def cGauss : ProbabilityMeasure ℂ :=
  ProbabilityMeasure.map
    (⟨(gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)), inferInstance⟩ :
      ProbabilityMeasure (ℝ × ℝ)) fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

/-- The coordinate law of the GUE of size `Mc` used in Theorem 2.2 [MixEV]: through `wig Mc`,
`E|W_{ij}|² = 1/Mc` off the diagonal and real diagonal entries of variance `1/Mc`, the
normalization of (4.1) [defVt] and (4.3) [eq:eq_in_law_H]. -/
def gueLaw (Mc : ℕ) : Measure (Coords Mc) :=
  (Measure.pi fun _ : Fin Mc => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin Mc => Measure.pi fun _ : Fin Mc => (cGauss : Measure ℂ))

/-- `blockLaw D N L` is a probability measure. -/
theorem blockLaw_isProbabilityMeasure (D N : ℕ) {C : ℕ → ℝ} (L : EntryLaws C) :
    IsProbabilityMeasure (blockLaw D N L) := by
  unfold blockLaw coordLaw
  infer_instance

/-- `gueLaw Mc` is a probability measure. -/
theorem gueLaw_isProbabilityMeasure (Mc : ℕ) : IsProbabilityMeasure (gueLaw Mc) := by
  unfold gueLaw
  infer_instance

/-- The Wigner matrix `wig n w` is Hermitian. -/
private lemma Basic_wig_isHermitian (n : ℕ) (w : Coords n) : (wig n w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [wig, star_mul', Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.not_gt, h.ne']
  · subst h
    simp
  · simp [h, h.ne, h.not_gt, h.ne']

/-- The interaction `lam D N A` is Hermitian, for every `A`. -/
private lemma Basic_lam_isHermitian (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (lam D N A).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  simp only [lam, star_add]
  split_ifs <;> simp [add_comm]

/-- The block-diagonal matrix `blockH D N w` is Hermitian. -/
private lemma Basic_blockH_isHermitian (D N : ℕ) (w : Fin D → Coords N) :
    (blockH D N w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  by_cases h : p.1 = q.1
  · simp only [blockH, h, ↓reduceIte]
    exact (Basic_wig_isHermitian N (w q.1)).apply p.2 q.2
  · have h' : ¬ q.1 = p.1 := fun e => h e.symm
    simp [blockH, h, h']

/-- `H_Λ` of (1.2) [eq:def_model] is Hermitian. -/
theorem HLam_isHermitian (D N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin D → Coords N) :
    (HLam D N A w).IsHermitian := by
  unfold HLam
  exact (Basic_blockH_isHermitian D N w).add (Basic_lam_isHermitian D N A)

/-- The operator norm of a scalar matrix `c I_n`, `n ≥ 1`, is `|c|`. -/
theorem opNorm_smul_one (n : ℕ) (hn : 1 ≤ n) (c : ℂ) :
    opNorm (c • (1 : Matrix (Fin n) (Fin n) ℂ)) = ‖c‖ := by
  unfold opNorm
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [map_smul, map_one, norm_smul, norm_one, mul_one]

/-- The Hilbert–Schmidt norm of a scalar matrix `c I_n` is `|c| √n`. -/
theorem hsNorm_smul_one (n : ℕ) (c : ℂ) :
    hsNorm (c • (1 : Matrix (Fin n) (Fin n) ℂ)) = ‖c‖ * Real.sqrt n := by
  unfold hsNorm
  have h : ∀ i j : Fin n, ‖(c • (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ^ 2 =
      if i = j then ‖c‖ ^ 2 else 0 := by
    intro i j
    by_cases hij : i = j <;> simp [hij]
  have : ∀ i : Fin n, ∑ j : Fin n, ‖(c • (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ^ 2 = ‖c‖ ^ 2 := by
    intro i
    rw [Finset.sum_congr rfl fun j _ => h i j]
    simp
  simp only [this]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_comm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_comm]

/-- `𝔯(1) = 1` of (1.4) [eq:rk] when `DN ≥ 1`. -/
theorem rk_one (D N : ℕ) (h : 1 ≤ D * N) : rk D N 1 = 1 := by
  have : min 1 (D * N + 1 - 1) = 1 := by omega
  unfold rk
  rw [this]
  simp

/-- The Rademacher law `(δ₁ + δ₋₁)/2` on `ℝ`. -/
private def Basic_rademacher : Measure ℝ :=
  (2 : ENNReal)⁻¹ • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ))

private instance : IsProbabilityMeasure Basic_rademacher :=
  ⟨by simp [Basic_rademacher, ENNReal.inv_two_add_inv_two]⟩

/-- Every function is integrable against the Rademacher law. -/
private lemma Basic_rademacher_integrable {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) :
    Integrable f Basic_rademacher := by
  unfold Basic_rademacher
  exact ((integrable_dirac enorm_lt_top).add_measure
    (integrable_dirac enorm_lt_top)).smul_measure (by simp)

/-- The integral against the Rademacher law is the average over `±1`. -/
private lemma Basic_rademacher_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) :
    ∫ x, f x ∂Basic_rademacher = (1 / 2 : ℝ) • (f 1 + f (-1)) := by
  unfold Basic_rademacher
  rw [integral_smul_measure, integral_add_measure (integrable_dirac enorm_lt_top)
    (integrable_dirac enorm_lt_top)]
  simp [integral_dirac]

/-- The uniform law on `{1, i, -1, -i}`. -/
private def Basic_fourth : Measure ℂ :=
  (4 : ENNReal)⁻¹ • (Measure.dirac (1 : ℂ) + Measure.dirac Complex.I + Measure.dirac (-1 : ℂ) +
    Measure.dirac (-Complex.I))

private instance : IsProbabilityMeasure Basic_fourth :=
  ⟨by
    simp only [Basic_fourth, Measure.coe_smul, Measure.coe_add, Pi.smul_apply, Pi.add_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul]
    have h4 : (1 + 1 + 1 + 1 : ENNReal) = 4 := by norm_num
    rw [h4]
    exact ENNReal.inv_mul_cancel (by norm_num) (by simp)⟩

/-- Every function is integrable against the uniform law on `{1, i, -1, -i}`. -/
private lemma Basic_fourth_integrable {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) :
    Integrable f Basic_fourth := by
  have h1 : ∀ a, Integrable f (Measure.dirac a) := fun a => integrable_dirac enorm_lt_top
  unfold Basic_fourth
  exact ((((h1 _).add_measure (h1 _)).add_measure (h1 _)).add_measure (h1 _)).smul_measure
    (by simp)

/-- The integral against the uniform law on `{1, i, -1, -i}` is the average over the four points. -/
private lemma Basic_fourth_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℂ → E) :
    ∫ x, f x ∂Basic_fourth = (1 / 4 : ℝ) • (f 1 + f Complex.I + f (-1) + f (-Complex.I)) := by
  have h1 : ∀ a, Integrable f (Measure.dirac a) := fun a => integrable_dirac enorm_lt_top
  unfold Basic_fourth
  rw [integral_smul_measure,
    integral_add_measure (((h1 _).add_measure (h1 _)).add_measure (h1 _)) (h1 _),
    integral_add_measure ((h1 _).add_measure (h1 _)) (h1 _), integral_add_measure (h1 _) (h1 _)]
  simp [integral_dirac, smul_add, add_assoc]

/-- Assumption 1 [main_assm] can be met with moment constants `C p = 2`. -/
theorem entryLaws_nonempty : Nonempty (EntryLaws fun _ => (2 : ℝ)) := by
  refine ⟨{ νd := ⟨Basic_rademacher, inferInstance⟩
            νo := ⟨Basic_fourth, inferInstance⟩
            intd := ?_
            into := ?_
            meand := ?_
            vard := ?_
            meano := ?_
            varo := ?_
            pseudo := ?_
            moments := ?_ }⟩
  · intro p
    exact Basic_rademacher_integrable _
  · intro p
    exact Basic_fourth_integrable _
  · simp only [ProbabilityMeasure.coe_mk]
    rw [Basic_rademacher_integral]
    norm_num
  · simp only [ProbabilityMeasure.coe_mk]
    rw [Basic_rademacher_integral]
    norm_num
  · simp only [ProbabilityMeasure.coe_mk]
    rw [Basic_fourth_integral]
    simp
  · simp only [ProbabilityMeasure.coe_mk]
    rw [Basic_fourth_integral]
    simp
    norm_num
  · simp only [ProbabilityMeasure.coe_mk]
    rw [Basic_fourth_integral]
    simp
  · intro p
    simp only [ProbabilityMeasure.coe_mk]
    rw [Basic_rademacher_integral, Basic_fourth_integral]
    simp
    norm_num

end RBMTransitionEdge

end
